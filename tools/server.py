import logging
import csv
import os
import subprocess
import atexit
from IsaREPL import Client, REPLFail
import time
import concurrent.futures
import threading
from . import slurm

logger = logging.getLogger(__name__)
# Read the logging level from an environment variable, default to INFO if not set.
log_level = os.getenv("LOG_LEVEL", "INFO").upper()

# Configure logging using the specified log level.
logging.basicConfig(
    level=log_level,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)

CFG_SERVERS = {}
try:
    with open('./config/evaluation_servers.csv', 'r') as f:
        csv_reader = csv.reader(f)
        # Read the first row as headers
        headers = next(csv_reader, None)
        for row in csv_reader:
            # Skip empty rows or comment rows
            if not row or row[0].startswith('#'):
                continue

            # Create a dictionary that maps from headers to data for the current row
            row_data = {}
            for i, header in enumerate(headers):
                if i < len(row):
                    data = row[i].strip()
                    if i >= 1:
                        data = int(data)
                    row_data[header.strip()] = data
                else:
                    # If the row doesn't have a value for this header, set it to empty string
                    row_data[header.strip()] = ""

            CFG_SERVERS[row_data["server"]] = row_data

        logger.info(f"Loaded {len(CFG_SERVERS)} servers from ./config/evaluation_servers.csv")
except FileNotFoundError:
    logger.warning("No server configuration found. Using default server.")
    CFG_SERVERS["127.0.0.1:6666"] = {
        "server": "127.0.0.1:6666",
        "numprocs": 8,
        "num-translator": 3,
        "num-evaluator": 4
    }

SERVERS = CFG_SERVERS.copy()

# Read the cluster configuration from environment variable, default to 'local' if not set
CLUSTER = os.getenv("CLUSTER", "ssh")
BASE_SESSION = os.getenv("SESSION", "AFP-1-PISA")

def test_server(addr, timeout_retry=6):
    try:
        Client.test_server(addr, timeout=300)
        return True
    except KeyboardInterrupt as E:
        raise E
    except InterruptedError as E:
        raise E
    except ConnectionRefusedError as E:
        return False
    except TimeoutError as E:
        if timeout_retry > 0:
            logger.error(f"Cannot connect to server {addr}: {E}")
            return test_server(addr, timeout_retry-1)
        else:
            logger.error(f"Cannot connect to server {addr}: {E}")
            return False
    except Exception as E:
        logger.error(f"Cannot connect to server {addr}: {E}")
        return False

def launch_server(server, retry=6, timeout=600):
    if test_server(server):
        logger.info(f"Server on {server} is already running")
        return (True, server, "Already running")
    else:
        pwd = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        host, port = server.split(':')
        if CLUSTER != "slurmx":
            # Construct the SSH command to launch the REPL server
            # ./contrib/Isa-REPL/repl_server_watch_dog.sh 0.0.0.0:6666 HOL /tmp/repl_outputs -o threads=32
            numprocs = SERVERS[server]["numprocs"]
            ssh_command = f"ssh {host} \"bash -lc \'cd {pwd} && " + \
                f"mkdir -p ./cache/repl_tmps/{host}_{port} && " + \
                f"source ./envir.sh && " + \
                f"(fuser -n tcp -k {port} || true) && " + \
                f"MASH_STATE_PATH={pwd}/cache/repl_tmps/{host}_{port}/mash_state nohup ./contrib/Isa-REPL/repl_server.sh 0.0.0.0:{port} {BASE_SESSION} {pwd}/cache/repl_tmps/{host}_{port} -o threads={numprocs} > ./cache/repl_tmps/{host}_{port}/log.txt 2>&1 &\'\""

            # Log the command being executed
            logger.info(f"Launching server on {host}:{port} with command: {ssh_command}")

            # Execute the SSH command in a subprocess
            subprocess.Popen(ssh_command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            logger.info(f"Command sent to {host}:{port}. It typically takes 90 seconds to start.")

        start_time = time.monotonic()  # 返回以秒为单位的浮点数
        end_time = start_time + timeout
        
        while time.monotonic() < end_time:
            if test_server(server):
                elapsed_time = time.monotonic() - start_time
                logger.info(f"Server on {host}:{port} started after {elapsed_time:.1f} seconds")
                return (True, server, f"Started successfully after {elapsed_time:.1f} seconds")
            
            elapsed_time = time.monotonic() - start_time
            
            if elapsed_time <= 90:  # First 90 seconds
                msg = f"Waiting for server {host}:{port} to start ({elapsed_time:.1f}/{timeout:.0f} seconds). Calm down, it typically takes 90 seconds to start."
            else:
                msg = f"Waiting for server {host}:{port} to start ({elapsed_time:.1f}/{timeout:.0f} seconds). Maybe it is not working, check the log file ./cache/repl_tmps/{host}_{port}/log.txt"
            
            logger.info(msg)
            # Use a shorter sleep interval for more responsive checking
            time.sleep(10)

        if retry > 1:
            logger.warning(f"Server on {host}:{port} failed to start after {timeout:.0f} seconds, retrying...")
            if CLUSTER == "slurm" or CLUSTER == "slurmx":
                slurm.restart_job(host)
            return launch_server(server, retry-1, timeout)
        else:
            elapsed_time = time.monotonic() - start_time
            logger.warning(f"Server on {host}:{port} failed to start after {elapsed_time:.1f} seconds")
            return (False, server, f"Failed to start after {elapsed_time:.1f} seconds")


class ServerSupervisor:
    """Class to monitor and maintain server health"""
    _instance = None
    _initialized = False

    def __new__(cls, *args, **kwargs):
        if cls._instance is None:
            cls._instance = super(ServerSupervisor, cls).__new__(cls)
        return cls._instance

    def __init__(self, check_interval=10):
        """
        Initialize the server supervisor

        Args:
            check_interval: Time in seconds between health checks (default: 10)
        """
        if not self._initialized:
            self.check_interval = check_interval
            self.is_running = False
            self.supervision_threads = {}  # Dictionary to track supervision threads for each server
            self._lock = threading.Lock()  # Lock for thread-safe operations
            self._initialized = True

    def start(self):
        """Start the server supervision with a dedicated thread for each server"""
        with self._lock:
            if self.is_running:
                logger.info("Server supervisor is already running")
                return

            self.is_running = True

            # Create and start a thread for each server
            for server in SERVERS.keys():
                self._start_server_supervision(server)

            logger.info(f"Server supervisor started with dedicated threads for {len(SERVERS)} servers, checking every {self.check_interval} seconds")

    def _start_server_supervision(self, server):
        """Start a dedicated supervision thread for the specified server"""
        if server in self.supervision_threads and self.supervision_threads[server].is_alive():
            logger.debug(f"Supervision thread for {server} is already running")
            return

        thread = threading.Thread(
            target=self._server_supervision_loop,
            args=(server,),
            daemon=True,
            name=f"supervisor-{server}"
        )
        self.supervision_threads[server] = thread
        thread.start()
        logger.debug(f"Started supervision thread for server {server}")

    def stop(self):
        """Stop all server supervision threads"""
        with self._lock:
            if not self.is_running:
                return

            self.is_running = False

            # Wait for all supervision threads to terminate
            for server, thread in self.supervision_threads.items():
                if thread.is_alive():
                    thread.join(timeout=10)
                    logger.debug(f"Stopped supervision thread for server {server}")

            self.supervision_threads.clear()
            logger.info("Server supervisor stopped")

    def _server_supervision_loop(self, server):
        """Supervision loop for a specific server that checks its health periodically"""
        logger.debug(f"Starting supervision loop for server {server}")
        while self.is_running:
            self._check_and_restart_server(server)
            # Sleep for the specified interval
            time.sleep(self.check_interval)

    def _check_and_restart_server(self, server):
        """Check health of a specific server and restart it if down"""
        is_running = test_server(server)
        if is_running:
            logger.debug(f"Server {server} is UP")
        else:
            logger.warning(f"Server {server} is DOWN - attempting to restart")
            if CLUSTER == "slurm" or CLUSTER == "slurmx":
                host, _ = server.split(":")
                slurm.restart_job(host)
            self._restart_server(server)

    def _restart_server(self, server):
        """Restart a specific server"""
        try:
            success, _, message = launch_server(server)
            if success:
                logger.info(f"Successfully restarted server {server}: {message}")
            else:
                logger.error(f"Failed to restart server {server}: {message}")
        except Exception as e:
            logger.error(f"Error while restarting server {server}: {str(e)}")


# Add this near the top of the file with other global variables
_launch_servers_called = False

def launch_servers():
    """Launch all REPL servers in parallel using ThreadPoolExecutor."""
    global _launch_servers_called

    if _launch_servers_called:
        logger.warning("launch_servers has already been called. Ignoring subsequent calls.")
        return

    # Get the list of servers to launch
    match CLUSTER:
        case "ssh":
            pass
        case "slurm":
            atexit.register(slurm.free_servers)
            logger.info("Allocating servers for SLURM...")
            server_names = list(set(map(lambda x: x.split(":")[0], SERVERS.keys())))
            print(server_names)
            slurm.alloc_servers(server_names)
            time.sleep(15)
            allocated_servers = slurm.allocated_servers()
            for server in SERVERS.keys():
                if server not in allocated_servers:
                    logger.warning(f"Server {server} not allocated, skipping")
                    # SERVERS.pop(server)
            logger.info(f"{len(SERVERS)}/{len(CFG_SERVERS)} servers are allocated for SLURM")
        case 'slurmx':
            atexit.register(slurm.free_servers)
            logger.info("Running servers for SLURMX...")
            server_names = {}
            for server, info in SERVERS.items():
                host, port = server.split(":")
                if host not in server_names:
                    server_names[host] = []
                server_names[host].append((port, info["numprocs"]))
            print(server_names)
            slurm.run_servers(server_names) # The only difference from slurm is `run_servers` instead of `alloc_servers`
            time.sleep(15)
        case _:
            raise ValueError(f"Invalid cluster configuration: {CLUSTER}")

    servers_to_launch = list(SERVERS.keys())

    if not servers_to_launch:
        logger.warning("No servers to launch")
        return

    logger.info(f"Launching {len(servers_to_launch)} servers")

    # Use a ThreadPoolExecutor to launch servers in parallel
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(servers_to_launch)) as executor:
        # Submit all tasks and map them to their servers for tracking
        future_to_server = {executor.submit(lambda s: launch_server(s, retry=1, timeout=600), server): server for server in servers_to_launch}

        # Process results as they complete
        success_count = 0
        for future in concurrent.futures.as_completed(future_to_server):
            server = future_to_server[future]
            try:
                success, server, message = future.result()
                if success:
                    success_count += 1
            except Exception as e:
                logger.error(f"Server {server} launch raised an exception: {str(e)}")

    # Final report
    logger.info(f"Server launch complete: {success_count}/{len(servers_to_launch)} servers running")
    # Initialize and start the server supervisor
    supervisor = ServerSupervisor(check_interval=10)  # Check every 10 seconds
    supervisor.start()

    _launch_servers_called = True


# Register an atexit handler to stop the supervisor gracefully when the program exits
#import atexit
#atexit.register(supervisor.stop)

def kill_all_servers():
    logger.info("Killing all server processes...")
    # Kill all existing server processes
    killed_servers = []
    for server_addr in SERVERS.keys():
        try:
            # Parse the server address to get host and port
            if ':' in server_addr:
                host, port = server_addr.split(':')

                # Use SSH to run fuser for all hosts
                try:
                    cmd = f"ssh {host} 'fuser -k {port}/tcp'"
                    result = subprocess.run(
                        cmd,
                        shell=True,
                        check=False,
                        stderr=subprocess.PIPE,
                        stdout=subprocess.PIPE
                    )
                    if result.returncode == 0:
                        logger.info(f"Killed server process on {host}:{port}")
                        killed_servers.append(server_addr)
                    else:
                        message = result.stderr.decode()
                        if message.strip() == "":
                            logger.warning(f"{host}:{port} not running")
                        else:
                            logger.warning(f"{host}:{port} failed to kill: {message}")
                except Exception as e:
                    logger.error(f"SSH command failed for {host}:{port}: {str(e)}")
            else:
                logger.error(f"Invalid server address format: {server_addr}")
        except Exception as e:
            logger.error(f"Error killing server {server_addr}: {str(e)}")

    if not killed_servers:
        logger.warning("No servers were killed")
        return 0, 0

    killed_count = len(killed_servers)
    logger.info(f"Killed {killed_count} server processes.")

    return killed_servers
