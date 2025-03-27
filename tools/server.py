import logging
import csv
import os
import subprocess
from IsaREPL import Client, REPLFail
import time
import concurrent.futures
import threading

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
        for row in csv_reader:
            # Skip empty rows or comment rows
            if not row or row[0].startswith('#'):
                continue
                
            # Check if the row has at least two columns (server, instances)
            if len(row) >= 2:
                server = row[0].strip()
                try:
                    # Parse the number of instances, default to 1 if invalid
                    instances = int(row[1].strip())
                    if instances <= 0:
                        logger.warning(f"Invalid instance count {instances} for server {server}, defaulting to 1")
                        instances = 1
                except ValueError:
                    logger.warning(f"Invalid instance count format for server {server}, defaulting to 1")
                    instances = 1

                try:
                    # Parse the number of instances, default to 1 if invalid
                    numprocs = int(row[2].strip())
                    if numprocs <= 0:
                        logger.warning(f"Invalid numprocs {numprocs} for server {server}, defaulting to 1")
                        numprocs = 1
                except ValueError:
                    logger.warning(f"Invalid numprocs format for server {server}, defaulting to 1")
                    numprocs = 1
                
                
                CFG_SERVERS[server] = (instances, numprocs)
            else:
                # Handle the case where only the server is specified (assume 1 instance)
                server = row[0].strip()
                if server:
                    CFG_SERVERS[server] = (1, 1)
                    
        logger.info(f"Loaded {len(CFG_SERVERS)} servers from ./config/evaluation_servers.csv")
except FileNotFoundError:
    logger.warning("No server configuration found. Using default server.")
    CFG_SERVERS["127.0.0.1:6666"] = (1, 8)


def test_server(addr):
    try:
        with Client(addr, 'HOL', timeout=10) as client:
            client.num_processor()
            return True
    except KeyboardInterrupt as E:
        raise E
    except InterruptedError as E:
        raise E
    except Exception:
        return False

def launch_server(server, retry=20):
    if test_server(server):
        logger.info(f"Server on {server} is already running")
        return (True, server, "Already running")
    else:
        pwd = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        host, port = server.split(':')
        try:
            # Construct the SSH command to launch the REPL server
            # ./contrib/Isa-REPL/repl_server_watch_dog.sh 0.0.0.0:6666 HOL /tmp/repl_outputs -o threads=32
            numprocs = CFG_SERVERS[server][1]
            ssh_command = f"ssh {host} 'cd {pwd} && " + \
                f"mkdir -p ./cache/repl_tmps/{port} && " + \
                f"source ./envir.sh && " + \
                f"(fuser -n tcp -k {port} || true) && " + \
                f"nohup ./contrib/Isa-REPL/repl_server.sh 0.0.0.0:{port} HOL {pwd}/cache/repl_tmps/{port} -o threads={numprocs} > ./cache/repl_tmps/{port}/log.txt 2>&1 &'"
            
            # Log the command being executed
            logger.info(f"Launching server on {host}:{port} with command: {ssh_command}")
            
            # Execute the SSH command in a subprocess
            subprocess.Popen(ssh_command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            logger.info(f"Command sent to {host}:{port}")

            # Wait for the server to start (try up to 60 times)
            for attempt in range(30):
                if test_server(server):
                    logger.info(f"Server on {host}:{port} started after {attempt+1} attempts")
                    return (True, server, f"Started successfully after {attempt+1} attempts")
                logger.debug(f"Waiting for server {host}:{port} to start (attempt {attempt+1}/60)")
                time.sleep(10)
            
            logger.warning(f"Server on {host}:{port} failed to start after 30 attempts")
            if retry > 0:
                return launch_server(server, retry - 1)
            else:
                return (False, server, "Failed to start after 60 attempts")
        except Exception as e:
            error_msg = str(e)
            logger.error(f"Failed to launch server on {host}:{port}: {error_msg}, retrying...")
            return (False, server, f"Error: {error_msg}")
    # Add the server to the SERVERS dictionary
    return (True, server, "Already running")

SERVERS = {}
SERVER_INSTANCES = []

def launch_servers():
    """Launch all REPL servers in parallel using ThreadPoolExecutor."""
    # Get the list of servers to launch
    servers_to_launch = list(CFG_SERVERS.keys())
    
    if not servers_to_launch:
        logger.warning("No servers to launch")
        return
        
    logger.info(f"Launching {len(servers_to_launch)} servers")
    
    # Use a ThreadPoolExecutor to launch servers in parallel
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(servers_to_launch)) as executor:
        # Submit all tasks and map them to their servers for tracking
        future_to_server = {executor.submit(launch_server, server): server for server in servers_to_launch}
        
        # Process results as they complete
        success_count = 0
        for future in concurrent.futures.as_completed(future_to_server):
            server = future_to_server[future]
            try:
                success, server, message = future.result()
                if success:
                    SERVERS[server] = CFG_SERVERS[server]
                    SERVER_INSTANCES.extend([server] * CFG_SERVERS[server][0])
                    success_count += 1
            except Exception as e:
                logger.error(f"Server {server} launch raised an exception: {str(e)}")
    
    # Final report
    logger.info(f"Server launch complete: {success_count}/{len(servers_to_launch)} servers running")

launch_servers()

class ServerSupervisor:
    """Class to monitor and maintain server health"""
    
    def __init__(self, check_interval=10):
        """
        Initialize the server supervisor
        
        Args:
            check_interval: Time in seconds between health checks (default: 60)
        """
        self.check_interval = check_interval
        self.is_running = False
        self.supervisor_thread = None
        self._lock = threading.Lock()  # Lock for thread-safe operations
    
    def start(self):
        """Start the server supervision in a background thread"""
        with self._lock:
            if self.is_running:
                logger.info("Server supervisor is already running")
                return
                
            self.is_running = True
            self.supervisor_thread = threading.Thread(target=self._supervision_loop, daemon=True)
            self.supervisor_thread.start()
            logger.info(f"Server supervisor started, checking every {self.check_interval} seconds")
    
    def stop(self):
        """Stop the server supervision"""
        with self._lock:
            if not self.is_running:
                return
                
            self.is_running = False
            if self.supervisor_thread:
                self.supervisor_thread.join(timeout=30)
                logger.info("Server supervisor stopped")
    
    def _supervision_loop(self):
        """Main supervision loop that checks server health periodically"""
        while self.is_running:
            self._check_and_restart_servers()
            # Sleep for the specified interval
            time.sleep(self.check_interval)
    
    def _check_and_restart_servers(self):
        """Check health of all servers and restart any that are down"""
        logger.debug("Running server health check...")
        
        server_status = []
        servers_to_restart = []
        
        # Check status of all servers
        for server in list(SERVERS.keys()):
            is_running = test_server(server)
            server_status.append(f"{server}: {'UP' if is_running else 'DOWN'}")
            if not is_running:
                servers_to_restart.append(server)
        
        # Log status summary
        logger.debug(f"Server health status: {', '.join(server_status)}")
        
        # Restart any servers that are down
        if servers_to_restart:
            logger.warning(f"Detected {len(servers_to_restart)} servers down: {', '.join(servers_to_restart)}")
            for server in servers_to_restart:
                logger.info(f"Attempting to restart server {server}")
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


# Initialize and start the server supervisor
supervisor = ServerSupervisor(check_interval=10)  # Check every 10 seconds
supervisor.start()

# Register an atexit handler to stop the supervisor gracefully when the program exits
import atexit
atexit.register(supervisor.stop)

if __name__ == "__main__":
    time.sleep(1000000)

