import logging
import csv

logger = logging.getLogger(__name__)
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)

SERVERS = {}
SERVER_INSTANCES = []
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
                
                # Add the server to the list multiple times based on instance count
                SERVER_INSTANCES.extend([server] * instances)
                SERVERS[server] = instances
            else:
                # Handle the case where only the server is specified (assume 1 instance)
                server = row[0].strip()
                if server:
                    SERVER_INSTANCES.append(server)
                    SERVERS[server] = 1
                    
        logger.info(f"Loaded {len(SERVERS)} servers with {len(SERVER_INSTANCES)} instances from CSV")
except FileNotFoundError:
    logger.warning("No server configuration found. Using default server.")
    SERVERS["127.0.0.1:6666"] = 1
    SERVER_INSTANCES.append("127.0.0.1:6666")
