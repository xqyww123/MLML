#!/bin/bash

host=$1
shift  # Remove the host argument, leaving only the port/numproc pairs

# Ensure we have an even number of arguments (port/numproc pairs)
if [ $(($# % 2)) -ne 0 ]; then
  echo "Error: Invalid arguments format. Expected: host port1 numproc1 port2 numproc2 ..."
  exit 1
fi

# Create necessary directories
source ./envir.sh
set -e

# Process each port/numproc pair
while [ $# -gt 0 ]; do
  port=$1
  numprocs=$2
  shift 2  # Move to the next pair
  
  #echo "Setting up server instance on port $port with $numprocs processes"
  
  # Create directory for this instance
  mkdir -p ./cache/repl_tmps/${host}_${port}
  
  # Kill any process using this port
  fuser -n tcp -k $port || true
  
  # Make cache directory path absolute
  dir="$(realpath ./cache/repl_tmps/${host}_${port})"
  
  # Start the server instance
  MASH_STATE_PATH=$dir/mash_state ./contrib/Isa-REPL/repl_server.sh 0.0.0.0:$port AFP-1-PISA $dir -o threads=$numprocs > $dir/log.txt 2>&1 &
  
  #echo "Started server on port $port"
done

# Wait for any child process to exit
wait -n