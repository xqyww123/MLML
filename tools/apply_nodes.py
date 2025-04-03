#!/usr/bin/env python3

import os
import sys
import time
import subprocess
import threading

N = 24
node_list = [f"cn-{i:02d}" for i in range(1,N+1) if i not in [1, 3]]


def check_node(node):
    # Get list of running jobs for the user
    cmd = f"squeue -u haonan.li"
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    if node in result.stdout.strip():
        return True
    return False


def alloc_servers(node):
    while True:
        if not check_node(node):
            cmd = f"srun --job-name=minilang --partition=standard --nodes=1 --nodelist={node} --ntasks-per-node=1 --cpus-per-task=128 --time=120:00:00 sleep 10000000000"
            subprocess.Popen(cmd, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        time.sleep(1)


# Create and start threads for each node
threads = []
for node in node_list:
    thread = threading.Thread(target=alloc_servers, args=(node,))
    thread.start()
    threads.append(thread)

# Wait for all threads to complete (which won't happen in this case due to infinite loops)
for thread in threads:
    thread.join()
