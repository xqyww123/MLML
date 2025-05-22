#!/usr/bin/env python3

import os
import sys
import time
import subprocess
import threading

def allocated_servers():
    cmd = f"squeue -u haonan.li"
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    return result.stdout.strip()

def check_node(node):
    # Get list of running jobs for the user
    return node in allocated_servers()


def alloc_server(node):
    cmd = f"srun --job-name=minilang --partition=standard --nodes=1 --nodelist={node} --ntasks-per-node=1 --cpus-per-task=128 --time=120:00:00 sleep 10000000000"
    subprocess.Popen(cmd, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def restart_job(node):
    running_jobs = allocated_servers().split('\n')
    for job in running_jobs:
        if node in job:
            job_id = job.split()[0]
            cmd = f"scancel {job_id}"
            os.system(cmd)
    time.sleep(10)
    # alloc_server(node)
    # time.sleep(10)

def alloc_server(node):
    while True:
        if not check_node(node):
            cmd = f"srun --job-name=minilang --partition=standard --nodes=1 --nodelist={node} --ntasks-per-node=1 --cpus-per-task=128 --time=120:00:00 sleep 10000000000"
            subprocess.Popen(cmd, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        time.sleep(10)


def alloc_servers(node_list):
    for node in node_list:
        #alloc_server(node)
        thread = threading.Thread(target=alloc_server, args=(node,))
        thread.start()


def free_servers():
    getjobs_cmd = 'squeue --format="%.18i %.9P %.30j %.8u %.8T %.10M %.9l %.6D %R" --me | grep "minilang" > tmp.txt'
    os.system(getjobs_cmd)

    with open('tmp.txt','r') as f:
        for line in f.readlines():
            pid = line.strip().split()[0]
            cancel_cmd = 'scancel ' + pid
            os.system(cancel_cmd)

    os.system('rm tmp.txt')




# new interfaces

def run_servers (nodes):
    for node, numprocss in nodes.items():
        thread = threading.Thread(target=run_server, args=(node, numprocss))
        thread.start()

def run_server(node, numprocss):
    while True:
        if not check_node(node):
            args = ""
            for port, numprocs in numprocss:
                args += f"{port} {numprocs} "
            cmd = f"srun --job-name=minilang --partition=standard --nodes=1 --nodelist={node} --ntasks-per-node=1 --cpus-per-task=128 --time=120:00:00 ./tools/slurm_run_server.sh {node} {args}"
            subprocess.Popen(cmd, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        time.sleep(10)
