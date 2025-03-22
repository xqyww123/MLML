#!/bin/env python3
import os
import time
import subprocess
from sqlitedict import SqliteDict

def tasks_of_job(job_id):
    return [job_id * 2, job_id * 2 + 1]

def task_finished(task_id):
    with open(f"./translation/tasks/targets.{task_id}", 'r') as f:
        targets = [target.strip() for target in f.readlines()]
    with SqliteDict(f"./translation/results/minilang.{task_id}.db") as db:
        for target in targets:
            if target not in db:
                return False
    return True

def job_finished(job_id):
    for task_id in tasks_of_job(job_id):
        if not task_finished(task_id):
            return False
    return True

def get_running_jobs(user):
    # Get list of running jobs for the user
    cmd = f"squeue -u {user}"
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    return result.stdout.strip().split('\n')

def submit_job(idx, total):
    cmd = f"sbatch translation/translate.sh {idx} {total}"
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    # Extract job ID from sbatch output (typically looks like "Submitted batch job 123456")
    if result.stdout:
        return result.stdout.strip().split()[-1]
    return None

os.system("./init.sh")

# Get current username
username = os.getenv('USER')

N = 24
job_status = {}  # Dictionary to track job IDs and their status

# Initial submission of all jobs
for i in range(N):
    job_id = submit_job(i, N)
    if job_id:
        job_status[str(i)] = job_id
        print(f"Submitted job {i} with ID {job_id}")

# Monitor jobs
while job_status:
    running_jobs = get_running_jobs(username)
    
    # Check each job
    for idx, job_id in list(job_status.items()):
        # If job not found in running jobs, check if it's finished
        if not any(job_id in job for job in running_jobs):
            if job_finished(int(idx)):
                print(f"Job {idx} completed successfully")
                del job_status[idx]
            else:
                print(f"Job {idx} (ID: {job_id}) not found and not finished. Resubmitting...")
                new_job_id = submit_job(int(idx), N)
                if new_job_id:
                    job_status[idx] = new_job_id
                    print(f"Resubmitted job {idx} with new ID {new_job_id}")
            
    # Wait before next check
    time.sleep(60)  # Check every minute

print("All jobs completed successfully!")
