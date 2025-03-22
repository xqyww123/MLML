#! /usr/bin/env python3
from sqlitedict import SqliteDict

def tasks_of_job(job_id):
    return [job_id * 2, job_id * 2 + 1]

sum_finished = 0
sum_total = 0
def task_finished_precentage(task_id):
    with open(f"./translation/tasks/targets.{task_id}", 'r') as f:
        targets = [target.strip() for target in f.readlines()]
    num = 0
    with SqliteDict(f"./translation/results/minilang.{task_id}.db") as db:
        for target in targets:
            if target in db:
                num += 1
    global sum_finished
    global sum_total
    sum_finished += num
    sum_total += len(targets)
    return num / len(targets)


def print_progress():
    for i in range(48):
        print(f"Task {i} status: {task_finished_precentage(i) * 100}%")

print_progress()
print(f"Total finished: {sum_finished}, Total total: {sum_total}, Percentage: {sum_finished / sum_total * 100}%")