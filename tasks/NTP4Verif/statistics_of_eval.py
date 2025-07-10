#!/usr/bin/env python3

USAGE = """
statistics_of_eval.py <MLML-evaluation-result-db> <base.csv>

<MLML-evaluation-result-db> is the database of MLML evaluation results.
<base.csv> is the base line file, e.g., ./data/why3/no-lemma5/Auto_level_3.csv
"""

import sys

if len(sys.argv) != 3:
    print(USAGE)
    sys.exit(1)

mlml_eval_db = sys.argv[1]
base_csv = sys.argv[2]

from sqlitedict import SqliteDict
from evaluation.evaluator import Result, Status
import os
import csv

eval_success = 0
eval_total = 0
base_success = 0
base_total = 0

BASE = {}
with open(base_csv, "r") as f:
    reader = csv.reader(f)
    for row in reader:
        BASE[(row[0], row[1])] = (row[2] == 'True')

with SqliteDict(mlml_eval_db) as db:
    for (key, result) in db.items():
        file, line = key.split(":")
        goal_name = os.path.splitext(os.path.basename(file))[0]
        directory = os.path.splitext(os.path.dirname(os.path.dirname(file)))[0]
        # Get the subpath under data/why3/*
        directory = directory.split("data/why3/")[-1]  # Split on data/why3/ and take last part
        mlw_path = directory.split("/")[-1]  # Take the last directory component
        print((mlw_path, goal_name))
        if result.status == Status.CASE_NOT_AVAILABLE:
            continue
        if (mlw_path, goal_name) not in BASE:
            goal_name += 'qtvc'
        if (mlw_path, goal_name) not in BASE:
            print(f"{(mlw_path, goal_name)} not in BASE")
            continue
        if result.status == Status.SUCCESS:
            eval_success += 1
        eval_total += 1
        if BASE[(mlw_path, goal_name)]:
            base_success += 1
        base_total += 1

print(f"Base success: {base_success}/{base_total}")
print(f"Eval success: {eval_success}/{eval_total}")


