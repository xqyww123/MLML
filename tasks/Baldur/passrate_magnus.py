#!/usr/bin/env python3
import sys
from sqlitedict import SqliteDict
from evaluation.evaluator import Status, Result

def success_rate(result_db_path):
    with SqliteDict(result_db_path) as db:
        case_num = 0
        pass_num = 0
        for key, result in db.items():
            time = 0
            if result.status != Status.CASE_NOT_AVAILABLE:
                case_num += 1
            if result.status != Status.SUCCESS:
                continue
            for t in result.elapsed_time:
                time += t
            if time > 500:
                print(time)
                continue
            pass_num += 1
        pass_rate = float(pass_num) / case_num
        print(pass_rate)
        return pass_rate


if len(sys.argv) <= 1:
    print("Usage: python passrate_magnus.py <file>")
    sys.exit(1)

file = sys.argv[1]
success_rate(file)
