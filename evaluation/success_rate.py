#!/bin/env python3

import sys
from sqlitedict import SqliteDict
from evaluation.evaluator import Status, Result

def success_rate(result_db_path):
    with SqliteDict(result_db_path) as db:
        max_pass = 1
        case_num = 0
        for key, result in db.items():
            max_pass = max(max_pass, len(result.errors))
            if result.status == Status.SUCCESS or result.status == Status.FAIL:
                case_num += 1
        pass_count = [0] * (max_pass + 1)
        sum = 0
        for key, result in db.items():
            sum += len(result.errors)
            if result.status != Status.SUCCESS:
                continue
            pas = len(result.errors)
            for i in range(pas, max_pass):
                pass_count[i] += 1
        pass_rate = [pass_count[i] / case_num for i in range(max_pass)]
        print(sum)
        return pass_rate

if __name__ == "__main__":
    if len(sys.argv) <= 1:
        print("Usage: python evaluation/success_rate.py <result_db_path>")
    pass_rate = success_rate(sys.argv[1])
    print(pass_rate)

