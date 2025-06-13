#!/usr/bin/env python3
import json
import csv
from sqlitedict import SqliteDict
from evaluation.evaluator import Result, Status
import sys

def report_evaluation(response_path : str, result_path : str, pass_num : int, print_time : bool):
    responses = {}
    with open(response_path, "r", encoding="utf-8") as f:
        for line in f:
            data = json.loads(line)
            responses[str(data["index"])] = data["response"]
    with open(result_path + '.csv', "w", encoding="utf-8") as f:
        csv_writer = csv.writer(f)
        if print_time:
            csv_writer.writerow(["index", "attempt", "status", 'time (seconds)', "error", "response"])
        else:
            csv_writer.writerow(["index", "attempt", "status", "error", "response"])
        with SqliteDict(result_path) as db:
            for key, result in sorted(db.items(), key=lambda x: int(x[0])):
                try:
                    errs = [str(e) for e in result.errors]
                except AttributeError:
                    errs = [result.error]
                if result.status == Status.CASE_NOT_AVAILABLE:
                    err = "\n\n".join(errs)
                    if print_time:
                        csv_writer.writerow([key, "", Status.CASE_NOT_AVAILABLE, "", err, ""])   
                    else:
                        csv_writer.writerow([key, "", Status.CASE_NOT_AVAILABLE, err, ""])   
                    continue
                num = len(errs)
                ress = responses[key]
                if not isinstance(ress, list):
                    ress = [ress]
                try:
                    times = result.elapsed_time
                except AttributeError:
                    times = []
                if not isinstance(times, list):
                    times = [times]
                for i, err in enumerate(errs):
                    if print_time:
                        csv_writer.writerow([key, i, Status.FAIL, times[i], err, ress[i]])
                    else:
                        csv_writer.writerow([key, i, Status.FAIL, err, ress[i]])
                if num < pass_num:
                    if print_time:
                        csv_writer.writerow([key, num, Status.SUCCESS, times[num], "", ress[num]])
                    else:
                        csv_writer.writerow([key, num, Status.SUCCESS, "", ress[num]])

if __name__ == "__main__":
    if len(sys.argv) < 5:
        print("Usage: python tasks/Baldur/report.py <response_path> <result_path> <pass> <print_time>")
        sys.exit(1)
    
    response_path = sys.argv[1]
    result_path = sys.argv[2]
    pass_num = int(sys.argv[3])
    print_time = (sys.argv[4] == 'yes')
    report_evaluation(response_path, result_path, pass_num, print_time)
