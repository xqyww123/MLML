#!/bin/env python3
from sqlitedict import SqliteDict
import csv
import json
with open("minilang.jsonl", "w") as f:
    with open("minilang-no-SH.jsonl", "w") as f2:
        # csv_writer = csv.writer(f)
        # csv_writer.writerow(["file", "pos", "translation"])
        # csv_writer2 = csv.writer(f2)
        # csv_writer2.writerow(["file", "pos", "translation"])
        with SqliteDict("./cache/translation/results.db") as db:
            for key, value in db.items():
                (file, pos, cat) = key.split(":")
                (src, err, pos_prf) = value
                if cat == "refined" and not err:
                    f.write(json.dumps({"file": file, "decl_line": pos, "proof_line": pos_prf, "translation": src}))
                    f.write("\n")
                    # csv_writer.writerow([file, pos, src])
                if cat == "raw" and not err:
                    f2.write(json.dumps({"file": file, "decl_line": pos, "proof_line": pos_prf, "translation": src}))
                    f2.write("\n")
                    # csv_writer2.writerow([file, pos, src])
