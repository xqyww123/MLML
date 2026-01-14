from sqlitedict import SqliteDict
import pyarrow as pa
import pyarrow.parquet as pq
import json


DATA = {}
NUM = 0

with SqliteDict('./data/translation/results.db') as db:
    for key, value in db.items():
        (file, line, cat) = key.split(':')
        (src, err, pos_prf, spec_offset) = value
        dbk = f"{file}:{line}"
        if err:
            continue
        NUM += 1
        if NUM % 1000 == 0:
            print(f"Processed {NUM} cases")
        if cat == 'refined' and not err:
            if dbk not in DATA:
                DATA[dbk] = {}
            DATA[dbk]["minilang"] = src
            DATA[dbk]["proof_position"] = pos_prf
        if cat == 'origin' and not err:
            if dbk not in DATA:
                DATA[dbk] = {}
            DATA[dbk]["isar"] = src
            DATA[dbk]["proof_position"] = pos_prf

DATA2 = []
for dbk, data in DATA.items():
    DATA2.append({
        "spec_position": dbk,
        "minilang": data["minilang"] if "minilang" in data else None,
        "proof_position": data["proof_position"] if "proof_position" in data else None,
        "isar": data["isar"] if "isar" in data else None
    })

with open("dataset.jsonl", "w") as f:
    for data in DATA2:
        f.write(json.dumps(data) + "\n")
table = pa.Table.from_pylist(DATA2)   # 自动推断 schema
pq.write_table(table, "dataset.parquet", compression="snappy")

exit(0)
