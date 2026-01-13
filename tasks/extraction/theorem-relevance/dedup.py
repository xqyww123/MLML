#! /usr/bin/env python3
from sqlitedict import SqliteDict, decode
import sqlite3
from data.isabelle import PISA_Data
import json
import msgpack
import argparse
import os

parser = argparse.ArgumentParser(description='Deduplicate premise relevance data')
parser.add_argument('db_path',
                    help='Path to the premise relevance database')
parser.add_argument('--output', '-o', required=True,
                    help='Path to store the deduplicated result database')
parser.add_argument('--chunks', '-n', type=int, default=1000,
                    help='Number of chunks to split the data into (default: 1000)')
parser.add_argument('--exclude', '-x', type=str, action='append', default=None,
                    help='Path to the file containing the keys to exclude (can be specified multiple times)')
parser.add_argument('--include', '-I', type=str, action='append', default=None,
                    help='Path to the file containing the keys to include (can be specified multiple times). White list')
parser.add_argument('--thm-db-path', type=str,
                    default='/home/qiyuan/Current/MLML/data/premise_info.db',
                    help='Path to premise_info.db (default: /home/qiyuan/Current/MLML/data/premise_info.db)')
args = parser.parse_args()

data_provider = PISA_Data()
PISA_files = set(data_provider.goal_pos_of(i).to_s(with_column=False) for i in data_provider.all_cases())

KEYS_TO_EXCLUDE = set()
KEYS_TO_INCLUDE = None
if args.exclude:
    for exclude_path in args.exclude:
        with open(exclude_path, 'r') as f:
            for line in f:
                KEYS_TO_EXCLUDE.add(line.strip())
if args.include:
    KEYS_TO_INCLUDE = set()
    for include_path in args.include:
        with open(include_path, 'r') as f:
            for line in f:
                KEYS_TO_INCLUDE.add(line.strip())
GOALS_TO_EXCLUDE = set()
with SqliteDict(args.db_path) as db:
    for key in KEYS_TO_EXCLUDE:
        for goal, _ in db[key]:
            goal_str = msgpack.packb(goal)
            GOALS_TO_EXCLUDE.add(goal_str)
print(f"Excluded {len(GOALS_TO_EXCLUDE)} goals and {len(KEYS_TO_EXCLUDE)} keys")
if KEYS_TO_INCLUDE is not None:
    print(f"Included {len(KEYS_TO_INCLUDE)} keys")

db_conn = sqlite3.connect(args.db_path)
db_cursor = db_conn.cursor()
db_cursor.execute('SELECT COUNT(*) FROM "unnamed"')
TOTAL = db_cursor.fetchone()[0]

db_cursor.execute('SELECT key, value FROM "unnamed"')
DATA = {}
DUP_NUM = 0
MISSING_NUM = 0
with SqliteDict(args.thm_db_path) as thm_db:
    for i, row in enumerate(db_cursor):
        if i % 1000 == 0:
            print(f"Processed {i} keys {TOTAL}")
        key_str, value_bytes = row
        pos = key_str
        parts = pos.split(':')
        file = parts[0]
        number = parts[1]
        entries = decode(value_bytes)
        if f"{file}:{number}" in PISA_files or key_str in KEYS_TO_EXCLUDE:
            for goal, _ in entries:
                goal_str = msgpack.packb(goal)
                GOALS_TO_EXCLUDE.add(goal_str)
            continue
        for entry in entries:
            goal, (ctxt, prems, goal_acs) = entry
            goal_str = msgpack.packb(goal)
            if goal_str in GOALS_TO_EXCLUDE:
                continue
            if KEYS_TO_INCLUDE is not None and key_str not in KEYS_TO_INCLUDE:
                continue
            try:
                store = DATA[goal_str]
            except KeyError:
                store = (goal, ctxt, set(), goal_acs)
                DATA[goal_str] = store
            prem_set = store[2]
            for prem in prems:
                if prem not in thm_db:
                    MISSING_NUM += 1
                    print(f"Missing {MISSING_NUM}/{DUP_NUM}. Premise {prem} not in thm_db")
                prem_set.add(prem)
            #prem_set.update(prems)
            DUP_NUM += len(prems)

NUM = sum(len(prem_set) for (_, _, prem_set, _) in DATA.values())
print(f"Exported number: {NUM}, the duplicated number: {DUP_NUM}")

# # Filter out premises that don't exist in thm_db
# print(f"Filtering out premises that don't exist in thm_db: {args.thm_db_path}")
# thm_db = SqliteDict(args.thm_db_path)
# filtered_count = 0
# total_prems_before = 0
# total_prems_after = 0
# 
# for goal_str, (goal, ctxt, prem_set, goal_acs) in DATA.items():
#     total_prems_before += len(prem_set)
#     # Filter premises that exist in thm_db
#     valid_prems = {prem for prem in prem_set if prem in thm_db}
#     filtered_count += len(prem_set) - len(valid_prems)
#     # Update the prem_set in place
#     DATA[goal_str] = (goal, ctxt, valid_prems, goal_acs)
#     total_prems_after += len(valid_prems)
# 
# thm_db.close()
# 
# print(f"Filtered out {filtered_count} premises that don't exist in thm_db")
# print(f"Premises before filtering: {total_prems_before}")
# print(f"Premises after filtering: {total_prems_after}")

# Split DATA into N chunks and write to files
data_items = list(DATA.items())
del DATA
total_items = len(data_items)
chunk_size = (total_items + args.chunks - 1) // args.chunks  # Ceiling division

os.makedirs(args.output, exist_ok=True)

for chunk_idx in range(args.chunks):
    start_idx = chunk_idx * chunk_size
    end_idx = min(start_idx + chunk_size, total_items)
    
    if start_idx >= total_items:
        break
    
    chunk_data = []
    for goal_str, (goal, ctxt, prem_set, goal_acs) in data_items[start_idx:end_idx]:
        # Convert set to list for msgpack serialization
        prem_list = list(prem_set)
        chunk_data.append((goal_str, (goal, ctxt, prem_list, goal_acs)))
    
    chunk_path = os.path.join(args.output, f'chunk.{chunk_idx}')
    chunk_len = len(chunk_data)  # Save length before deleting
    packed_data = msgpack.packb(chunk_data)
    del chunk_data  # Free memory immediately after packing
    with open(chunk_path, 'wb') as f:
        f.write(packed_data)  # type: ignore
    del packed_data  # Free memory after writing
    
    print(f"Written chunk {chunk_idx} with {chunk_len} items to {chunk_path}")

# Free memory explicitly
del data_items
db_cursor.close()
db_conn.close()
print("All chunks written. Memory freed.")