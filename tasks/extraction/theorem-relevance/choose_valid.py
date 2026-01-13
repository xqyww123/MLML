#! /usr/bin/env python3
import sqlite3
import threading
import random
# import argparse
from data.isabelle import PISA_Data
from sqlitedict import SqliteDict
import json

# parser = argparse.ArgumentParser(description='Deduplicate premise relevance data')
# parser.add_argument('db_path', default='./data/premise_relevance.db',
#                     help='Path to the premise relevance database')
# args = parser.parse_args()

DB_PATH = './data/premise_relevance.db'
VALIDATE_DB_PATH = './tasks/extraction/theorem-relevance/premise_relevance.validate.db'
VALIDATE_IDX = './tasks/extraction/theorem-relevance/premise_relevance.validate.keys'

db_conn = sqlite3.connect(DB_PATH)
db_cursor = db_conn.cursor()
db_cursor.execute('SELECT COUNT(*) FROM "unnamed"')
TOTAL = db_cursor.fetchone()[0]

data_provider = PISA_Data()
PISA = set(data_provider.goal_pos_of(i).to_s(with_column=False) for i in data_provider.all_cases())
PISA_KEYS = set()

db_cursor.execute('SELECT key FROM "unnamed"')
KEYS = set()
for i, row in enumerate(db_cursor):
    if i % 1000 == 0:
        print(f"Processed {i} keys {TOTAL}")
    parts = row[0].split(':')
    key = f"{parts[0]}:{parts[1]}"
    if key in PISA:
        PISA_KEYS.add(key)
        continue
    KEYS.add(row[0])
db_cursor.close()

print(f"Total keys: {len(KEYS)}")

def encode_goal(goal):
    premises, concl = goal
    return '|||'.join([premise for premise in premises] + [concl])

KEY_list = list(KEYS)
CHOSEN_KEYS = {}
CHOSING_LOCKER = threading.Lock()
CHOSEN_NUM = 50000
MEET_GOALS = set()
PAIRS = 0
with SqliteDict(DB_PATH) as db:
    for key in PISA_KEYS:
        for goal, _ in db[key]:
            MEET_GOALS.add(encode_goal(goal))
    while len(CHOSEN_KEYS) < CHOSEN_NUM:
        key = random.choice(KEY_list)
        if key in CHOSEN_KEYS:
            continue
        value = db[key]
        if len(value) != 1:
            continue
        goal, (ctxt, prems, goal_acs) = value[0]
        #if len(prems) <= 2:
        #    continue
        if encode_goal(goal) in MEET_GOALS:
            continue
        MEET_GOALS.add(encode_goal(goal))
        CHOSEN_KEYS[key] = value[0]
        PAIRS += len(prems)
        #print(f"Chosen one, with {len(prems)} premises and {len(goal_acs)} AC equivs")

with SqliteDict(VALIDATE_DB_PATH) as db:
    for key, value in CHOSEN_KEYS.items():
        db[key] = [value]

with open(VALIDATE_IDX, 'w') as f:
    for key in CHOSEN_KEYS.keys():
        f.write(key)
        f.write("\n")

print(f"Chosen {len(CHOSEN_KEYS)} keys, {PAIRS} pairs, written to {VALIDATE_DB_PATH} and {VALIDATE_IDX}")
