#! /usr/bin/env python3

import sys
import json
from Isabelle_RPC_Host.unicode import pretty_unicode

# NUM = 0
# PRED = 0
# with SqliteDict('./data/basic_info.db') as db:
#     for i, (k, (_, all_info)) in enumerate(db.items()):
#         if i % 1000 == 0:
#             print(f"Processed {i} keys")
#         for cmd_info in all_info:
#             statement = cmd_info.command
#             if statement.startswith('private '):
#                 statement = statement[len('private '):]
#             if statement.startswith('qualified '):
#                 statement = statement[len('qualified '):]
#             if statement.startswith('datatype '):
#                 NUM += 1
#                 if "pred:" in statement or "map:" in statement or "rel:" in statement:
#                     PRED += 1
#                     print(f"NUM: {NUM}, PRED: {PRED}, {k}, {statement}")

LINENUM = 0
NUM = 0
def process(text):
    global NUM
    lines = text.split('\n')
    for line in lines:
        if line.startswith("""datatype (?'a::type, ?'b::type) test = is_Test: Test \<open>nat\<close> \<open>?'b::type\<close> | is_Test2: Test2 \<open>tB1: ?'a::type"""):
            NUM += 1
            print(f"NUM: {NUM}, {line}")


for line in sys.stdin:
    LINENUM += 1
    if LINENUM % 100000 == 0:
        print(f"Processed {LINENUM} lines")
    line = line.strip()
    if not line:
        continue
    try:
        (goal, prem) = json.loads(line)
        # goal = Client.pretty_unicode(goal)
        # prem = Client.pretty_unicode(prem)
        process(goal)
        process(prem)
    except json.JSONDecodeError as e:
        print(f"JSONDecodeError: {e}", file=sys.stderr)
