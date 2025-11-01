#!/bin/env python3
from sqlitedict import SqliteDict

with SqliteDict('./data/premise_selection/SH-final-goal.pretty.db') as db:
    for k, v in db.items():
        for n,s in v.items():
            print(s)
            if "::" in s:
                print(f"MEET {k}:{n}")
                print(v)

