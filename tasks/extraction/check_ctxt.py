#!/bin/env python3
from sqlitedict import SqliteDict

with SqliteDict('./cache/proof_context.db') as db:
    for k, v in db.items():
        if len(v[0]) > 20:
            print(f"MEET {k}")

