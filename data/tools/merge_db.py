#!/bin/env python3
from sqlitedict import SqliteDict


def merge_db(db1, db2):
    count = 0
    with SqliteDict(db1) as d1:
        with SqliteDict(db2) as d2:
            for key, value in d2.items():
                if key in d1:
                    existing = d1[key]
                    if existing != value:
                        print(f"conflict: {key}----------------------------------\n{existing}\n{value}")
                else:
                    d1[key] = value
                    count += 1
                    if count % 100 == 0:
                        d1.commit()
                    if count % 1000 == 0:
                        print(f"merged {count} entries")
            d1.commit()
    print(f"merged {count} entries")

merge_db('data/translation/results.db', '/home/xero/Current/tmp/aaa/results.db')
