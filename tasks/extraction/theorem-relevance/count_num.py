from sqlitedict import SqliteDict, decode
import sqlite3

DB_PATH = '/home/qiyuan/Current/MLML/data/premise_relevance.db'
db_conn = sqlite3.connect(DB_PATH)
db_cursor = db_conn.cursor()
db_cursor.execute('SELECT COUNT(*) FROM "unnamed"')
TOTAL = db_cursor.fetchone()[0]
NUM = 0
db_cursor.execute('SELECT key, value FROM "unnamed"')
for i, (key, value) in enumerate(db_cursor):
    if i % 1000 == 0:
        print(f"Processed {i}/{TOTAL} keys, {NUM} premises")
    value = decode(value)
    lens = [len(r) for _, (_, r, _, _, _, _) in value]
    NUM += sum(lens)
db_conn.close()
print(f"Total: {NUM}")