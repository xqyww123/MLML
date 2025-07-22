from sqlitedict import SqliteDict
import os
from collections import namedtuple

_DB = None
Context = namedtuple('Context', ['local_facts', 'assumptions', 'binding', 'fixes', 'goals'])

def get_db():
    global _DB
    if _DB is None:
        path = f"./data/proof_context.db"
        if not os.path.exists(path):
            raise Exception(f"Proof context database is lost!")
        _DB = SqliteDict(path)
    return _DB

def get_context(file, line, pp='pretty'):
    db = get_db()
    key = f"{file}:{line}:{pp}"
    if key in db:
        return Context(*db[key])
    else:
        return None
