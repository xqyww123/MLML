from sqlitedict import SqliteDict
import os
from tools import MLML_BASE

_DBS = {}

def get_db(method, pp):
    if (method, pp) in _DBS:
        return _DBS[(method, pp)]
    else:
        path = f"{MLML_BASE}/data/premise_selection/{method}.{pp}.db"
        if not os.path.exists(path):
            raise Exception(f"No premise selection database available for ({method}, {pp})")
        db = SqliteDict(path)
        _DBS[(method, pp)] = db
        return db

def premise_of(method, pp, file, line):
    db = get_db(method, pp)
    key = f"{file}:{line}"
    if key in db:
        return db[key]
    else:
        return None