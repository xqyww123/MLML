#!/usr/bin/env python3
from sqlitedict import SqliteDict

def prt(pos):
    return f"{pos.line}:{pos.column}"

with SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/positions.db') as db:
    for key, (value, _) in db.items():
        for (cmd, prf, statement_begin, statement_end, proof_begin, proof_end) in value:
            print(f"{key}, statement: {prt(statement_begin)} - {prt(statement_end)}, proof: {prt(proof_begin)} - {prt(proof_end)}. {cmd}\n {prf}\n\n")
