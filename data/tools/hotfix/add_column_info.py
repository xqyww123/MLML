#!/bin/env python3

from IsaREPL import Client, Position
from sqlitedict import SqliteDict
import logging
import re

c = Client('127.0.0.1:6666', 'HOL')
c.set_register_thy (False)

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

def is_goal(src):
    if src.startswith('private'):
        src = re.sub(r'^private\s*', '', src)
    if src.startswith('qualified'):
        src = re.sub(r'^qualified\s*', '', src)
    ret = (src.startswith('lemma') and not src.startswith('lemmas')) or\
        src.startswith('theorem') or src.startswith('corollary') or src.startswith('proposition') or\
        src.startswith('schematic_goal') or src.startswith('interpretation') or src.startswith('global_interpretation') or src.startswith('sublocale')
    return ret

_LEX = {}
with SqliteDict('./cache/translation/lex.db', autocommit=True) as lex_db:
    def lex_of(file):
        if file in _LEX:
            return _LEX[file]
        elif file in lex_db:
            ret = lex_db[file]
            _LEX[file] = ret
            return ret
        else:
            lex = c.lex_file(file)
            lex2 = []
            for i in range(len(lex) - 1):
                if is_goal(lex[i][1]):
                    lex2.append(lex[i])
                    lex2.append(lex[i+1])
                    if lex[i][0].line == lex[i+1][0].line and is_goal(lex[i+1][1]):
                        logging.error(f"Conflict of line occurs at {file}:{lex[i][0]}")
            lex_db[file] = lex2
            lex_db.commit()
            _LEX[file] = lex2
            return lex2

    def column_of(file, line):
        lex = lex_of(file)
        for i in range(len(lex)):
            if lex[i][0].line == line:
                return (lex[i][0].column, lex[i+1][0].column)
        raise ValueError(f"Line {line} not found in {file}")

    iter = 0
    with SqliteDict('./cache/translation/results.db') as db:
        total_cases = len(db)
        with SqliteDict('./cache/translation/fixed_results.db') as dbf:
            for k, v in db.items():
                iter += 1
                if k in dbf:
                    continue
                file, spec_line, cat = k.split(':')
                spec_line = int(spec_line)
                if file == './contrib/Isabelle2024/src/HOL/Computational_Algebra/Polynomial.thy' and spec_line == 5785:
                    spec_line = 5783
                (src, err, prf_pos) = v
                spec_col, prf_col = column_of(file, spec_line)
                prf_pos = Position.from_s(prf_pos)
                #prf_col = column_of(file, prf_pos.line)
                if spec_col == prf_col and spec_line == prf_pos.line:
                    print("BAD")
                    exit(1)
                prf_pos.column = prf_col
                prf_pos = str(prf_pos)
                dbf[k] = (src, err, prf_pos, spec_col)
                if iter % 100 == 0:
                    logging.info(f"{file}:{spec_line}:{spec_col} -> {prf_pos}")
                    logging.info(f"Processed {iter}/{total_cases} cases")
                    dbf.commit()
        dbf.commit()

