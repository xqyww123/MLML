#!/bin/env python


from sqlitedict import SqliteDict
import sys
import csv
from collections import Counter

total = 0
success = 0
distr = Counter({})

COMMANDS = {'HAVE', 'END', 'NEXT', 'CONSIDER', 'RULE', 'UNFOLD', 'INTRO', 'APPLY', 'CRUSH',
            'CASE_SPLIT', 'INDUCT', 'OPEN_MODULE', 'CONFIG', 'DEFINE', 'LET', 'NOTATION'}

def distr_of_commands (script):
    all_commands = [line.split()[0] for line in script.splitlines() if line.strip() and line.split()]
    commands = [word for word in all_commands if word in COMMANDS]
    return Counter(commands)


decl = 0
with SqliteDict('data/translation/results.db') as db:
    for k,v in db.items():
        file,line,cat = k.split(':')
        if cat == 'origin':
            decl += 1
            total += 1
        if cat == 'raw':
            success += 1
            src, err, _ = v
            d = distr_of_commands(src)
            distr.update(d)
    #with open('result.csv', 'w', newline='') as f:
    #    w = csv.writer(f, delimiter=',', quotechar='\"', quoting=csv.QUOTE_MINIMAL)
    #    for k,v in db.items():
    #        match k.split(':'):
    #            case (file,line,cat):
    #                decl += 1
    #            case (file,line):
    #                if v[1]:
    #                    for t,s in v[1].items():
    #                        w.writerow([file,line,v[0],t,s])
    #                else:
    #                    w.writerow([file, line, v[0], v[1]])
    #                total += 1
    #                if v[1]:
    #                    success += 1
    #                    d = distr_of_commands(v[1]['refined'])
    #                    distrs[file, line] = d
    #                    distr.update(d)

print(f"{success} / {total} = {success / total}")
print(f"{decl} decls")

total_count = sum(distr.values())
percentage_distribution = {word: (count / total_count * 100) for word, count in distr.items()}
print(percentage_distribution)
aaa = [{'name': word, 'value': count / total_count * 100} for word, count in distr.items()]
print(aaa)

