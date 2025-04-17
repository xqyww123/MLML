import re
from sqlitedict import SqliteDict

with SqliteDict('cache/translation/declarations.db') as decls:
    with SqliteDict('cache/translation/results.db') as db:
        bad = {}
        for key, value in db.items():
            match key.split(':'):
                case (file, line, cat):
                    (proof, _, _) = value
                    matches = re.finditer(r'^.*(NEXT|END|NXT).*\(((\d+|\d+-\d+|\d+-),)+(\d+|\d+-\d+|\d+-)\).*$', proof, re.MULTILINE)
                    #matches = re.finditer(r'^.*auto_sledgehammer.*\(((\d+|\d+-\d+|\d+-),)+(\d+|\d+-\d+|\d+-)\).*$', proof, re.MULTILINE)
                    def check_bad(cmd):
                        for sequence in re.finditer(r'\([\d\-,]+\)', cmd):
                            raw_intervals = sequence.group(0).strip('()').split(',')
                            def parse(item):
                                match item.split('-'):
                                    case [a,'']:
                                        return (int(a), int(98123456789))
                                    case [a, b]:
                                        return (int(a), int(b))
                                    case [a]:
                                        return (int(a), int(a))
                            intervals = [parse(item) for item in raw_intervals]
                            intervals.sort(key=lambda x: x[0])
                            # Check for collapsed adjacent intervals
                            for i in range(len(intervals)-1):
                                if intervals[i+1][0] <= intervals[i][1]:
                                    print(f"Interval collapses! {cmd}")
                                    return True
                        return False
                    for cmd in matches:
                        if check_bad(cmd.group(0)):
                            if cat not in bad:
                                bad[cat] = 0
                            bad[cat] += 1
                            del db[key]
                            if f"{file}:{cat}" in decls:
                                del decls[f"{file}:{cat}"]
                            break
        db.commit()
        decls.commit()
        print(f"removed {sum(bad.values())} bad proofs")
        for cat, count in bad.items():
            print(f"{cat}: {count}")
