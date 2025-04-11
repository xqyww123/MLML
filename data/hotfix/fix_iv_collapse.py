import re
from sqlitedict import SqliteDict

with SqliteDict('./cache/translation/results.db') as db:
    bad = 0
    for key, value in db.items():
        match key.split(':'):
            case (file, line, _):
                (proof, _, _) = value
                matches = re.finditer(r'^.*auto_sledgehammer.*\(((\d+|\d+-\d+|\d+-),)+(\d+|\d+-\d+|\d+-)\).*$', proof, re.MULTILINE)
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
                        bad += 1
                        del db[key]
                        break
    db.commit()
    print(f"removed {bad} bad proofs")
