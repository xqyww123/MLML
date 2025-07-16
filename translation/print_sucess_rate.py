from sqlitedict import SqliteDict

counts = {}
counts['origin'] = 0
with SqliteDict('./data/translation/results.db') as db:
    for key, value in db.items():
        (_,_,cat) = key.split(':')
        (_,err,_,_) = value
        if err:
            continue
        if cat not in counts:
            counts[cat] = 0
        counts[cat] += 1

print(f"total: {counts['origin']}")
for cat, count in counts.items():
    print(f"{cat}: {count / counts['origin'] * 100:.2f}%")
