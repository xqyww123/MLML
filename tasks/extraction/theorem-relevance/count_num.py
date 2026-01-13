from sqlitedict import SqliteDict

NUM = 0
with SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/premise_relevance.db') as db:
    for i, (_, value) in enumerate(db.items()):
        if i % 1000 == 0:
            print(f"Processed {i} keys {NUM}")
        lens = [len(r) for _, (_, r, _) in value]
        NUM += sum(lens)
print(NUM)
