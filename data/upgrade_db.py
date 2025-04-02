from sqlitedict import SqliteDict


with SqliteDict('cache/translation/results_translated.db') as db_ok:
    with SqliteDict('cache/translation/results.db') as db:
        for key, (ret, errs, pos_prf) in db.items():
            for cat, src in ret.items():
                if cat == 'isar-SH*':
                    db_ok[f"{key}:{cat}"] = (src, errs, pos_prf)
                else:
                    db_ok[f"{key}:{cat}"] = (src, [], pos_prf)
