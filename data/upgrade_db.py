from sqlitedict import SqliteDict


# with SqliteDict('cache/translation/results_translated.db') as db_ok:
#     with SqliteDict('cache/translation/results.db') as db:
#         for key, (ret, errs, pos_prf) in db.items():
#             for cat, src in ret.items():
#                 if cat == 'isar-SH*':
#                     db_ok[f"{key}:{cat}"] = (src, errs, pos_prf)
#                 else:
#                     db_ok[f"{key}:{cat}"] = (src, [], pos_prf)
#             db_ok.commit()


print("Declarations:")
with SqliteDict('cache/translation/declarations.db') as db:
    for key, val in list(db.items()):
        match key.split(':'):
            case [file,line,column]:
                print(f"{file}:{line}:{column}")
#num = 0
#with SqliteDict('cache/translation/declarations.db') as db:
#    for key, val in list(db.items()):
#        if ':' not in key:
#            if val != True:
#                print(f"ERROR: Declaration {key} is not True")
#                exit(1)
#            for cat in ['origin', 'goal', 'isar-SH*']:
#                db[f"{key}:{cat}"] = True
#            del db[key]
#            db.commit()
#            print(f"Upgraded {key}")
#            num += 1
#print(f"Upgraded {num} declarations")
#

# with SqliteDict('cache/translation/declarations.db') as decls:
#     with SqliteDict('cache/translation/results.db') as db:
#         for key, val in db.items():
#             match key.split(':'):
#                 case [file,line,cat]:
#                     print(f"{file}:{line}:{cat}")

