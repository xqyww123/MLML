from sqlitedict import SqliteDict
from IsaREPL import Client, REPLFail

with SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/premise_relevance.db') as db_org,\
    SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/premise_info.db') as thm_db_org,\
    SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/premise_relevance.unicode.db') as db,\
    SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/premise_info.unicode.db') as thm_db:
    for key, value in db_org.items():
        premises, concl = key
        premises = [Client.pretty_unicode(premise) for premise in premises]
        concl = Client.pretty_unicode(concl)
        key2 = (premises, concl)
