from sqlitedict import SqliteDict
import numpy as np
from IsaREPL import Client
from collections import Counter
import io
from scipy.sparse import csr_matrix, save_npz, load_npz

# THMS = {}
#GRAPH = {}
INDEX = {}
THM_OCCUR = Counter()
#GOAL_OCCUR = Counter()

THM_REL = {}
THM_CSR = {}

def encode_csr(mat: csr_matrix):
    bio = io.BytesIO()
    save_npz(bio, mat, compressed=True)
    return bio.getvalue()

def decode_csr(blob: bytes):
    bio = io.BytesIO(blob)
    return load_npz(bio)

def mk_csr(counter: Counter, N: int):
    cols = np.fromiter([INDEX[thm] for thm in counter.keys()], dtype=np.int32)
    data = np.fromiter(counter.values(), dtype=np.float32)
    rows = np.zeros_like(cols, dtype=np.int32)
    v = csr_matrix((data, (rows, cols)), shape=(1, N), dtype=np.float32)
    return v

# def encode_goal(goal):
#     premises, concl = goal
#     premises = [Client.pretty_unicode(premise) for premise in premises]
#     concl = Client.pretty_unicode(concl)
#     goal = "###PREMISES\n" + "\n\n\n".join(premises) + "\n\n\n###CONCLUSION\n" + concl
#     if goal.count("###PREMISES") > 1 or goal.count("###CONCLUSION") > 1:
#         print("Warning: Found multiple occurrences of ###PREMISES or ###CONCLUSION in goal")
#         exit(1)
#     return goal

     #SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/thm2thm_rel.db') as t2t_db
with SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/premise_relevance.db') as db,\
     SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/premise_info.db') as thm_db,\
     SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/thm2thm_rel.db') as t2t_db:
    # def get_premise(premise):
    #     if premise in THMS:
    #         return THMS[premise]
    #     else:
    #         try:
    #             data = thm_db[premise]
    #         except KeyError:
    #             print(f"Warning: {premise} not found in thm_db")
    #             exit(1)
    #         defctxt, equivs = data
    #         msg = defctxt + "\n" + "\n".join(equivs)
    #         THMS[premise] = (defctxt, equivs)
    #         return (defctxt, equivs)

    num = 0
    for _, data in db.items():
        key, (_, thms, _) = data
        THM_OCCUR.update(thms)
        for thm in thms:
            if thm not in THM_REL:
                THM_REL[thm] = Counter()
            THM_REL[thm].update(thms)
            if thm not in INDEX:
                INDEX[thm] = len(INDEX)
        num += 1
        if num % 1000 == 0:
            print(f"Calculating Occurrence: Processed {num} keys")
    N = len(INDEX)
    TOTAL_NUMBER = mk_csr(THM_OCCUR, N)
    # t2t_db['$THM_OCCUR'] = encode_csr(TOTAL_NUMBER)
    # t2t_db.commit()
    num = 0
    for thm1, counter in THM_REL.items():
        csr = mk_csr(counter, N)
        THM_CSR[thm1] = csr
        # t2t_db[thm1] = encode_csr(csr)
        # num += 1
        # if num % 100 == 0:
        #     print(f"Processed {num} theorems")
        #     t2t_db.commit()
    print(f"CSR is built")
    
    for _, data in db.items():
        key, (_, thms, _) = data
        x = csr_matrix((1, N), dtype=np.float32)
        for thm in thms:
            PMI = THM_CSR[thm] * N / TOTAL_NUMBER[thm] / TOTAL_NUMBER
            np.log(PMI.data, out=PMI.data)
            np.maximum(PMI.data, 0, out=PMI.data)
            PMI.eliminate_zeros()
            


        # goal = encode_goal(key)
        # GOAL_OCCUR[goal] += 1
        # if goal not in GRAPH:
        #     GRAPH[goal] = Counter()
        # GRAPH[goal].update(thms)
    #for goal, counter in GRAPH.items():


        #goal = dctxt + "\n###PREMISES\n" + "\n\n\n".join(premises) + "\n\n\n###CONCLUSION\n" + concl
        

        
        
