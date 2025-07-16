#!/bin/env python3

"""
Add premise selection information into ./cache/SH_premise_selection.db
"""

import logging
from data.isabelle import Position, load_ISAR_PROOF_INDEX
from sqlitedict import SqliteDict
from IsaREPL import Client, REPLFail
import os
import queue
import time
import threading

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

pos = load_ISAR_PROOF_INDEX()
total = len(pos)
logging.info(f"{total} propositions to be processed")

iter = 0
task_queue = queue.Queue()
for spec_pos, proof_pos in sorted(pos.items()):
    task_queue.put((spec_pos, proof_pos))

threadLock = threading.Lock()
counter = 0

with SqliteDict('./cache/SH_premise_selection.db') as db:
    def worker():
        global counter
        while True:
            with Client('127.0.0.1:6666', 'HOL') as c:
                while True:
                    try:
                        (spec_pos, proof_pos) = task_queue.get(timeout=1)
                    except queue.Empty:
                        return
                    with threadLock:
                        counter += 1
                        if counter % 3000 == 0:
                            c.clean_cache()
                    try:
                        key = f'{spec_pos.file}:{spec_pos.line}'
                        if key in db and len(db[key]) > 10:
                            continue
                        try:
                            file = os.path.abspath(proof_pos.file)
                            c.file(file, line=proof_pos.line, column=proof_pos.column, cache_position=True, use_cache=True)
                        except REPLFail as e:
                            logging.error(f"Error loading file {proof_pos.file}: {e}")
                            continue
                        res = c.premise_selection(1000, ['mesh'], {}, 'pretty')
                        db[key] = res
                        db.commit()
                        logging.info(f"[{counter}/{total}] obtained {len(res)} for {proof_pos}")
                    except Exception as e:
                        logging.error(f"Error: {e}")
                        exit(1)
                        time.sleep(3)
                        break
                    # if iter % 100 == 0:
                    #     logging.info(f"Processed {iter} propositions")
                    #     db.commit()
    threads = []
    for _ in range(16):
        thread = threading.Thread(target=worker)
        thread.daemon = True  # Make threads daemon so they exit if main thread exits
        threads.append(thread)
        thread.start()
        
    # Wait for all threads to complete
    for thread in threads:
        thread.join()

    db.commit()
    db.close()

logging.info('Done')
    
