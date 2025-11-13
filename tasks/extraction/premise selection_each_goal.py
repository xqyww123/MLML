#!/bin/env python3

"""
Add premise selection information into ./cache/SH_premise_selection.db
"""

import logging
from tools.logger import configure_logging
from data.isabelle import Position, load_ISAR_PROOF_INDEX
from sqlitedict import SqliteDict
from IsaREPL import Client, REPLFail
import os
import queue
import time
import threading

configure_logging(level=logging.INFO)

pos = load_ISAR_PROOF_INDEX()
threadLock = threading.Lock()
counter = 0

with SqliteDict('./cache/SH_premise_selection.db') as db:
    pre_total = len(pos)
    complete_indexes = set()
    for j, (key, val) in enumerate(db.items()):
        if j % 1000 == 0:
            logging.info(f"Checking [{j}/{pre_total}] records...")
        if isinstance(val, int) or len(val) <= 10:
            continue
        complete_indexes.add(key)

    task_queue = queue.Queue()
    the_chunk = []
    last_file = None
    total = 0
    for spec_pos, proof_pos in sorted(pos.items()):
        if last_file != spec_pos.file:
            if last_file is not None:
                task_queue.put(the_chunk)
            the_chunk = []
            last_file = spec_pos.file
        key = f'{spec_pos.file}:{spec_pos.line}#0'
        if key in complete_indexes:
            continue
        total += 1
        the_chunk.append((spec_pos, proof_pos))
    if last_file is not None:
        task_queue.put(the_chunk)
    logging.info(f"{total} tasks in total.")

    def worker():
        global counter
        while True:
            with Client('127.0.0.1:6666', 'HOL') as c:
                while True:
                    try:
                        chunk = task_queue.get(timeout=1)
                    except queue.Empty:
                        return
                    for spec_pos, proof_pos in chunk:
                        with threadLock:
                            counter += 1
                            if counter % 1000 == 0:
                                c.clean_cache()
                        try:
                            key = f'{spec_pos.file}:{spec_pos.line}'
                            if key in db and len(db[f"{key}#0"]) > 10:
                                continue
                            try:
                                file = os.path.abspath(proof_pos.file)
                                c.file(file, line=proof_pos.line, column=proof_pos.column, cache_position=True, use_cache=True)
                            except REPLFail as e:
                                logging.error(f"Error loading file {proof_pos.file}: {e}")
                                continue
                            res = c.premise_selection('each', 1000, ['mesh'], {}, 'pretty')
                            db[key] = len(res)
                            for j, r in enumerate(res):
                                db[f'{key}#{j}'] = r
                                # if counter % 100 == 0:
                                #    logging.info(r)
                            db.commit()
                            logging.info(f"[{counter}/{total}] obtained {len(res[0])} for {proof_pos}")
                        except Exception as e:
                            logging.error(f"Error: {e}")
                            exit(1)
                            time.sleep(3)
                            break
                        # if iter % 100 == 0:
                        #     logging.info(f"Processed {iter} propositions")
                        #     db.commit()
    threads = []
    for _ in range(24):
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
    
