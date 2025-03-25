#!/usr/bin/env python3

import logging
from evaluation.server import SERVERS
from sqlitedict import SqliteDict
import msgpack as mp
import sys
import os
import concurrent.futures
import threading
import time
from IsaREPL import Client
import queue

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)

SERVER_INSTANCES = []
for server, (_, numproc) in SERVERS.items():
    numconn = max(int (numproc * 0.6), 1)
    SERVER_INSTANCES.extend([server] * numconn)

os.makedirs(f"{os.getcwd()}/cache/translation/tmp", exist_ok=True)
INIT_SCRIPT = f"""
ML_Translator_Top.init_translator (Path.explode "{os.getcwd()}/cache/translation/tmp") (ML_Translator_Top.interactive_reporter());
REPL_Server.register_app "Minilang-Translator" ML_Translator_Top.REPL_App
"""

def norm_file(file):
    if os.path.isabs(file):
        try:
            rel_path = os.path.relpath(file, os.getcwd())
            file = './' + rel_path if not rel_path.startswith('.') else rel_path
            return file
        except ValueError:
            return file

def encode_pos (pos):
    return f'{norm_file(pos[3][1])}:{pos[0]}'

def encode_pos2 (pos):
    return f'{norm_file(pos[3][1])}:{pos[0]}:{pos[1]}'

def translate(result_path : str):

    total_tasks = 0
    finished_tasks = 0
    task_queue = queue.Queue()
    with open('translation/targets', "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            task_queue.put(line)
            total_tasks += 1

    with SqliteDict(result_path) as db:
        def translate_one(server, rpath):
            path=os.path.abspath(rpath)
            rpath=norm_file(path)
            if rpath in db:
                logger.info(f"skipped {rpath}")
                return
            with Client(server, 'HOL') as c:
                c.set_register_thy(False)
                c.set_trace(False)
                c.load_theory(['Minilang_Translator.MS_Translator_Top'])
                c.run_ML("Minilang_Translator.MS_Translator_Top", INIT_SCRIPT)

                def interact():
                    while True:
                        match c.unpack.unpack():
                            case (0, pos):
                                pos = encode_pos(pos)
                                run = False
                                try:
                                    run = not db[pos][0]
                                except KeyError:
                                    run = True
                                mp.pack(run, c.cout)
                                c.cout.flush()
                            case (1, pos_spec, pos_prf, origin, err):
                                logger.error(f"[{finished_tasks}/{total_tasks}] - {server} - {norm_file(pos_spec[3][1])}:{pos_spec[0]} fails")
                                logger.error(err)
                                pos_spec = encode_pos(pos_spec)
                                pos_prf = encode_pos(pos_prf)
                                db[pos_spec] = (False, err, origin, pos_prf)
                                db.commit()
                            case (2, pos_spec, pos_prf, origin, ret):
                                logger.info(f"[{finished_tasks}/{total_tasks}] - {server} - {norm_file(pos_spec[3][1])}:{pos_spec[0]} succeeds")
                                logger.info(ret['refined'])
                                pos_spec = encode_pos(pos_spec)
                                pos_prf = encode_pos(pos_prf)
                                db[pos_spec] = (True, ret, origin, pos_prf)
                                db.commit()
                            case 3:
                                break
                            case (4, pos, src):
                                pos = encode_pos2(pos)
                                db[pos] = src
                            case (5, pos, header):
                                pos = encode_pos(pos)
                                db[':header:'+pos] = header
                            case X:
                                raise Exception("Invalid message " + X)

                c.run_app("Minilang-Translator")
                logger.info(f"[{finished_tasks}/{total_tasks}] - {server} - translating {rpath}")
                mp.pack(path, c.cout)
                c.cout.flush()
                interact()
                db[rpath] = True
                db.commit()
                logger.info(f"[{finished_tasks}/{total_tasks}] - {server} - finished {rpath}")

        def worker(server):
            nonlocal finished_tasks
            while True:
                try:
                    rpath = task_queue.get(timeout=1)
                except queue.Empty:
                    return
                success = False
                try:
                    while not success:
                        try:
                            translate_one(server, rpath)
                            success = True
                        except Exception as e:
                            logger.error(f"[{finished_tasks}/{total_tasks}] - {server} - Error translating {rpath}: {e}")
                            time.sleep(10)
                finally:
                    if success:
                        finished_tasks += 1
                        task_queue.task_done()
                    else:
                        task_queue.put(rpath)

        # Create and start worker threads for each server
        threads = []
        for server_addr in SERVER_INSTANCES:
            thread = threading.Thread(target=worker, args=(server_addr,))
            thread.daemon = True  # Make threads daemon so they exit if main thread exits
            threads.append(thread)
            thread.start()
            
        # Wait for all threads to complete
        for thread in threads:
            thread.join()

if __name__ == "__main__":
    translate('./cache/translation/results.db')