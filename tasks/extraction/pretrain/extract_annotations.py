#!/usr/bin/env python3

import logging
from tools.logger import configure_logging
from tools.server import SERVERS, CLUSTER, launch_servers
from sqlitedict import SqliteDict
import msgpack as mp
import os
import threading
import time
from IsaREPL import Client, REPLFail
import queue
import tools.slurm as slurm
from tools.server import test_server
import traceback
import sys

if len(sys.argv) < 2:
    print("Usage: python extract_annotations.py <formats of term printing>")
    exit(1)
pp_names = sys.argv[1:]

configure_logging(level=logging.INFO)
logger = logging.getLogger(__name__)

SERVER_INSTANCES = []
for server, data in SERVERS.items():
    SERVER_INSTANCES.extend([server] * data["num-translator"])
logger.info(f"SERVER_INSTANCES: {SERVER_INSTANCES}")

# os.makedirs(f"{os.getcwd()}/cache/translation/tmp", exist_ok=True)
# INIT_SCRIPT = f"""
# ML_Translator_Top.init_translator {translation_target_str} (ML_Translator_Top.interactive_reporter());
# REPL_Server.register_app "Minilang-Translator" ML_Translator_Top.REPL_App
# """

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
    #print(pos)
    return f'{norm_file(pos[3][1])}:{pos[0]}:{pos[1]}'

def watcher(client_id, status):
    is_live, errors = status
    logger.error(f"Client {client_id} is {'' if is_live else 'not '}live. Errors: {errors}")


def extract():
    total_theories = 0
    finished_theories = 0
    total_goals = 0
    finished_goals = 0
    # Add a lock for thread-safe counter operations
    task_counter_lock = threading.Lock()

    def report():
        logger.info(f"theories: {finished_theories/total_theories*100:.2f}%, goals: {finished_goals}/{total_goals} = {finished_goals/total_goals*100:.2f}%")

    all_tasks = []
    with open('translation/targets', "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            all_tasks.append(line)
            total_theories += 1
    all_task_num = len(all_tasks)
    task_queue = queue.Queue()
    for task in all_tasks:
        task_queue.put(task)

    with SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/annotations_on_original_isar.db') as db,\
        SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/annotations_on_original_isar_control.db') as control_db:
        total_annotations = 0
        if '$total' in control_db:
            total_annotations = control_db['$total']
        def translate_one(server, rpath):
            path=os.path.abspath(rpath)
            rpath=norm_file(path)
            if rpath in control_db:
                logger.info(f"skipped {rpath}")
                return
            with Client(server, 'HOL', timeout=None) as c:
                c.set_register_thy(False)
                c.set_trace(False)
                c.load_theory(['Pretrain_Extraction.Pretrain_Extraction'])

                def interact():
                    nonlocal total_goals, finished_goals, total_annotations
                    pos = None
                    while True:
                        match c.unpack.unpack():
                            case (0, pos):
                                pos = encode_pos(pos)
                                run = pos not in db
                                mp.pack(run, c.cout)
                                c.cout.flush()
                                #logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - {pos} - reached")
                            case (1, pos, data):
                                pos = encode_pos(pos)
                                num = len(data[0])
                                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - {pos} - get {num} annotations. In total {total_annotations}  are collected.")
                                #logger.info(str(data))
                                db[pos] = data
                                db.commit()
                                total_annotations += num
                                control_db['$total'] = total_annotations
                                control_db.commit()
                            case (2, msgs):
                                logger.debug(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - {msgs}")
                            case (3, errs):
                                logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - file {rpath} - position {pos} - Error: {"\n\n".join(errs)}")
                            case 5:
                                break
                            case (None, err):
                                raise REPLFail(f"{pos} REPL failed: " + err)
                            case X:
                                raise REPLFail(f"{pos} Invalid message " + str(X))

                c.run_app("Pretrain_Extraction")
                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - annotating {rpath}")
                mp.pack((path, pp_names), c.cout)
                c.cout.flush()
                interact()
                control_db[rpath] = True
                control_db.commit()
                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - finished {rpath}")

        def worker(server):
            nonlocal finished_theories, all_task_num
            while True:
                if not test_server(server):
                    logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Server is down")
                    time.sleep(60)
                    continue
                try:
                    task = task_queue.get(timeout=1)
                except queue.Empty:
                    if all_task_num == 0:
                        break
                    logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} - No tasks available, waiting...")
                    time.sleep(60)
                    continue
                
                reentry = True
                try:
                    # Create a copy of the group for iteration
                    for _ in range(5):
                        try:
                            translate_one(server, task)
                            reentry = False
                            finished_theories += 1
                            break
                        except ConnectionError:
                            logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Connection error in extraction {task}")
                            time.sleep(180)
                        except Exception as e:
                            # reentry = False
                            # finished_theories += 1
                            traceback.print_exc()
                            logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Error extracting {task}: {e}")
                finally:
                    # Mark the current group as done and requeue any remaining failed tasks
                    task_queue.task_done()
                    
                    # Put any remaining tasks back in the queue
                    if reentry:
                        task_queue.put(task)
                    else:
                        # Use lock to make the decrement operation atomic
                        with task_counter_lock:
                            all_task_num -= 1

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
    launch_servers()
    # ACTIVE_SERVERS = {k for k, v in SERVERS.items() if v["num-translator"] > 0}
    # for server in ACTIVE_SERVERS:
    #     Client.install_watcher(server, watcher, interval=1)
    extract()
