#!/usr/bin/env python3
# Positions of statements, proofs, and ends of proofs

import logging
from tools.logger import configure_logging
from tools.server import SERVERS, launch_servers
from sqlitedict import SqliteDict
import os
import threading
import time
from IsaREPL import Client, REPLFail
import queue
from tools.server import test_server
import traceback

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

def extract():
    total_theories = 0
    finished_theories = 0
    # Add a lock for thread-safe counter operations
    task_counter_lock = threading.Lock()

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

    with SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/basic_info.db') as db:
        def process_one(server, rpath):
            nonlocal finished_theories
            path=os.path.abspath(rpath)
            rpath=norm_file(path)
            if rpath in db:
                logger.info(f"skipped {rpath}")
                return
            with Client(server, 'HOL', timeout=None) as client:
                client.set_register_thy(False)
                with open(path, 'r') as file:
                    src = file.read()
                directory = os.path.dirname(path)
                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {client.client_id} - evaluating {rpath}")
                session = client.session_name_of(path)
                client.set_thy_qualifier(session)
                eval_info = client.eval(src, import_dir=directory, base_dir=directory)
                tr_pos1 = client.translate_position(src)
                def tr_pos(pos):
                    ret = tr_pos1(pos)
                    ret.file = rpath
                    return ret
                mode = 'normal'
                statement_begin = None
                statement_end = None
                proof_begin = None
                proof_end = None
                statement = None
                proof = []
                ALL_CMDS = []
                DATA = []
                for cmd_info in eval_info:
                    begin_pos, end_pos = cmd_info.range
                    begin_pos = tr_pos(begin_pos)
                    end_pos = tr_pos(end_pos)
                    cmd_info.range = (begin_pos, end_pos)
                    ALL_CMDS.append(cmd_info)
                    if mode == 'proof':
                        proof.append((cmd_info.command, begin_pos, end_pos))
                        if proof_begin is None:
                            proof_begin = begin_pos
                        if cmd_info.flags.is_theory:
                            proof_end = end_pos
                            DATA.append((statement, proof, statement_begin, statement_end, proof_begin, proof_end))
                            mode = 'normal'
                            statement_begin = None
                            statement_end = None
                            proof_begin = None
                            proof_end = None
                            proof = []
                            statement = None
                    elif mode == 'normal' and cmd_info.flags.is_proof:
                        mode = 'proof'
                        statement_begin = cmd_info.range[0]
                        statement_end = cmd_info.range[1]
                        statement = cmd_info.command
                db[rpath] = (DATA, ALL_CMDS)
                db.commit()
                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {client.client_id} - finished {rpath}")

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
                
                reentry = False
                try:
                    # Create a copy of the group for iteration
                    for _ in range(5):
                        try:
                            process_one(server, task)
                            finished_theories += 1
                            #reentry = False
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
