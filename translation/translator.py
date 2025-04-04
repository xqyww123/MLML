#!/usr/bin/env python3

import logging
from tools.server import SERVERS, CLUSTER, launch_servers
from sqlitedict import SqliteDict
import msgpack as mp
import sys
import os
import concurrent.futures
import threading
import time
from IsaREPL import Client, REPLFail
import queue
import atexit
import tools.slurm as slurm
from tools.server import test_server

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)

SERVER_INSTANCES = []
for server, data in SERVERS.items():
    SERVER_INSTANCES.extend([server] * data["num-translator"])


KNOWN_TRANSLATION_TARGETS = {"origin", "isar-SH", "isar-SH*", "refined", "raw", "reord_raw", "reord_refined", 'goal'}

if len(sys.argv) > 1:
    translation_targets = sys.argv[1:]
    quotes = ['\"' + t + '\"' for t in translation_targets]
    translation_target_str = f"[{', '.join(quotes)}] "
else:
    logger.error("Translation targets must be provided.\n"
                 "Available targets: " + ", ".join(KNOWN_TRANSLATION_TARGETS))
    exit(1)

if any(target not in KNOWN_TRANSLATION_TARGETS for target in translation_targets):
    logger.error("Unknown translation targets: " + ", ".join(translation_targets) +
                "\nAvailable targets: " + ", ".join(KNOWN_TRANSLATION_TARGETS))
    exit(1)

os.makedirs(f"{os.getcwd()}/cache/translation/tmp", exist_ok=True)
INIT_SCRIPT = f"""
ML_Translator_Top.init_translator {translation_target_str} (Path.explode "{os.getcwd()}/cache/translation/tmp") (ML_Translator_Top.interactive_reporter());
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

def translate():

    total_theories = 0
    finished_theories = 0
    total_goals = 0
    finished_goals = {}

    def add_goal(ret):
        for cat in ret:
            if cat in finished_goals:
                finished_goals[cat] += 1
            else:
                finished_goals[cat] = 1

    def report():
        s = [f"theories: {finished_theories/total_theories*100:.2f}%, goals: {total_goals}"]
        for cat, count in finished_goals.items():
            s.append(f"{cat}: {count / total_goals * 100:.2f}%")
        logger.info(", ".join(s))

    all_tasks = []
    with open('translation/targets', "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            all_tasks.append(line)
            total_theories += 1
    # Group tasks by directory
    grouped_tasks = {}
    for task in all_tasks:
        # Get the directory part of the path
        directory = os.path.dirname(task)
        if directory not in grouped_tasks:
            grouped_tasks[directory] = []
        grouped_tasks[directory].append(task)

    for directory, tasks in grouped_tasks.items():
        logger.debug(f"Directory '{directory}': {len(tasks)} tasks")
    task_queue = queue.Queue()
    for directory, tasks in grouped_tasks.items():
        task_queue.put(tasks)

    with SqliteDict('./cache/translation/results.db') as db:
        with SqliteDict('./cache/translation/declarations.db', autocommit=True) as db_decl:
            def translate_one(server, rpath):
                path=os.path.abspath(rpath)
                rpath=norm_file(path)
                if all(f"{rpath}:{target}" in db_decl for target in translation_targets):
                    logger.info(f"skipped {rpath}")
                    return
                with Client(server, 'HOL') as c:
                    c.set_register_thy(False)
                    c.set_trace(False)
                    c.load_theory(['Minilang_Translator.MS_Translator_Top'])
                    c.run_ML("Minilang_Translator.MS_Translator_Top", INIT_SCRIPT)

                    def interact():
                        nonlocal total_goals, finished_goals
                        while True:
                            match c.unpack.unpack():
                                case (0, pos):
                                    pos = encode_pos(pos)
                                    run = False
                                    for target in translation_targets:
                                        key = f"{pos}:{target}"
                                        if key not in db or db[key][1]:
                                            run = True
                                            break
                                    mp.pack(run, c.cout)
                                    c.cout.flush()
                                case (2, pos_spec, pos_prf, ret):
                                    total_goals += 1
                                    pos_spec = encode_pos(pos_spec)
                                    pos_prf = encode_pos(pos_prf)
                                    if all(not err for _, (_, err) in ret.items()):
                                        logger.info(f"{server} - {pos_spec} succeeds")
                                        logger.info(ret[translation_targets[0]][0])
                                    for cat, (src, err) in ret.items():
                                        db[f"{pos_spec}:{cat}"] = (src, err, pos_prf)
                                        if err:
                                            logger.info(f"{server} - {pos_spec} - {cat} fails: {err}")
                                        else:
                                            if cat in finished_goals:
                                                finished_goals[cat] += 1
                                            else:
                                                finished_goals[cat] = 1
                                    report()
                                    db.commit()
                                case 3:
                                    break
                                case (4, pos, src):
                                    # declarations
                                    pos = encode_pos2(pos)
                                    db_decl[pos] = src
                                case (5, pos, header):
                                    pos = encode_pos(pos)
                                    db_decl[':header:'+pos] = header
                                case (7, err):
                                    raise REPLFail(err)
                                case X:
                                    raise REPLFail("Invalid message " + str(X))

                    c.run_app("Minilang-Translator")
                    logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} - translating {rpath}")
                    mp.pack((path, translation_targets), c.cout)
                    c.cout.flush()
                    interact()
                    for target in translation_targets:
                        db_decl[f"{rpath}:{target}"] = True
                    db_decl.commit()
                    logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} - finished {rpath}")

            def worker(server):
                nonlocal finished_theories
                while True:
                    if not test_server(server):
                        logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Server is down")
                        time.sleep(60)
                        continue
                    try:
                        group = task_queue.get(timeout=1)
                    except queue.Empty:
                        return
                    
                    try:
                        # Create a copy of the group for iteration
                        for rpath in group[:]:
                            success = False
                            for _ in range(10):
                                try:
                                    translate_one(server, rpath)
                                    success = True
                                    finished_theories += 1
                                    group.remove(rpath)  # Remove succeeded task from group
                                    break
                                except REPLFail as e:
                                    group.remove(rpath)  # Remove bad task from group
                                    logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Error translating {rpath}: {e}")
                                    break
                                except ConnectionError:
                                    logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Connection error translating {rpath}")
                                    time.sleep(60)
                                except Exception as e:
                                    logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Error translating {rpath}: {e}")
                                    time.sleep(10)
                    finally:
                        # Mark the current group as done and requeue any remaining failed tasks
                        task_queue.task_done()
                        
                        # Put any remaining tasks back in the queue
                        if group:
                            task_queue.put(group)

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
    translate()