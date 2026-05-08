#!/usr/bin/env python3
# Specially repair the bug that the context of about 5% premises are missing.

import logging
from tools.logger import configure_logging
from tools.server import SERVERS, CLUSTER, launch_servers
from sqlitedict import SqliteDict, decode
import msgpack as mp
import sys
import os
import asyncio
import time
from IsaREPL import Client, REPLFail
import atexit
import tools.slurm as slurm
from tools.server import test_server
import traceback
import sqlite3

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

TROUBLE = set()
TROUBLE2 = set()
TROUBLE4 = set()
LOST_NUMBER = 0

def repair():
    global LOST_NUMBER
    with sqlite3.connect('./data/premise_relevance.db') as db_conn:
        db_cursor = db_conn.cursor()
        db_cursor.execute('SELECT COUNT(*) FROM "unnamed"')
        TOTAL = db_cursor.fetchone()[0]
        db_cursor.execute('SELECT key, value FROM "unnamed"')
        count = 0
        with SqliteDict('./data/premise_info.db') as thm_db:
            for key, value in db_cursor:
                value = decode(value)
                count += 1
                if count % 1000 == 0:
                    print(f"Processed {count} keys {TOTAL}, {len(TROUBLE2)} trouble2, {len(TROUBLE4)} trouble4")
                has_trouble = 0
                for _, (_, prems, _) in value:
                    for prem in prems:
                        if prem not in thm_db:
                            has_trouble += 1
                parts = key.split(':')
                pos = f"{parts[0]}:{parts[1]}"
                num = len(parts)
                if has_trouble > 0:
                    LOST_NUMBER += has_trouble
                    print(f"has_trouble: {has_trouble} for {key}, total lost {LOST_NUMBER}")
                    if num == 4:
                        TROUBLE4.add(key)
                    TROUBLE2.add(pos)
                    TROUBLE.add(parts[0])
    with open('./cache/trouble2.txt', "w", encoding="utf-8") as f:
        for pos in TROUBLE2:
            f.write(pos)
            f.write("\n")
    with open('./cache/trouble4.txt', "w", encoding="utf-8") as f:
        for key in TROUBLE4:
            f.write(key)
            f.write("\n")
    with open('./cache/trouble.txt', "w", encoding="utf-8") as f:
        for key in TROUBLE:
            f.write(key)
            f.write("\n")

repair()
exit(0)

with open('./cache/trouble2.txt', "r", encoding="utf-8") as f:
    TROUBLE2 = set(line.strip() for line in f)
with open('./cache/trouble4.txt', "r", encoding="utf-8") as f:
    TROUBLE4 = set(line.strip() for line in f)
with open('./cache/trouble.txt', "r", encoding="utf-8") as f:
    TROUBLE = set(line.strip() for line in f)

# mk_mode_db()
# exit(0)

# with SqliteDict('./cache/mode.db') as mode_db:
#     for key in mode_db.keys():
#         _, line = key.split(':')
#         if int(line) <= 30:
#            print(key, mode_db[key])
# exit(0)

import re
def norm(s):
    return re.sub(r'(\w+)_\b', r'\1_x', s)
def norm_goal(goal):
    (hs, cl) = goal
    hs = [norm(h) for h in hs]
    cl = norm(cl)
    return (hs, cl)
def norm_premise_group(premise_group):
    (goal, (thms, acs)) = premise_group
    goal = norm_goal(goal)
    thms = [norm(thm) for thm in thms]
    acs = [norm_goal(ac) for ac in acs]
    return (goal, (thms, acs))
    


async def extract():

    total_theories = 0
    finished_theories = 0
    total_goals = 0
    finished_goals = 0

    def report():
        logger.info(f"theories: {finished_theories/total_theories*100:.2f}%, goals: {finished_goals}/{total_goals} = {finished_goals/total_goals*100:.2f}%")

    all_tasks = []
    with open('cache/trouble.txt', "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            all_tasks.append(line)
            total_theories += 1
    all_task_num = len(all_tasks)
    task_queue = asyncio.Queue()
    for task in all_tasks:
        task_queue.put_nowait(task)
    ## Group tasks by directory
    #grouped_tasks = {}
    #for task in all_tasks:
    #    # Get the directory part of the path
    #    directory = os.path.dirname(task)
    #    if directory not in grouped_tasks:
    #        grouped_tasks[directory] = []
    #    grouped_tasks[directory].append(task)

    #for directory, tasks in grouped_tasks.items():
    #    logger.info(f"Directory '{directory}': {len(tasks)} tasks")
    #task_queue = queue.Queue()
    #for directory, tasks in grouped_tasks.items():
    #    # Divide tasks into groups of at most 5
    #    for i in range(0, len(tasks), 5):
    #        task_group = tasks[i:i+5]
    #        task_queue.put(task_group)

    with SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/premise_relevance.db') as db,\
        SqliteDict('./cache/premise_extration_control.db') as control_db,\
        SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/premise_info.db') as thm_db:
        total_pairs = 0
        if '$total' in control_db:
            total_pairs = control_db['$total']
        async def translate_one(server, rpath):
            path=os.path.abspath(rpath)
            rpath=norm_file(path)
            if rpath in control_db and rpath not in TROUBLE:
                logger.info(f"skipped {rpath}")
                return
            async with Client(server, 'HOL', timeout=None) as c:
                await c.set_register_thy(False)
                await c.set_trace(False)
                await c.load_theory(['Premise_Extraction.Premise_Extraction'])

                async def interact():
                    nonlocal total_goals, finished_goals, total_pairs
                    pos = None
                    while True:
                        match await c._feed_and_unpack():
                            case (0, pos):
                                pos = encode_pos(pos)
                                run = pos in TROUBLE2
                                c.writer.write(mp.packb(run))
                                await c.writer.drain()
                                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - {pos} - reached")
                            case (6, pos, transformed, id):
                                pos = encode_pos(pos)
                                key = f"{pos}:{'T' if transformed else 'O'}:{id}"
                                run = key in TROUBLE4
                                c.writer.write(mp.packb(run))
                                await c.writer.drain()
                            case (1, pos, data):
                                pos = encode_pos(pos)
                                lens = [len(r) for _, (_, r, _) in data]
                                AC_equivs = [len(ac) for _, (_, _, ac) in data]
                                total_pairs += sum(lens)
                                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - {pos} - finished {len(data)} goals, each of length {lens}, AC equivs {AC_equivs}, and {sum(lens)} pairs. In total {total_pairs} pairs are collected.")
                                db[pos] = data
                                db.commit()
                                control_db['$total'] = total_pairs
                                control_db.commit()
                            case (7, (pos, transformed, id), data):
                                pos = encode_pos(pos)
                                key = f"{pos}:{'T' if transformed else 'O'}:{id}"
                                lens = [len(r) for _, (_, r, _) in data]
                                AC_equivs = [len(ac) for _, (_, _, ac) in data]
                                total_pairs += sum(lens)
                                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - {key} - finished {len(data)} goals, each of length {lens}, AC equivs {AC_equivs}, and {sum(lens)} pairs. In total {total_pairs} pairs are collected.")
                                db[key] = data
                                db.commit()
                                control_db['$total'] = total_pairs
                                control_db.commit()
                            case (2, premises):
                                seen = [premise for premise in premises if premise in thm_db]
                                c.writer.write(mp.packb(seen))
                                await c.writer.drain()
                            case (3, premises):
                                for premise, (defctxt, equivs) in premises.items():
                                    # existing = []
                                    # if premise in thm_db:
                                    #     (defctxt, existing) = thm_db[premise]
                                    # existing += [x for x in equivs if x not in existing]
                                    thm_db[premise] = (defctxt, equivs)
                                thm_db.commit()
                                lens = [len(r) for _, r in premises.values()]
                                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - meet {len(premises)} premises, each of {lens} AC equivs.")
                            case (4, errs):
                                logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - file {rpath} - position {pos} - Error: {"\n\n".join(errs)}")
                            case 5:
                                break
                            case (None, err):
                                raise REPLFail(f"{pos} REPL failed: " + err)
                            case (9, msgs):
                                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - {msgs}")
                            # case (11, pos):
                            #     pos = encode_pos(pos)
                            #     try:
                            #         data = old_db[pos]
                            #         #data = [(x, norm_premise_group(x)) for x in data]
                            #     except KeyError:
                            #         data = None
                            #     mp.pack(data, c.cout)
                            #     c.cout.flush()
                            # case (13, premises):
                            #     def get(premise):
                            #         try:
                            #             return old_thm_db[premise]
                            #         except KeyError:
                            #             return None
                            #     ret = [get(premise) for premise in premises]
                            #     mp.pack(ret, c.cout)
                            #     c.cout.flush()
                            # case (14, (pos, transformed, id)):
                            #     pos = encode_pos(pos)
                            #     key = f"{pos}:{'T' if transformed else 'O'}:{id}"
                            #     try:
                            #         data = old_db[key]
                            #         #data = [(x, norm_premise_group(x)) for x in data]
                            #     except KeyError:
                            #         data = None
                            #     mp.pack(data, c.cout)
                            #     c.cout.flush()
                            # case (17, pos):
                            #     pos = encode_pos(pos)
                            #     new_version = pos in mode_db
                            #     # if new_version:
                            #     #     logger.warning(f"New version {pos}: {mode_db[pos]}")
                            #     mp.pack(new_version, c.cout)
                            #     c.cout.flush()
                            case X:
                                raise REPLFail(f"{pos} Invalid message " + str(X))

                await c.run_app("Premise_Extraction")
                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - extracting {rpath}")
                c.writer.write(mp.packb(path))
                await c.writer.drain()
                await interact()
                control_db[rpath] = True
                control_db.commit()
                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - finished {rpath}")

        async def worker(server):
            nonlocal finished_theories, all_task_num
            while True:
                if not await test_server(server):
                    logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Server is down")
                    await asyncio.sleep(60)
                    continue
                try:
                    task = task_queue.get_nowait()
                except asyncio.QueueEmpty:
                    if all_task_num == 0:
                        break
                    logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} - No tasks available, waiting...")
                    await asyncio.sleep(60)
                    continue

                reentry = True
                try:
                    for _ in range(5):
                        try:
                            await translate_one(server, task)
                            reentry = False
                            finished_theories += 1
                            break
                        except ConnectionError:
                            logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Connection error in extraction {task}")
                            await asyncio.sleep(180)
                        except Exception as e:
                            traceback.print_exc()
                            logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Error extracting {task}: {e}")
                finally:
                    if reentry:
                        task_queue.put_nowait(task)
                    else:
                        all_task_num -= 1

        await asyncio.gather(*(worker(server_addr) for server_addr in SERVER_INSTANCES))

async def main():
    await launch_servers()
    await extract()

if __name__ == "__main__":
    asyncio.run(main())
