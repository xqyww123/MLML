#!/usr/bin/env python3

import logging
from tools.logger import configure_logging
from tools.server import SERVERS, CLUSTER, launch_servers
from sqlitedict import SqliteDict
import msgpack as mp
import os
import asyncio
import time
from IsaREPL import Client, REPLFail
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

def watcher(client_id, status):
    is_live, errors = status
    logger.error(f"Client {client_id} is {'' if is_live else 'not '}live. Errors: {errors}")


async def extract():
    total_theories = 0
    finished_theories = 0
    total_goals = 0
    finished_goals = 0

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
    task_queue = asyncio.Queue()
    for task in all_tasks:
        task_queue.put_nowait(task)

    with SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/annotations_on_elaborated_isar.db') as db,\
        SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/annotations_on_elaborated_isar_control.db') as control_db:
        total_annotations = 0
        if '$total' in control_db:
            total_annotations = control_db['$total']
        async def translate_one(server, rpath):
            path=os.path.abspath(rpath)
            rpath=norm_file(path)
            if rpath in control_db:
                logger.info(f"skipped {rpath}")
                return
            async with Client(server, 'HOL', timeout=None) as c:
                await c.set_register_thy(False)
                await c.set_trace(False)
                await c.load_theory(['Pretrain_Extraction.Pretrain_Extraction'])

                async def interact():
                    nonlocal total_goals, finished_goals, total_annotations
                    pos = None
                    while True:
                        match await c._feed_and_unpack():
                            case (0, pos):
                                pos = encode_pos(pos)
                                run = pos not in db
                                c.writer.write(mp.packb(run))
                                await c.writer.drain()
                            case (1, pos, data):
                                pos = encode_pos(pos)
                                total_annotations += 1
                                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - {pos} - Get One. In total {total_annotations}  are collected.")
                                db[pos] = data
                                db.commit()
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

                await c.run_app("Pretrain_Extraction2")
                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {c.client_id} - annotating {rpath}")
                c.writer.write(mp.packb((path, pp_names)))
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
