#!/usr/bin/env python3
# Positions of statements, proofs, and ends of proofs

import logging
from tools.logger import configure_logging
from tools.server import SERVERS, launch_servers
from sqlitedict import SqliteDict
import os
import asyncio
import time
from IsaREPL import Client, REPLFail
from tools.server import test_server
import traceback

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
    #print(pos)
    return f'{norm_file(pos[3][1])}:{pos[0]}:{pos[1]}'

async def extract():
    total_theories = 0
    finished_theories = 0

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

    with SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/basic_info.db') as db:
        async def process_one(server, rpath):
            nonlocal finished_theories
            path=os.path.abspath(rpath)
            rpath=norm_file(path)
            if rpath in db:
                logger.info(f"skipped {rpath}")
                return
            async with Client(server, 'HOL', timeout=None) as client:
                await client.set_register_thy(False)
                with open(path, 'r') as file:
                    src = file.read()
                directory = os.path.dirname(path)
                logger.info(f"[{finished_theories/total_theories*100:.2f}%] - {server} {client.client_id} - evaluating {rpath}")
                session = await client.session_name_of(path)
                await client.set_thy_qualifier(session)
                eval_info = await client.eval(src, import_dir=directory, base_dir=directory)
                tr_pos1 = await client.translate_position(src)
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

                reentry = False
                try:
                    for _ in range(5):
                        try:
                            await process_one(server, task)
                            finished_theories += 1
                            break
                        except ConnectionError:
                            logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Connection error in extraction {task}")
                            await asyncio.sleep(180)
                        except Exception as e:
                            traceback.print_exc()
                            logger.error(f"[{finished_theories/total_theories*100:.2f}%] - {server} - Error extracting {task}: {e}")
                finally:
                    task_queue.task_done()
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
