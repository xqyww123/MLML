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
import asyncio
import time

configure_logging(level=logging.INFO)

pos = load_ISAR_PROOF_INDEX()
counter = 0

async def main():
    global counter

    with SqliteDict('./cache/SH.pretty.db') as db:
        pre_total = len(pos)
        complete_indexes = set()
        for j, (key, val) in enumerate(db.items()):
            if j % 1000 == 0:
                logging.info(f"Checking [{j}/{pre_total}] records...")
            if isinstance(val, int) or len(val) <= 10:
                continue
            complete_indexes.add(key)

        task_queue = asyncio.Queue()
        the_chunk = []
        last_file = None
        total = 0
        for spec_pos, proof_pos in sorted(pos.items()):
            if last_file != spec_pos.file:
                if last_file is not None:
                    task_queue.put_nowait(the_chunk)
                the_chunk = []
                last_file = spec_pos.file
            key = f'{spec_pos.file}:{spec_pos.line}'
            if key in complete_indexes:
                continue
            total += 1
            the_chunk.append((spec_pos, proof_pos))
        if last_file is not None:
            task_queue.put_nowait(the_chunk)
        logging.info(f"{total} tasks in total.")

        async def worker(addr):
            global counter
            while True:
                async with Client(addr, 'HOL') as c:
                    while True:
                        try:
                            chunk = task_queue.get_nowait()
                        except asyncio.QueueEmpty:
                            return
                        for spec_pos, proof_pos in chunk:
                            counter += 1
                            if counter % 1000 == 0:
                                await c.clean_cache()
                            try:
                                key = f'{spec_pos.file}:{spec_pos.line}'
                                if key in db and len(db[key]) > 10:
                                    continue
                                try:
                                    file = os.path.abspath(proof_pos.file)
                                    await c.file(file, line=proof_pos.line, column=proof_pos.column, cache_position=True, use_cache=True)
                                except REPLFail as e:
                                    logging.error(f"Error loading file {proof_pos.file}: {e}")
                                    continue
                                res = await c.premise_selection('final', 1000, ['mesh'], {}, 'pretty')
                                db[key] = res
                                db.commit()
                                logging.info(f"[{counter}/{total}] obtained {len(res)} for {proof_pos}")
                            except Exception as e:
                                logging.error(f"Error: {e}")
                                await asyncio.sleep(1)
                                break

        servers = ['127.0.0.1:6666'] * 24
        await asyncio.gather(*(worker(server) for server in servers))

        db.commit()
        db.close()

    logging.info('Done')

asyncio.run(main())
