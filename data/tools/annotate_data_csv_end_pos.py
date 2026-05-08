from IsaREPL import Client, Position
import csv
from data.isabelle import MLML_BASE
from sqlitedict import SqliteDict
import asyncio
import os

async def preprocess_PISA2(addr, num_workers=4):
    csv_file_path = f"{MLML_BASE}/data/pisa_test.csv"
    DATA = []
    EVAL_CACHE = {}
    NUM = 0

    # Read all rows first
    rows = []
    with open(csv_file_path, 'r', encoding='utf-8') as csvfile:
        csv_reader = csv.reader(csvfile)
        next(csv_reader)  # Skip the header
        rows = list(csv_reader)

    # Open cache once for all workers
    cache = SqliteDict(f"{MLML_BASE}/cache/pisa_test.sqlite")

    async def process_row(row):
        nonlocal NUM
        async with Client(addr, 'HOL') as client:
            await client.set_register_thy(False)
            index, pos_spec, pos_proof, statement = row
            pos_spec2 = Position.from_s(pos_spec)
            pos_proof2 = Position.from_s(pos_proof)

            # Check cache
            eval_info = None
            pos_tr = None
            if pos_spec2.file in EVAL_CACHE:
                (eval_info, pos_tr) = EVAL_CACHE[pos_spec2.file]

            if eval_info is None:
                # Check SQLite cache
                if pos_spec2.file in cache:
                    eval_info = cache[pos_spec2.file]

                if eval_info is not None:
                    # Need to get pos_tr
                    with open(pos_spec2.file, 'r', encoding='utf-8') as file:
                        src = file.read()
                    pos_tr = await client.translate_position(src)
                    # Cache it
                    EVAL_CACHE[pos_spec2.file] = (eval_info, pos_tr)
                else:
                    # Need to eval
                    with open(pos_spec2.file, 'r', encoding='utf-8') as file:
                        src = file.read()
                    if pos_spec2.file == "./contrib/afp-2025-02-12/thys/Circus/Denotational_Semantics.thy":
                        pass
                    dir_of_spec = '/home/qiyuan.xu/MLML/' + os.path.dirname(pos_spec2.file)
                    file_name = '/home/qiyuan.xu/MLML/' + pos_spec2.file
                    session = await client.session_name_of(file_name)
                    await client.set_thy_qualifier(session)
                    eval_info = await client.eval(src, import_dir=dir_of_spec)
                    pos_tr = await client.translate_position(src)

                    # Cache it
                    EVAL_CACHE[pos_spec2.file] = (eval_info, pos_tr)
                    cache[pos_spec2.file] = eval_info
                    cache.commit()

            # Process eval_info to find END_POS
            # At this point, eval_info and pos_tr should both be not None
            assert eval_info is not None and pos_tr is not None, "eval_info and pos_tr should not be None"
            START = False
            END_POS = None
            for cmd_info in eval_info:
                begin_pos, end_pos = cmd_info.range
                begin_pos = pos_tr(begin_pos)  # type: ignore
                if begin_pos.line == pos_proof2.line and begin_pos.column == pos_proof2.column:  # type: ignore
                    START = True
                if START:
                    if cmd_info.flags.is_theory:
                        END_POS = pos_tr(end_pos)  # type: ignore
                        END_POS.file = pos_spec2.file  # type: ignore
                        break

            if END_POS is None:
                raise ValueError(f"PISA {index}: Cannot find the end position of the proof")

            NUM += 1
            print(f"Processing PISA {NUM}")

            DATA.append((int(index), pos_spec, pos_proof, END_POS, statement))

            return (int(index), pos_spec, pos_proof, END_POS, statement)

    # Process rows concurrently using asyncio semaphore to limit concurrency
    sem = asyncio.Semaphore(num_workers)

    async def limited_process(row):
        async with sem:
            return await process_row(row)

    results = await asyncio.gather(
        *(limited_process(row) for row in rows),
        return_exceptions=True
    )

    for row, result in zip(rows, results):
        if isinstance(result, Exception):
            print(f"Error processing row: {row}")
            print(f"Exception: {result}")
            raise result

    cache.close()

    # Sort by index to maintain original order
    DATA.sort(key=lambda x: x[0])

    with open(csv_file_path, 'w', encoding='utf-8') as csvfile:
        csv_writer = csv.writer(csvfile)
        csv_writer.writerow(['Index', 'Position_spec', 'Position_proof', 'Position_end', 'Statement'])
        for index, pos_spec, pos_proof, END_POS, statement in DATA:
            csv_writer.writerow([index, pos_spec, pos_proof, END_POS, statement])

asyncio.run(preprocess_PISA2("127.0.0.1:6622", 30))
exit()
