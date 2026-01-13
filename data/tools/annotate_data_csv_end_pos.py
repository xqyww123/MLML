from IsaREPL import Client, Position
import csv
from data.isabelle import MLML_BASE
from sqlitedict import SqliteDict
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
import os

def preprocess_PISA2(addr, num_threads=4):
    csv_file_path = f"{MLML_BASE}/data/pisa_test.csv"
    DATA = []
    DATA_LOCK = threading.Lock()
    EVAL_CACHE = {}
    EVAL_CACHE_LOCK = threading.Lock()
    NUM = 0
    NUM_LOCK = threading.Lock()
    
    # Read all rows first
    rows = []
    with open(csv_file_path, 'r', encoding='utf-8') as csvfile:
        csv_reader = csv.reader(csvfile)
        next(csv_reader)  # Skip the header
        rows = list(csv_reader)
    
    # Open cache once for all threads
    cache = SqliteDict(f"{MLML_BASE}/cache/pisa_test.sqlite")
    
    def process_row(row):
        nonlocal NUM
        with Client(addr, 'HOL') as client:
            client.set_register_thy(False)
            index, pos_spec, pos_proof, statement = row
            pos_spec2 = Position.from_s(pos_spec)
            pos_proof2 = Position.from_s(pos_proof)
            
            # Check cache with lock
            eval_info = None
            pos_tr = None
            with EVAL_CACHE_LOCK:
                if pos_spec2.file in EVAL_CACHE:
                    (eval_info, pos_tr) = EVAL_CACHE[pos_spec2.file]
            
            if eval_info is None:
                # Check SQLite cache with lock
                if pos_spec2.file in cache:
                    eval_info = cache[pos_spec2.file]
                
                if eval_info is not None:
                    # Need to get pos_tr
                    with open(pos_spec2.file, 'r', encoding='utf-8') as file:
                        src = file.read()
                    pos_tr = client.translate_position(src)
                    # Cache it
                    with EVAL_CACHE_LOCK:
                        EVAL_CACHE[pos_spec2.file] = (eval_info, pos_tr)
                else:
                    # Need to eval
                    with open(pos_spec2.file, 'r', encoding='utf-8') as file:
                        src = file.read()
                    if pos_spec2.file == "./contrib/afp-2025-02-12/thys/Circus/Denotational_Semantics.thy":
                        pass
                    dir_of_spec = '/home/qiyuan.xu/MLML/' + os.path.dirname(pos_spec2.file)
                    file_name = '/home/qiyuan.xu/MLML/' + pos_spec2.file
                    session = client.session_name_of(file_name)
                    client.set_thy_qualifier(session)
                    eval_info = client.eval(src, import_dir=dir_of_spec)
                    pos_tr = client.translate_position(src)
                    
                    # Cache it
                    with EVAL_CACHE_LOCK:
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
            
            # Update counter and append result
            with NUM_LOCK:
                NUM += 1
                current_num = NUM
            print(f"Processing PISA {current_num}")
            
            with DATA_LOCK:
                DATA.append((int(index), pos_spec, pos_proof, END_POS, statement))
            
            return (int(index), pos_spec, pos_proof, END_POS, statement)
    
    # Process rows in parallel
    with ThreadPoolExecutor(max_workers=num_threads) as executor:
        # Create a mapping from future to row for error reporting
        future_to_row = {}
        for row in rows:
            future = executor.submit(process_row, row)
            future_to_row[future] = row
        
        for future in as_completed(future_to_row):
            try:
                future.result()
            except Exception as e:
                row = future_to_row[future]
                print(f"Error processing row: {row}")
                print(f"Exception: {e}")
                raise
    
    cache.close()
    
    # Sort by index to maintain original order
    DATA.sort(key=lambda x: x[0])

    with open(csv_file_path, 'w', encoding='utf-8') as csvfile:
        csv_writer = csv.writer(csvfile)
        csv_writer.writerow(['Index', 'Position_spec', 'Position_proof', 'Position_end', 'Statement'])
        for index, pos_spec, pos_proof, END_POS, statement in DATA:
            csv_writer.writerow([index, pos_spec, pos_proof, END_POS, statement])

preprocess_PISA2("127.0.0.1:6622", 30)
exit()