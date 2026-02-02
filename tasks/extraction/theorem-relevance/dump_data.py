#! /usr/bin/env python3
from sqlitedict import SqliteDict
from IsaREPL import Client
import json
import argparse
import random
from transformers import AutoTokenizer
import multiprocessing
from concurrent.futures import ProcessPoolExecutor, as_completed
import os
import tempfile
import shutil
import traceback
import time
from datetime import datetime, timedelta
import msgpack
import glob
import re

# Tokenizer will be initialized in each worker process

TOKEN_LIMIT = 7997

def post_process(s):
    s = re.sub(r'::type\b', '', s)
    s = re.sub(r'__\b', '', s)
    s = re.sub(r'‹', '\"', s)
    s = re.sub(r'›', '\"', s)
    return s

def process_batch(batch_info):
    """Process a batch of data from a chunk file.
    
    Args:
        batch_info: tuple of (batch_id, chunk_file_path, use_ctxt, use_ac, use_unicode,
                             thm_db_path, temp_dir)
    
    Returns:
        tuple of (batch_id, temp_file_path, num_processed, num_entries)
    """
    batch_id, chunk_file_path, use_ctxt, use_ac, use_unicode, thm_db_path, temp_dir = batch_info
    
    # Initialize tokenizer in this process
    tokenizer = AutoTokenizer.from_pretrained("deepseek-ai/DeepSeek-Prover-V1.5-Base", use_fast=True)
    
    # Define pretty_unicode function based on use_unicode flag
    def pretty_unicode(s):
        if use_unicode:
            return Client.pretty_unicode(s)
        return s
    
    def encode_goal(goal, goal_vars):
        premises, concl = goal
        goal = "###Variables\n" + "".join([gv + "\n\n" for gv in goal_vars])\
             + "###Premises\n" + "".join([premise + "\n\n" for premise in premises])\
             + "###Conclusion\n" + concl
        if goal.count("###Premises") > 1 or goal.count("###Conclusion") > 1:
            print(f"[Batch {batch_id}] Warning: Found multiple occurrences of ###Premises or ###Conclusion in goal")
            # Don't exit in worker process, just continue
        return goal
    
    def count_tokens(text):
        tokens = tokenizer.encode(text, add_special_tokens=False)
        return len(tokens)
    
    def shrink_tokens(existing, for_goal):
        if not isinstance(existing, str):
            existing = str(existing)
        tok_count = count_tokens(existing)
        if tok_count > TOKEN_LIMIT:
            if not for_goal:
                raise ValueError(f"tok_count {tok_count} is greater than TOKEN_LIMIT {TOKEN_LIMIT}")
            lines = existing.split('\n')
            ret_lines = []
            for i,line in enumerate(lines):
                if line.startswith('###'):
                    ret_lines.append(line)
                    continue
                if not line:
                    ret_lines.append(line)
                    continue
                tok_count -= count_tokens(line)
                if tok_count <= TOKEN_LIMIT:
                    if len(lines) <= 0:
                        raise ValueError(f"tok_count {tok_count} is greater than TOKEN_LIMIT {TOKEN_LIMIT}")
                    ret_lines.extend(lines[i+1:])
                    # if count_tokens("".join(ret_lines)) > TOKEN_LIMIT:
                    #     raise ValueError(f"DDDD tok_count {count_tokens(''.join(ret_lines))} is greater than TOKEN_LIMIT {TOKEN_LIMIT} {for_goal}")
                    return "\n".join(ret_lines)
            raise ValueError(f"tok_count {tok_count} is greater than TOKEN_LIMIT {TOKEN_LIMIT}")
        return existing
    def trim_context(existing : str, ctxt, for_goal):
        tok_count = count_tokens(existing)
        if tok_count == TOKEN_LIMIT:
            return existing
        if tok_count > TOKEN_LIMIT:
            return shrink_tokens(existing, for_goal)

        ret = []
        segs = ctxt.split('\n\n\n')
        for seg in segs:
            if not seg:
                continue
            if not for_goal and seg.startswith('theory '):
                continue
            if tok_count >= TOKEN_LIMIT:
                break
            seg = seg + "\n\n"
            cnt = count_tokens(seg)
            if tok_count + cnt > TOKEN_LIMIT:
                break
            ret.append(seg)
            tok_count += cnt
        def m(cmd : str) -> int:
            if cmd.startswith('theory '):
                return -1
            elif cmd.startswith('notation '):
                return 0
            elif cmd.startswith('class '):
                return 1
            elif cmd.startswith('fact '):
                return 3
            else:
                return 2
        k_ret = [(m(cmd), cmd) for cmd in ret]
        k_ret.sort(key=lambda x: x[0])
        ret = [cmd for _, cmd in k_ret]
        # if count_tokens("".join(ret)) > TOKEN_LIMIT:
        #     raise ValueError(f"AAAAAAAAAAAA tok_count {count_tokens(''.join(ret))} is greater than TOKEN_LIMIT {TOKEN_LIMIT}")
        return "".join(ret) + existing
    
    # Create temporary output file for this batch
    temp_file = os.path.join(temp_dir, f'batch_{batch_id}.jsonl')
    
    # Open thm_db for this process
    thm_db = SqliteDict(thm_db_path)
    _CACHE = {}
    err_num = 0
    total_num = 0
    
    def get_premise(premise):
        nonlocal err_num, total_num
        if premise in _CACHE:
            return _CACHE[premise]
        else:
            try:
                pctxt, prem_acs, norm_prem, vars, _ = thm_db[premise]
                _CACHE[premise] = (pctxt, prem_acs, norm_prem, vars)
                total_num += 1
                return (pctxt, prem_acs, norm_prem, vars)
            except KeyError:
                err_num += 1
                print(f"\033[91m[Batch {batch_id}] Error {err_num}/{total_num}: {premise}\033[0m")
                # Cache the missing premise result to avoid repeated errors
                missing_result = ("", [], "", [])
                _CACHE[premise] = missing_result
                return missing_result
    
    num_processed = 0
    num_entries = 0
    
    with open(temp_file, 'w', buffering=8192) as output:
        def gen_goal(goal, ctxt, goal_vars):
            goal = encode_goal(goal, goal_vars)
            goal = pretty_unicode(goal)
            goal = post_process(goal)
            if use_ctxt and ctxt:
                goal = trim_context(goal, ctxt, True)
            else:
                goal = shrink_tokens(goal, True)
            goal = "#Goal\n" + goal
            num = count_tokens(goal)
            if num > TOKEN_LIMIT + 3:
                raise ValueError(f"BBBB Goal has {num} tokens, which is greater than TOKEN_LIMIT {TOKEN_LIMIT} {bool(use_ctxt and ctxt)}")
            return goal
        def gen_premise(premise, pctxt, prem_vars):
            premise = "###Variables\n" + "".join([pv + "\n\n" for pv in prem_vars])\
                    + "###Statement\n" + premise
            premise = pretty_unicode(premise)
            premise = post_process(premise)
            if use_ctxt and pctxt:
                premise = trim_context(premise, pctxt, False)
            else:
                premise = shrink_tokens(premise, False)
            premise = "#Fact\n" + premise
            num = count_tokens(premise)
            if num > TOKEN_LIMIT + 3:
                raise ValueError(f"CCCC Goal has {num} tokens, which is greater than TOKEN_LIMIT {TOKEN_LIMIT}")
            return premise
        def write_entry(goal, premise):
            nonlocal num_entries
            num_entries += 1
            output.write(json.dumps((goal, premise)) + "\n")
        
        # Read chunk file
        with open(chunk_file_path, 'rb') as f:
            chunk_data = msgpack.unpackb(f.read())
        
        batch_total = len(chunk_data)
        batch_start_time = time.time()
        last_progress_time = batch_start_time
        
        # Process each item in the chunk
        # chunk_data is a list of (goal_str, (goal, ctxt, prem_list, goal_acs))
        for goal_str, (goal, ctxt, prem_list, goal_acs, goal_norm, goal_vars) in chunk_data:
            num_processed += 1
            ctxt = pretty_unicode(ctxt)
            ctxt = post_process(ctxt)
            
            # Print progress every 100 items or every 5 seconds
            current_time = time.time()
            if num_processed % 100 == 0 or (current_time - last_progress_time) >= 5.0:
                elapsed = current_time - batch_start_time
                if num_processed > 0:
                    rate = num_processed / elapsed if elapsed > 0 else 0
                    eta = (batch_total - num_processed) / rate if rate > 0 else 0
                    print(f"[Batch {batch_id}] Progress: {num_processed}/{batch_total} items "
                          f"({num_processed*100//batch_total if batch_total > 0 else 0}%), "
                          f"{num_entries} entries, {rate:.1f} items/s, ETA: {eta:.1f}s")
                last_progress_time = current_time
            
            # Note: PISA files filtering is already done in dedup.py, so we don't need to filter here
            try:
                if use_ac == -1:
                    goal_str = gen_goal(goal_norm, ctxt, goal_vars)
                else:
                    goal_str = gen_goal(goal, ctxt, goal_vars)
            except ValueError as e:
                print(f"\033[91m[Batch {batch_id}] Error {err_num}/{total_num}: {e}\033[0m")
                continue
            for prem in prem_list:
                pctxt, prem_acs, norm_prem, prem_vars = get_premise(prem)
                pctxt = pretty_unicode(pctxt)
                pctxt = post_process(pctxt)
                try:
                    if use_ac == -1:
                        prem_str = gen_premise(norm_prem, pctxt, prem_vars)
                    else:
                        prem_str = gen_premise(prem, pctxt, prem_vars)
                    write_entry(goal_str, prem_str)
                except ValueError as e:
                    print(f"\033[91m[Batch {batch_id}] Error {err_num}/{total_num}: {e}\033[0m")
                    continue
                if use_ac > 0:
                    N = len(goal_acs) + 1
                    M = 1 # len(prem_acs) + 1
                    
                    if N == 1 and M == 1:
                        continue
                    
                    max_pairs = min(use_ac, N * M - 1)
                    
                    if max_pairs == N * M - 1:
                        selected_pairs = [(i, j) for i in range(N) for j in range(M) if not (i == N-1 and j == M-1)]
                    elif N * M - 1 <= use_ac * 10:
                        all_pairs = [(i, j) for i in range(N) for j in range(M) if not (i == N-1 and j == M-1)]
                        selected_pairs = random.sample(all_pairs, max_pairs)
                    else:
                        selected_pairs = set()
                        while len(selected_pairs) < max_pairs:
                            i = random.randrange(N)
                            j = random.randrange(M)
                            if i == N-1 and j == M-1:
                                continue
                            selected_pairs.add((i, j))
                        selected_pairs = list(selected_pairs)
                    
                    for i, j in selected_pairs:
                        if i == N-1 and j == M-1:
                            raise ValueError("i == N-1 and j == M-1")
                        aug_goal = goal if i == N-1 else goal_acs[i]
                        aug_prem = prem if j == M-1 else prem_acs[j]
                        try:
                            aug_goal_str = gen_goal(aug_goal, ctxt, goal_vars)
                            aug_prem_str = gen_premise(aug_prem, pctxt, prem_vars)
                            write_entry(aug_goal_str, aug_prem_str)
                        except ValueError as e:
                            print(f"\033[91m[Batch {batch_id}] Error {err_num}/{total_num}: {e}\033[0m")
                            continue
    
    thm_db.close()
    
    return (batch_id, temp_file, num_processed, num_entries)
        




if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Dump data from deduplicated chunks')
    parser.add_argument('result_file', help='Output JSONL file path')
    parser.add_argument('--chunks-dir', required=True,
                        help='Directory containing chunk files (output from dedup.py)')
    parser.add_argument('--use-ctxt', action='store_true', help='Include context in output')
    parser.add_argument('--use-ac', type=int, nargs='?', const=1, default=0, metavar='N',
                        help='Include AC (set N to 0 to disable). N is the maximal number of augmented versions of each goal-premise pair')
    parser.add_argument('--unicode', action='store_true', help='Enable Client.pretty_unicode for unicode formatting')
    parser.add_argument('--num-workers', type=int, default=None, 
                        help='Number of worker processes (default: CPU count)')
    parser.add_argument('--thm-db-path', type=str,
                        default='/home/qiyuan/Current/MLML/data/premise_info.db',
                        help='Path to premise_info.db (default: /home/qiyuan/Current/MLML/data/premise_info.db)')
    
    args = parser.parse_args()
    
    USE_CTXT = args.use_ctxt
    USE_AC = args.use_ac
    USE_UNICODE = args.unicode
    result_file = args.result_file
    CHUNKS_DIR = args.chunks_dir
    NUM_WORKERS = args.num_workers if args.num_workers else multiprocessing.cpu_count()
    
    # Database path (only for thm_db)
    THM_DB_PATH = args.thm_db_path
    
    # Find all chunk files in the chunks directory
    print(f"Scanning chunks directory: {CHUNKS_DIR}")
    chunk_files = sorted(glob.glob(os.path.join(CHUNKS_DIR, 'chunk.*')))
    
    if not chunk_files:
        raise ValueError(f"No chunk files found in {CHUNKS_DIR}. Make sure you have run dedup.py first.")
    
    # Check for duplicate files (shouldn't happen with glob, but safety check)
    chunk_files_set = set(chunk_files)
    if len(chunk_files_set) != len(chunk_files):
        duplicates = [f for f in chunk_files if chunk_files.count(f) > 1]
        raise ValueError(f"Found duplicate chunk files: {duplicates}")
    
    print(f"Found {len(chunk_files)} chunk files")
    print(f"Using {NUM_WORKERS} worker processes")
    
    # Create batches: assign chunk files to batches
    # Each batch will process one or more chunk files
    batches = []
    seen_batch_ids = set()
    for batch_id, chunk_file in enumerate(chunk_files):
        if batch_id in seen_batch_ids:
            raise ValueError(f"Duplicate batch_id detected: {batch_id}")
        seen_batch_ids.add(batch_id)
        batches.append((batch_id, chunk_file))
    
    print(f"Created {len(batches)} batches (one chunk file per batch)")
    
    # Create temporary directory for batch output files in the same directory as output file
    result_dir = os.path.dirname(os.path.abspath(result_file))
    result_basename = os.path.basename(result_file)
    # Create a temp directory name based on the output filename
    temp_dir_name = result_basename + '.tmp'
    temp_dir = os.path.join(result_dir, temp_dir_name)
    
    # Create the temporary directory
    os.makedirs(temp_dir, exist_ok=True)
    print(f"Temporary files will be stored in: {temp_dir}")
    
    # Flag to track if processing completed successfully
    processing_completed = False
    
    try:
        # Prepare batch info for workers
        batch_infos = [
            (bid, chunk_file, USE_CTXT, USE_AC, USE_UNICODE, THM_DB_PATH, temp_dir)
            for bid, chunk_file in batches
        ]
        
        # Process batches in parallel
        total_processed = 0
        total_entries = 0
        completed_batches = {}
        total_batches = len(batch_infos)
        start_time = time.time()
        
        print(f"\n{'='*60}")
        print(f"Starting processing at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"Total batches: {total_batches}")
        print(f"{'='*60}\n")
        
        with ProcessPoolExecutor(max_workers=NUM_WORKERS) as executor:
            # Submit all batches and verify no duplicates
            submitted_batch_ids = set()
            future_to_batch = {}
            for info in batch_infos:
                bid = info[0]
                if bid in submitted_batch_ids:
                    raise ValueError(f"Duplicate batch_id {bid} detected in batch_infos! This should not happen.")
                submitted_batch_ids.add(bid)
                future = executor.submit(process_batch, info)
                future_to_batch[future] = bid
            
            if len(submitted_batch_ids) != len(batch_infos):
                raise ValueError(f"Mismatch: submitted {len(submitted_batch_ids)} batches but have {len(batch_infos)} batch_infos")
            
            print(f"Submitted {len(submitted_batch_ids)} unique batches for processing")
            
            # Process completed batches
            processed_batch_ids = set()
            for future in as_completed(future_to_batch):
                batch_id = future_to_batch[future]
                try:
                    bid, temp_file, num_processed, num_entries = future.result()
                    
                    # Verify batch_id matches returned bid
                    if bid != batch_id:
                        raise ValueError(f"Batch ID mismatch: expected {batch_id} but got {bid} from result")
                    
                    # Check for duplicate completion
                    if bid in processed_batch_ids:
                        raise ValueError(f"Batch {bid} completed multiple times! This indicates a serious bug.")
                    
                    processed_batch_ids.add(bid)
                    completed_batches[bid] = temp_file
                    total_processed += num_processed
                    total_entries += num_entries
                    
                    # Calculate progress
                    completed_count = len(completed_batches)
                    progress_pct = completed_count * 100 // total_batches if total_batches > 0 else 0
                    elapsed_time = time.time() - start_time
                    
                    # Calculate ETA
                    if completed_count > 0:
                        avg_time_per_batch = elapsed_time / completed_count
                        remaining_batches = total_batches - completed_count
                        eta_seconds = avg_time_per_batch * remaining_batches
                        eta_str = str(timedelta(seconds=int(eta_seconds)))
                    else:
                        eta_str = "calculating..."
                    
                    print(f"[{datetime.now().strftime('%H:%M:%S')}] "
                          f"Batch {bid}/{total_batches-1} completed "
                          f"({progress_pct}% overall): "
                          f"{num_processed} goals, {num_entries} entries | "
                          f"Total: {total_processed} goals, {total_entries} entries | "
                          f"ETA: {eta_str}")
                    
                except Exception as exc:
                    print(f"\n[ERROR] Batch {batch_id} generated an exception:")
                    print(traceback.format_exc())
                    raise
        
        # Verify all batches were processed exactly once
        if len(processed_batch_ids) != total_batches:
            missing = set(range(total_batches)) - processed_batch_ids
            raise ValueError(f"Not all batches were processed! Expected {total_batches}, got {len(processed_batch_ids)}. Missing: {missing}")
        
        if len(completed_batches) != total_batches:
            raise ValueError(f"Mismatch in completed_batches: expected {total_batches}, got {len(completed_batches)}")
        
        total_elapsed = time.time() - start_time
        total_time_str = str(timedelta(seconds=int(total_elapsed)))
        
        print(f"\n{'='*60}")
        print(f"All batches completed at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"Total time: {total_time_str}")
        print(f"Total goals processed: {total_processed:,}")
        print(f"Total entries generated: {total_entries:,}")
        if total_processed > 0:
            print(f"Average processing rate: {total_processed/total_elapsed:.1f} goals/s")
        print(f"Verified: All {total_batches} batches processed exactly once (no duplicates)")
        print(f"{'='*60}\n")
        
        # I disabled this. Instead, we run `cat embedding_ctxt_ac5_unicode.jsonl.tmp/batch_* | pv -l -i 1 | zstd > embedding_ctxt_ac5_unicode.jsonl.zst`
        
        # # Merge all temporary files into final output
        # merge_start_time = time.time()
        # print(f"Merging {len(completed_batches)} batch files into {result_file}...")
        # merged_count = 0
        # with open(result_file, 'w', buffering=8192*4) as output:
        #     for bid in sorted(completed_batches.keys()):
        #         temp_file = completed_batches[bid]
        #         try:
        #             with open(temp_file, 'r', buffering=8192) as f:
        #                 shutil.copyfileobj(f, output)
        #             os.remove(temp_file)  # Clean up temporary file
        #             merged_count += 1
        #             if merged_count % 10 == 0 or merged_count == len(completed_batches):
        #                 print(f"  Merged {merged_count}/{len(completed_batches)} files...")
        #         except Exception as e:
        #             print(f"  [WARNING] Failed to merge batch {bid}: {e}")
        
        # merge_time = time.time() - merge_start_time
        # print(f"Merging completed in {merge_time:.1f}s")
        # print(f"Output written to {result_file}")
        
        # # Print file size if available
        # try:
        #     file_size = os.path.getsize(result_file)
        #     file_size_mb = file_size / (1024 * 1024)
        #     print(f"Output file size: {file_size_mb:.2f} MB")
        # except OSError:
        #     pass
        
        # # Mark processing as completed successfully
        # processing_completed = True
        
    except KeyboardInterrupt:
        print(f"\n\n[INTERRUPTED] Processing interrupted by user.")
        print(f"Temporary files are preserved in: {temp_dir}")
        print(f"You can resume processing later or manually clean up the directory.")
        raise
    except Exception as e:
        print(f"\n\n[ERROR] Processing failed with error: {e}")
        print(f"Temporary files are preserved in: {temp_dir}")
        print(f"You can inspect the files or manually clean up the directory.")
        raise
    finally:
        pass
        # # Clean up temporary directory only if processing completed successfully
        # if processing_completed:
        #     try:
        #         if os.path.exists(temp_dir):
        #             # Remove all files in the directory first
        #             for filename in os.listdir(temp_dir):
        #                 file_path = os.path.join(temp_dir, filename)
        #                 try:
        #                     if os.path.isfile(file_path):
        #                         os.remove(file_path)
        #                 except OSError:
        #                     pass
        #             # Remove the directory itself
        #             try:
        #                 os.rmdir(temp_dir)
        #                 print(f"Cleaned up temporary directory: {temp_dir}")
        #             except OSError:
        #                 print(f"[WARNING] Could not remove temporary directory: {temp_dir}")
        #                 print(f"  You may need to manually remove it.")
        #     except Exception as e:
        #         print(f"[WARNING] Error during cleanup: {e}")
                    
