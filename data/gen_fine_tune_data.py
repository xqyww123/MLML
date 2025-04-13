#!/usr/bin/env python3

import os
import sys
import json
import logging
import time
from data.isabelle import AFP_Data, CaseNotAvailable, PISA_Data
from transformers import AutoTokenizer
import multiprocessing
from concurrent.futures import ProcessPoolExecutor
from data.isabelle import Position

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(processName)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout)
    ]
)

def verify_contamination():
    afp = AFP_Data()
    pisa = PISA_Data()
    for i in pisa.all_cases():
        pos = pisa.goal_pos_of(i)
        if pos in afp.all_cases():
            print(f"Data contamination detected! {pos}")
            exit(1)
    print("no data contamination")

verify_contamination()

# Generating Fine tuning data

DATA = AFP_Data

def gen_fine_tune_data_isar_SHstar(proof_lang, result_path, model_name, partNum, totalNum):
    data = DATA()
    count = 0
    dropped = 0
    result_path = f"{result_path}.{partNum}.jsonl"
    logging.info(f"Generating {result_path}")

    # Filter cases based on partNum and totalNum
    partNum = int(partNum)
    totalNum = int(totalNum)
    if partNum < 0 or partNum >= totalNum:
        raise ValueError(f"partNum must be between 0 and {totalNum-1}")
    
    # Convert to list to enable indexing
    all_cases = list(data.all_cases())
    # Calculate the start and end indices for this partition
    start_idx = (len(all_cases) * partNum) // totalNum
    end_idx = (len(all_cases) * (partNum + 1)) // totalNum
    # Get the subset of cases for this partition
    all_cases = all_cases[start_idx:end_idx]
    logging.info(f"Processing partition {partNum+1}/{totalNum} with {len(all_cases)} cases")

    time_start = time.time()

    tokenizer = AutoTokenizer.from_pretrained(model_name)
    def length_of(text):
        tokens = tokenizer.encode(text)
        return len(tokens) + 2

    with open(result_path, 'w', encoding='utf-8') as f:
        for idx in all_cases:
            try:
                proof = data.proof_of(idx, proof_lang, comments=False)
                goal = data.goal_of(idx)
                if length_of(proof) + length_of(goal) > 2000:
                    dropped += 1
                    print(f"drop {idx} because proof is too long ({length_of(proof)}). Total dropped: {dropped / count * 100:.2f}%")
                    continue
                prelude = data.prelude_of(idx, dep_depth=None, use_proofs=proof_lang, use_comments=False, length_of=length_of, maxsize=2000)
                f.write(json.dumps({'prelude': prelude,
                                    'goal': goal,
                                    'proof': proof}) + '\n')
                count += 1
                if count % 100 == 0:
                    logging.info(f"Generated {count / len(all_cases) * 100:.2f}% fine-tune cases in {result_path}, ETA: {((time.time() - time_start) / count * (len(all_cases) - count)) / 60:.2f} minutes")
            except CaseNotAvailable:
                pass
    print(f"Generated {count} fine-tune cases in {result_path}")

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage:")
        print("  python gen_fine_tune_data.py proof_lang result_path model_name totalNum")
        print("")
        print("Arguments:")
        print("  proof_lang       Proof language format")
        print("  result_path      Base path for result files (will be suffixed with partition number)")
        print("  model_name       Name of the model for tokenization")
        print("  totalNum         Number of partitions to create (and processes to run)")
        exit(1)
    
    if len(sys.argv) < 5:
        print("Error: Not enough arguments for fine-tune-data command")
        print("Usage: python gen_fine_tune_data.py fine-tune-data proof_lang result_path model_name totalNum")
        exit(1)
    
    proof_lang = sys.argv[1]
    result_path = sys.argv[2]
    model_name = sys.argv[3]
    try:
        totalNum = int(sys.argv[4])
        if totalNum <= 0:
            raise ValueError("totalNum must be a positive integer")
    except ValueError as e:
        print(f"Error: {str(e)}")
        exit(1)
    
    # Limit the number of concurrent processes to avoid overloading the system
    max_concurrent = min(totalNum, multiprocessing.cpu_count())
    logging.info(f"Starting {totalNum} processes with maximum {max_concurrent} concurrent processes")
    
    # Create and execute processes using ProcessPoolExecutor to limit concurrency
    with ProcessPoolExecutor(max_workers=max_concurrent) as executor:
        futures = []
        for partNum in range(totalNum):
            future = executor.submit(
                gen_fine_tune_data_isar_SHstar,
                proof_lang, result_path, model_name, partNum, totalNum
            )
            futures.append(future)
            logging.info(f"Scheduled process {partNum+1}/{totalNum}")
        
        # Wait for all processes to complete
        for i, future in enumerate(futures):
            try:
                future.result()  # This will re-raise any exceptions from the process
                logging.info(f"Process {i+1}/{totalNum} completed successfully")
            except Exception as e:
                logging.error(f"Process {i+1}/{totalNum} failed with error: {str(e)}")
    
    logging.info("All processes completed. Merging results...")

    # Merge all partition files into a single result file
    merged_file_path = f"{result_path}.jsonl"
    logging.info(f"Merging partition files into {merged_file_path}")
    
    with open(merged_file_path, 'w', encoding='utf-8') as merged_file:
        total_examples = 0
        for partNum in range(totalNum):
            partition_file_path = f"{result_path}.{partNum}.jsonl"
            try:
                with open(partition_file_path, 'r', encoding='utf-8') as part_file:
                    part_content = part_file.read()
                    if part_content:
                        merged_file.write(part_content)
                        # Count examples in this partition
                        examples_count = part_content.count('\n')
                        total_examples += examples_count
                        logging.info(f"Added {examples_count} examples from partition {partNum}")
                
                # Optionally remove the partition file after merging
                os.remove(partition_file_path)
                logging.info(f"Removed partition file {partition_file_path}")
            except FileNotFoundError:
                logging.warning(f"Partition file {partition_file_path} not found, skipping")
            except Exception as e:
                logging.error(f"Error processing partition {partNum}: {str(e)}")
    
    data = DATA()
    all_cases = list(data.all_cases())
    logging.info(f"Merge complete. Total examples in {merged_file_path}: {total_examples}, {total_examples / len(all_cases) * 100:.2f}% of total")
    exit()
