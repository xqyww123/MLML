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
import data.language as language
import pandas as pd  # For DataFrame handling
import pyarrow  # Required for pandas to write parquet files

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
    print(f"Checking data contamination for {len(pisa.all_cases())} PISA cases")
    for i in pisa.all_cases():
        pos = pisa.goal_pos_of(i)
        print(pos)
        if pos in afp.all_cases():
            print(f"Data contamination detected! {pos}")
            exit(1)
    print("no data contamination")

verify_contamination()


# tokenizer = AutoTokenizer.from_pretrained('EleutherAI/llemma_34b')
# a = is_codepoint_supported(tokenizer, '\<s>')
# x = mk_unicode_table('EleutherAI/llemma_34b')
# y = mk_unicode_table('deepseek-ai/DeepSeek-Prover-V1.5-Base')
# 
# exit(1)

# Generating Fine tuning data

def get_data_class(data_source):
    if data_source.lower() == "afp":
        return AFP_Data
    elif data_source.lower() == "pisa":
        return PISA_Data
    else:
        logging.error(f"Invalid data source: {data_source}. Using AFP_Data as default.")
        return AFP_Data

def convert_jsonl_to_parquet(jsonl_file_path, parquet_file_path):
    """
    Convert a JSONL file to Parquet format using Pandas.
    
    Args:
        jsonl_file_path: Path to the input JSONL file
        parquet_file_path: Path to the output Parquet file
    
    Returns:
        bool: True if conversion was successful, False otherwise
    """
    try:
        logging.info(f"Converting {jsonl_file_path} to Parquet format...")
        # Read the JSONL file line by line and create a list of dictionaries
        data = []
        with open(jsonl_file_path, 'r', encoding='utf-8') as f:
            for line in f:
                data.append(json.loads(line.strip()))
        
        # Convert to pandas DataFrame
        df = pd.DataFrame(data)
        
        # Write to Parquet format
        df.to_parquet(parquet_file_path, index=False)
        logging.info(f"Successfully converted to Parquet: {parquet_file_path}")
        return True
    except Exception as e:
        logging.error(f"Error converting to Parquet: {str(e)}")
        return False

def gen_data(proof_lang, result_path, model_name, partNum, totalNum, data_source, include_proof=True):
    DATA = get_data_class(data_source)
    data = DATA()
    count = 0
    dropped = 0
    result_path = f"{result_path}.{partNum}.jsonl"
    logging.info(f"Generating {result_path} using {data_source} data" + (" with proofs" if include_proof else " without proofs"))

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
                if include_proof:
                    proof = data.proof_of(idx, proof_lang, comments=False, camlize=False).strip()
                    goal = data.goal_of(idx).strip()
                    if length_of(proof) + length_of(goal) > 2000:
                        dropped += 1
                        if dropped % 100 == 0:
                            print(f"drop {idx} because proof is too long ({length_of(proof)}). Total dropped: {dropped / count * 100:.2f}%")
                        continue
                    prelude = data.prelude_of(idx, dep_depth=None, use_proofs=proof_lang, use_comments=False, length_of=length_of, maxsize=2000, camlize=False).strip()
                    f.write(json.dumps({'index': idx,
                                        'prelude': prelude,
                                        'goal': goal,
                                        'proof': proof}) + '\n')
                else:
                    goal = data.goal_of(idx).strip()
                    prelude = data.prelude_of(idx, dep_depth=None, use_proofs=proof_lang, use_comments=False, length_of=length_of, maxsize=2000, camlize=False).strip()
                    f.write(json.dumps({'index': idx,
                                        'prelude': prelude,
                                        'goal': goal}) + '\n')
                count += 1
                if count % 100 == 0:
                    logging.info(f"Generated {count / len(all_cases) * 100:.2f}% fine-tune cases in {result_path}, ETA: {((time.time() - time_start) / count * (len(all_cases) - count)) / 60:.2f} minutes")
            except CaseNotAvailable:
                pass
    print(f"Generated {count} fine-tune cases in {result_path}")

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage:")
        print("  python gen_fine_tune_data.py proof_lang result_path model_name totalNum [data_source] [include_proof] [to_parquet]")
        print("")
        print("Arguments:")
        print("  proof_lang       Proof language format")
        print("  result_path      Base path for result files (will be suffixed with partition number)")
        print("  model_name       Name of the model for tokenization")
        print("  totalNum         Number of partitions to create (and processes to run)")
        print("  data_source      Data source to use: 'afp' or 'pisa' (default: 'afp')")
        print("  include_proof    Whether to include proofs in output: 'true' or 'false' (default: 'true')")
        print("  to_parquet       Whether to convert final output to Parquet format: 'true' or 'false' (default: 'false')")
        exit(1)
    
    if len(sys.argv) < 5:
        print("Error: Not enough arguments for fine-tune-data command")
        print("Usage: python gen_fine_tune_data.py proof_lang result_path model_name totalNum [data_source] [include_proof] [to_parquet]")
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
    
    # Get data source (default to 'afp' if not provided)
    data_source = sys.argv[5] if len(sys.argv) > 5 else 'afp'
    if data_source.lower() not in ['afp', 'pisa']:
        print(f"Warning: Invalid data source '{data_source}'. Using 'afp' as default.")
        data_source = 'afp'
    
    # Get include_proof option (default to 'true' if not provided)
    include_proof = True
    if len(sys.argv) > 6:
        if sys.argv[6].lower() in ['no_proof', 'false', 'f', 'no', 'n', '0']:
            include_proof = False
        elif sys.argv[6].lower() not in ['include_proof', 'true', 't', 'yes', 'y', '1']:
            print(f"Warning: Invalid include_proof value '{sys.argv[6]}'. Using 'true' as default.")
    
    # Get to_parquet option (default to 'false' if not provided)
    to_parquet = False
    if len(sys.argv) > 7:
        if sys.argv[7].lower() in ['true', 't', 'yes', 'y', '1', 'to_parquet']:
            to_parquet = True
        elif sys.argv[7].lower() not in ['false', 'f', 'no', 'n', '0']:
            print(f"Warning: Invalid to_parquet value '{sys.argv[7]}'. Using 'false' as default.")
    
    # Limit the number of concurrent processes to avoid overloading the system
    max_concurrent = min(totalNum, multiprocessing.cpu_count())
    logging.info(f"Starting {totalNum} processes with maximum {max_concurrent} concurrent processes using {data_source.upper()}_Data" +
                 (", including proofs" if include_proof else ", excluding proofs"))
    
    # Create and execute processes using ProcessPoolExecutor to limit concurrency
    with ProcessPoolExecutor(max_workers=max_concurrent) as executor:
        futures = []
        for partNum in range(totalNum):
            future = executor.submit(
                gen_data,
                proof_lang, result_path, model_name, partNum, totalNum, data_source, include_proof
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
    
    DATA = get_data_class(data_source)
    data = DATA()
    all_cases = list(data.all_cases())
    logging.info(f"Merge complete. Total examples in {merged_file_path}: {total_examples}, {total_examples / len(all_cases) * 100:.2f}% of total")

    if to_parquet:
        logging.info("Converting final output to Parquet format...")
        convert_jsonl_to_parquet(merged_file_path, merged_file_path.replace('.jsonl', '.parquet'))
        logging.info("Conversion completed successfully")

    exit()
