#!/bin/env python3
import json
import logging
import sys
import time
from data.isabelle import AFP_Data, CaseNotAvailable, PISA_Data, get_data_class
from transformers import AutoTokenizer
import multiprocessing
from concurrent.futures import ProcessPoolExecutor
from IsaREPL import Client
import os

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(processName)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout)
    ]
)

def gen_data(proof_lang, result_path, model_name, partNum, totalNum, data_source, token_limit, include_proof=True, process=lambda x: x):
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
                if isinstance(idx, int):
                    idx2 = idx
                else:
                    idx2 = str(idx)
                ctxt = data.context_of(idx)
                if ctxt is None:
                    logging.error(f"missing context: {idx}")
                    continue
                local_facts = {}
                for name, fact in ctxt.local_facts.items():
                    if name in ['<unnamed>']:
                        continue
                    if name.startswith('local.'):
                        name = name[6:]
                    match len(fact):
                        case 0:
                            pass
                        case 1:
                            local_facts[name] = fact[0]
                        case _:
                            for i, afact in enumerate(fact):
                                local_facts[f"{name}({i+1})"] = afact
                ret = {
                    'goals': [process(goal) for goal in ctxt.goals],
                    'vars': {k: process(v) for k,v in ctxt.fixes[0].items()},
                    'local_facts': {k: process(v) for k,v in local_facts.items()}
                }
                toks = sum(length_of(tok) + 2 for tok in ret['goals']) +\
                       sum(length_of(name) + length_of(typ) + 2 for name, typ in ret['vars'].items()) +\
                       sum(length_of(name) + length_of(fact) + 2 for name, fact in ret['local_facts'].items())
                if include_proof:
                    proof = process(data.proof_of(idx, proof_lang, comments=False, camlize=False).strip())
                    ret['proof'] = proof
                    toks += length_of(proof) + 2
                count += 1
                if toks > token_limit:
                    dropped += 1
                    logging.error(f"drop {idx} because proof is too long ({toks}). Total dropped: {dropped / count * 100:.2f}%")
                premises = {}
                all_premises = data.premise_of(idx, method='SH-final-goal', pp='pretty')
                if all_premises is None:
                    logging.error(f"missing premises: {idx}")
                    continue
                for name, fact in all_premises.items():
                    length = length_of(name) + length_of(fact) + 2
                    if length + toks > token_limit:
                        break
                    premises[name] = process(fact)
                    toks += length
                ret['premises'] = premises
                ret['index'] = idx
                if length_of(encode_prompt(ret)) > token_limit:
                    logging.error(f"drop {idx} because prompt is too long. Total dropped: {dropped / count * 100:.2f}%")
                    continue
                f.write(json.dumps(ret) + '\n')
                if count % 100 == 0:
                    logging.info(f"Generated {count / len(all_cases) * 100:.2f}% fine-tune cases in {result_path}, ETA: {((time.time() - time_start) / count * (len(all_cases) - count)) / 60:.2f} minutes")
            except CaseNotAvailable:
                pass
    print(f"Generated {count} fine-tune cases in {result_path}")

def encode_prompt(req):
    premises = '\n'.join(f"{name} : {prop}" for name, prop in req['premises'].items())
    vars = '\n'.join(f"{name} : {typ}" for name, typ in req['vars'].items())
    facts = '\n'.join(f"{name} : {fact}" for name, fact in req['local_facts'].items())
    goals = '\n'.join(f"{i+1}. {prop}" for i, prop in enumerate(req['goals']))
    prompt = f"LEMMAS:\n{premises}\n-----\nVARIABLES:\n{vars}\n\nFACTS:\n{facts}\n\nGOALS:\n{goals}"
    if 'proof' in req:
        prompt += f"\n\nPROOF:\n{req['proof']}"
    return prompt

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage:")
        print("  python gen_fine_tune_data.py proof_lang result_path model_name parallelNum token_limit [data_source] [include_proof]")
        print("")
        print("Arguments:")
        print("  proof_lang       Proof language format")
        print("  result_path      Base path for result files (will be suffixed with partition number)")
        print("  model_name       Name of the model for tokenization")
        print("  parallelNum      Number of parallel processes to run")
        print("  token_limit      Maximum number of tokens in the input")
        print("  data_source      Data source to use: 'afp' or 'pisa' (default: 'afp')")
        print("  include_proof    Whether to include proofs in output: 'true' or 'false' (default: 'true')")
        exit(1)
    
    if len(sys.argv) < 6:
        print("Error: Not enough arguments for fine-tune-data command")
        print("Usage: python gen_fine_tune_data.py proof_lang result_path model_name parallelNum token_limit [data_source] [include_proof]")
        exit(1)
    
    proof_lang = sys.argv[1]
    result_path = sys.argv[2]
    model_name = sys.argv[3]
    try:
        parallelNum = int(sys.argv[4])
        if parallelNum <= 0:
            raise ValueError("parallelNum must be a positive integer")
    except ValueError as e:
        print(f"Error: {str(e)}")
        exit(1)
    
    # Get data source (default to 'afp' if not provided)
    token_limit = int(sys.argv[5])
    data_source = sys.argv[6] if len(sys.argv) > 6 else 'afp'
    if data_source.lower() not in ['afp', 'pisa']:
        print(f"Warning: Invalid data source '{data_source}'. Using 'afp' as default.")
        data_source = 'afp'
    
    # Get include_proof option (default to 'true' if not provided)
    include_proof = True
    if len(sys.argv) > 7:
        if sys.argv[7].lower() in ['no_proof', 'false', 'f', 'no', 'n', '0']:
            include_proof = False
        elif sys.argv[7].lower() not in ['include_proof', 'true', 't', 'yes', 'y', '1']:
            print(f"Warning: Invalid include_proof value '{sys.argv[7]}'. Using 'true' as default.")
    
    # Limit the number of concurrent processes to avoid overloading the system
    max_concurrent = min(parallelNum, multiprocessing.cpu_count())
    logging.info(f"Starting {parallelNum} processes with maximum {max_concurrent} concurrent processes using {data_source.upper()}_Data" +
                 (", including proofs" if include_proof else ", excluding proofs"))
    
    # Create and execute processes using ProcessPoolExecutor to limit concurrency
    with ProcessPoolExecutor(max_workers=max_concurrent) as executor:
        futures = []
        for partNum in range(parallelNum):
            future = executor.submit(
                gen_data,
                proof_lang, result_path, model_name, partNum, parallelNum, data_source, token_limit, include_proof, Client.pretty_unicode
            )
            futures.append(future)
            logging.info(f"Scheduled process {partNum+1}/{parallelNum}")
        
        # Wait for all processes to complete
        for i, future in enumerate(futures):
            #try:
                future.result()  # This will re-raise any exceptions from the process
                logging.info(f"Process {i+1}/{parallelNum} completed successfully")
            #except Exception as e:
            #    logging.error(f"Process {i+1}/{parallelNum} failed with error: {str(e)}")
    
    logging.info("All processes completed. Merging results...")

    # Merge all partition files into a single result file
    merged_file_path = f"{result_path}.jsonl"
    logging.info(f"Merging partition files into {merged_file_path}")
    
    with open(merged_file_path, 'w', encoding='utf-8') as merged_file:
        total_examples = 0
        for partNum in range(parallelNum):
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

    exit()
