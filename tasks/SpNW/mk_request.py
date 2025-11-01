#!/usr/bin/env python3

import argparse
from IsaREPL import Client
import json
import os
import sys
import glob
import queue
import logging
import threading

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

TOKEN_LIMIT = 14000

def parse_args():
    parser = argparse.ArgumentParser(
        description="Identify unproven proof goals concluded by `sorry` in the source theory files and generate corresponding request.json that can be submitted to the LLM model using `inference.py`",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument(
        'source_files',
        nargs='+',
        metavar='isabelle_source.thy',
        help='One or more Isabelle source theory files (.thy)'
    )
    
    parser.add_argument(
        '-o', '--output',
        required=True,
        metavar='request.jsonl',
        help='Output JSON file path',
        default='request.jsonl'
    )

    parser.add_argument(
        '-c', '--address',
        required=False,
        metavar='address',
        help='ip_address:port of [Isabelle REPL](https://github.com/xqyww123/Isa-REPL), e.g., 127.0.0.1:6666',
        default='127.0.0.1:6666'
    )

    parser.add_argument(
        '-m', '--model',
        required=False,
        metavar='model',
        help='The model name of the LLM model, tpyically EleutherAI/llemma_7b or deepseek-ai/DeepSeek-Prover-V1.5-Base',
        default='reasonwang/deepseek-prover-SpNW-mini-16000'
    )

    return parser.parse_args()

from transformers import AutoTokenizer

def count_tokens(text, model_name):
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    
    tokens = tokenizer.encode(text)
    token_count = len(tokens)
    
    return token_count

def encode_prompt(req):
    premises = ''.join(f"{name} : {prop}\n" for name, prop in req['premises'].items())
    vars = ''.join(f"{name} : {typ}\n" for name, typ in req['vars'].items())
    facts = ''.join(f"{name} : {fact}\n" for name, fact in req['local_facts'].items())
    goals = ''.join(f"{i+1}. {prop}\n" for i, prop in enumerate(req['goals']))
    prompt = f"LEMMAS:\n{premises}\n-----\nVARIABLES:\n{vars}\nFACTS:\n{facts}\nGOALS:\n{goals}"
    if 'proof' in req:
        prompt += f"\nPROOF:\n{req['proof']}"
    return prompt

def gen_request(c : Client, source : str, file_name : str, model_name : str) -> list:
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    def length_of(text):
        tokens = tokenizer.encode(text)
        return len(tokens)

    rets = []
    cmds = c.fast_lex(source)

    for i, (pos, src) in enumerate(cmds):
        if (src.startswith('lemma ') or src.startswith('theorem ') or src.startswith('corollary ') or
            src.startswith('schematic_goal ') or src.startswith('proposition ')) and \
            i < len(cmds) - 1 and \
            cmds[i + 1][1].startswith('sorry'):
            pos = cmds[i + 1][0]

            c.file(file_name, pos.line, pos.column)
            local_facts_origin, _, _, fixes, goals = c.context('pretty')

            local_facts = {}
            for name, fact in local_facts_origin.items():
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
            # A tuple of (
            #     local_facts: dict[str, thm],
            #     assumptions: [thm],
            #     binding: dict[str, (typ, term)], where the key is the name of the binding,
            #         note, a binding is something that appears like `?x` in Isabelle, e.g., let ?binding = 123.
            #     (fixed term variabls, fixed type variables): (dict[str, typ], dict[str, sort]),
            #     goals: [term]
            # )
            process = Client.pretty_unicode
            ret = {
                'index': f"{file_name}:{pos.line}",
                'goals': [process(goal) for goal in goals],
                'vars': {k: process(v) for k,v in fixes[0].items()},
                'local_facts': {k: process(v) for k,v in local_facts.items()}
            }
            toks = sum(length_of(tok) + 2 for tok in ret['goals']) +\
                   sum(length_of(name) + length_of(typ) + 2 for name, typ in ret['vars'].items()) +\
                   sum(length_of(name) + length_of(fact) + 2 for name, fact in ret['local_facts'].items())
            

            premises = {}
            all_premises = c.premise_selection('final', 1000, ['mesh'], {}, 'pretty')
            for name, fact in all_premises.items():
                length = length_of(name) + length_of(fact) + 2
                if length + toks > TOKEN_LIMIT:
                    break
                premises[name] = process(fact)
                toks += length

            ret['premises'] = premises
            actual_toks = length_of(encode_prompt(ret))
            if actual_toks > 14300:
                print(f"{actual_toks}, calculated: {toks}, file: {file_name}:{pos.line}")
            else:
                rets.append(ret)

    return rets


if __name__ == "__main__":
    args = parse_args()
    ret = []
    
    # Collect all .thy files from source_files (which can be files or directories)
    thy_files = []
    for source_path in args.source_files:
        if os.path.isfile(source_path):
            thy_files.append(source_path)
        elif os.path.isdir(source_path):
            # Find all .thy files in the directory and subdirectories
            thy_pattern = os.path.join(source_path, '**', '*.thy')
            thy_files.extend(glob.glob(thy_pattern, recursive=True))
        else:
            logging.warning(f"Warning: {source_path} is neither a file nor a directory")
    
    def filter_thy_file(file):
        dir = os.path.dirname(file)
        return dir.endswith('isabelle') and 'lib/isabelle' not in dir
    thy_files = [f for f in thy_files if filter_thy_file(f)]

    task_queue = queue.Queue()
    for file_name in thy_files:
        task_queue.put(file_name)

    lock = threading.Lock()
    with open(args.output, 'w') as fout:
        counter = 0
        def worker():
            global counter
            with Client(args.address, 'HOL') as c:
                try:
                    while True:
                        try:
                            file_name = task_queue.get(timeout=1)
                        except queue.Empty:
                            return
                        logging.info(f"[{counter}/{len(thy_files)}] Processing {file_name}")
                        with open(file_name, 'r') as f:
                            source = f.read()
                        reqs = gen_request(c, source, file_name, args.model)
                        with lock:
                            ret.extend(reqs)
                            for req in reqs:
                                fout.write(json.dumps(req) + '\n')
                            counter += 1
                except Exception as e:
                    logging.error(f"Error: {e}")
                    raise e
                    exit(1)
        threads = []
        for _ in range(20):
            thread = threading.Thread(target=worker)
            thread.daemon = True  # Make threads daemon so they exit if main thread exits
            threads.append(thread)
            thread.start()
            
        # Wait for all threads to complete
        for thread in threads:
            thread.join()

