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
        default='anonymous6435/deepseek-prover-minilang'
    )

    return parser.parse_args()

from transformers import AutoTokenizer

def count_tokens(text, model_name):
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    
    tokens = tokenizer.encode(text)
    token_count = len(tokens)
    
    return token_count


def gen_request(c : Client, source : str, file_name : str, model_name : str) -> list:
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    def count_tokens(text):
        tokens = tokenizer.encode(text)
        return len(tokens)

    ret = []
    cmds = c.fast_lex(source)
    preludes = []
    parent_preludes = []
    dir = os.path.dirname(file_name)

    for (_, src) in cmds:
        if src.startswith('theory'):
            _, imports, _ = c.parse_thy_header(src)
            for i in imports:
                path = c.path_of_theory(i, dir)
                with open(path, 'r') as f:
                    for (_, src) in c.fast_lex(f.read()):
                        parent_preludes.append((src, count_tokens(src)))

    def get_prelude(sum) :
        n = len(preludes) - 1
        while n >= 0 and sum + preludes[n][1] <= 2000:
            sum += preludes[n][1] + 1
            n -= 1
        first_prelude = '\n'.join ([p[0] for p in preludes[n + 1 :]])
        #print(f"TOKEN USAGE 111: {sum}")
        if n < 0:
            n = len(parent_preludes) - 1
            while n >= 0 and sum + parent_preludes[n][1] <= 2000:
                sum += parent_preludes[n][1] + 1
                n -= 1
            second_prelude = '\n'.join ([p[0] for p in parent_preludes[n + 1 :]]) + '\n'
        else:
            second_prelude = ''
        logging.info(f"TOKEN USAGE: {sum}")
        return second_prelude + first_prelude

    for i, (_, src) in enumerate(cmds):
        if (src.startswith('lemma ') or src.startswith('theorem ') or src.startswith('corollary ') or
            src.startswith('schematic_goal ') or src.startswith('proposition ')) and \
            i < len(cmds) - 1 and \
            cmds[i + 1][1].startswith('sorry'):
            pos = cmds[i + 1][0]
            src_tokens = count_tokens(src)
            if src_tokens > 4000:
                logging.warning(f"Warning: {file_name}:{pos.line} has {src_tokens} tokens, which is greater than 4000. Skipping...")
                continue
            ret.append({
                'index': f"{file_name}:{pos.line}",
                'prelude': get_prelude(src_tokens),
                'goal': src
            })
        else:
            tokens = tokenizer.encode(src)
            token_count = len(tokens)
            preludes.append((src, token_count + 1))

    return ret


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
                    exit(1)
        threads = []
        for _ in range(2):
            thread = threading.Thread(target=worker)
            thread.daemon = True  # Make threads daemon so they exit if main thread exits
            threads.append(thread)
            thread.start()
            
        # Wait for all threads to complete
        for thread in threads:
            thread.join()

