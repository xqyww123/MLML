#!/usr/bin/env python3

import argparse
from IsaREPL import Client
import json
import os
import sys
import glob

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
        default='deepseek-ai/DeepSeek-Prover-V1.5-Base'
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

    ret = []
    cmds = c.lex(source)
    preludes = []

    def get_prelude() :
        n = len(preludes) - 1
        sum = 0
        while n >= 0 and sum + preludes[n][1] <= 2000:
            sum += preludes[n][1]
            n -= 1
        return '\n'.join ([p[0] for p in preludes[n + 1 :]])

    for i, (pos, src) in enumerate(cmds):
        if (src.startswith('lemma ') or src.startswith('theorem ') or src.startswith('corollary ') or
            src.startswith('schematic_goal ') or src.startswith('proposition ')) and \
            i < len(cmds) - 1 and \
            cmds[i + 1][1].startswith('sorry'):
            ret.append({
                'index': f"{file_name}:{pos.line}",
                'prelude': get_prelude(),
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
            print(f"Warning: {source_path} is neither a file nor a directory", file=sys.stderr)
    
    with Client(args.address, 'HOL') as c:
        for file_name in thy_files:
            with open(file_name, 'r') as f:
                source = f.read()
            ret.extend(gen_request(c, source, file_name, args.model))
    with open(args.output, 'w') as f:
        for x in ret:
            f.write(json.dumps(x) + '\n')
