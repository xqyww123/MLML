#!/usr/bin/env python3

import json
import os
import sys
import multiprocessing as mp
from transformers import AutoTokenizer

if len(sys.argv) < 4:
    print("Usage: python tmp.py <model_name> <token_limit> <file_path>")
    sys.exit(1)

model_name = sys.argv[1]
token_limit = int(sys.argv[2])
file_path = sys.argv[3]

tokenizer = None

def init_worker():
    global tokenizer
    tokenizer = AutoTokenizer.from_pretrained(model_name)

def length_of(text):
    tokens = tokenizer.encode(text)
    return len(tokens)

def encode_prompt(req):
    premises = ''.join(f"{name} : {prop}\n" for name, prop in req['premises'].items())
    vars = ''.join(f"{name} : {typ}\n" for name, typ in req['vars'].items())
    facts = ''.join(f"{name} : {fact}\n" for name, fact in req['local_facts'].items())
    goals = ''.join(f"{i+1}. {prop}\n" for i, prop in enumerate(req['goals']))
    prompt = f"LEMMAS:\n{premises}\n-----\nVARIABLES:\n{vars}\nFACTS:\n{facts}\nGOALS:\n{goals}"
    if 'proof' in req:
        prompt += f"\nPROOF:\n{req['proof']}"
    return prompt

def process_line(data):
    idx, line = data
    line = line.strip()
    obj = json.loads(line)
    prompt = encode_prompt(obj)
    size = length_of(prompt)
    if size > token_limit:
        print(f"MEET {idx}: {size}\n{prompt}")
    if idx % 1000 == 0:
        print(f"Processed {idx} lines")

with open(file_path, "r") as f:
    lines = f.readlines()

if __name__ == "__main__":
    with mp.Pool(initializer=init_worker) as pool:
        pool.map(process_line, enumerate(lines))
    
