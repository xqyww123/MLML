#!/usr/bin/env python3

import json
import os
import sys

if len(sys.argv) < 2:
    print("Usage: python tmp.py <file_path>")
    sys.exit(1)

file_path = sys.argv[1]

def encode_prompt(req):
    premises = ''.join(f"{name} : {prop}\n" for name, prop in req['premises'].items())
    vars = ''.join(f"{name} : {typ}\n" for name, typ in req['vars'].items())
    facts = ''.join(f"{name} : {fact}\n" for name, fact in req['local_facts'].items())
    goals = ''.join(f"{i+1}. {prop}\n" for i, prop in enumerate(req['goals']))
    prompt = f"LEMMAS:\n{premises}\n-----\nVARIABLES:\n{vars}\nFACTS:\n{facts}\nGOALS:\n{goals}"
    if 'proof' in req:
        prompt += f"\nPROOF:\n{req['proof']}"
    return prompt

with open(file_path, "r") as f:
    lines = f.readlines()
    for line in lines:
        line = line.strip()
        obj = json.loads(line)
        print(encode_prompt(obj))
        print("-----------------------------------\n\n")

