#!/usr/bin/env python3
from Isabelle_RPC_Host.unicode import pretty_unicode
import sys
import json

if len(sys.argv) != 2:
    print(f"Usage: {sys.argv[0]} <target jsonl file>")
    sys.exit(1)
path = sys.argv[1]

def unicode(data):
    data['text'] = pretty_unicode(data['text'])
    return data

with open(path, 'r') as f:
    DATA = [unicode(json.loads(line)) for line in f]

with open(path, 'w') as f:
    for data in DATA:
        f.write(json.dumps(data))
        f.write('\n')