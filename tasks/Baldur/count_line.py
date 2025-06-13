#!/usr/bin/env python3
import sys

if len(sys.argv) <= 1:
    print("Usage: python count_line.py <file>")
    sys.exit(1)

file = sys.argv[1]

import json

proofs = 0
total_lines = 0
with open(file, "r", encoding="utf-8") as f:
    for line in f:
        data = json.loads(line)
        # Count lines excluding empty lines
        proof_lines = [line for line in data['proof'].strip().split("\n") if line.strip()]
        total_lines += len(proof_lines)
        proofs += 1

print(f"Total proofs in {file}: {proofs}")
print(f"Total lines in {file}: {total_lines}")
