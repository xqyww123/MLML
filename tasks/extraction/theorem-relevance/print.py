#! /usr/bin/env python3
import sys
import json

for line in sys.stdin:
    line = line.rstrip('\n')
    (goal, premise) = json.loads(line)
    print(f"\033[38;5;208m{goal}\033[0m\n\033[1m->\033[0m\n\033[38;5;213m{premise}\033[0m\n-------------")
