#!/bin/env python3

import sys
import os
import json

USAGE = """
Usage: python mk_sledgehammer_response.py <response_file> [CMD]

Replace all the responses in the `response_file` to `auto_sledgehammer`
"""

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(USAGE)
        sys.exit(1)
    
    response_file = sys.argv[1]
    cmd = sys.argv[2] if len(sys.argv) > 2 else "by auto_sledgehammer"
    with open(response_file, "r") as f:
        for line in f:
            obj = json.loads(line)
            obj["response"] = cmd
            print(json.dumps(obj))