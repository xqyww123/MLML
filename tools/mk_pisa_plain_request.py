#! /usr/bin/env python3
from data.isabelle import PISA_Data
import json
import asyncio
import sys

if len(sys.argv) < 2:
    print("Usage: python mk_pisa_plain_request.py <output_path>")
    sys.exit(1)

path = sys.argv[1]

async def main():
    with open(path, 'w') as f:
        async with PISA_Data() as data:
            for i in data.all_cases():
                f.write(json.dumps({
                    'index': i
                }))
                f.write('\n')

asyncio.run(main())
