#!/usr/bin/env python3
from evaluation.evaluator import MinilangAgent

import sys
import argparse

parser = argparse.ArgumentParser(description="Run agent with file location")
parser.add_argument("file_line_column", help="File location in format <file>:<line>:<column>")
parser.add_argument("--driver", default="ClaudeCode", help="the agent driver you will use, e.g., ClaudeCode")
parser.add_argument("--repl", default="127.0.0.1:6666", help="REPL server address (default: 127.0.0.1:6666)")
parser.add_argument("--timeout", type=int, default=500, help="Timeout in seconds (default: 500)")
parser.add_argument("--connection-timeout", type=int, default=1200, help="Connection timeout in seconds (default: 1200)")
parser.add_argument("--step-limit", type=int, default=30, help="Step limit (default: 30)")
parser.add_argument("--parallel-runs", type=int, default=1, help="Parallel runs (default: 1)")
parser.add_argument("--query-ret-num", type=int, default=30, help="Query return number (default: 30)")

args = parser.parse_args()

file_line_column = args.file_line_column
try:
    file, line, column = file_line_column.split(":")
    line = int(line)
    column = int(column)
except ValueError:
    print(f"Invalid input {file_line_column}. Must be <file>:<line>:<column>")
    sys.exit(1)

with MinilangAgent(
    args.repl,
    timeout=args.timeout,
    connection_timeout=args.connection_timeout,
    step_limit=args.step_limit,
    parallel_runs=args.parallel_runs,
    query_ret_num=args.query_ret_num
) as agent:
    print(f"Loading the file {file_line_column}")
    agent.start_case(file_line_column)
    print(f"Loaded. Running the agent {args.driver}")
    result = agent.validate(file_line_column, args.driver)
    print(result)
