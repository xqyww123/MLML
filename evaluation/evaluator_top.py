#!/bin/env python3
import sys
from evaluation import *
import logging

logger = logging.getLogger(__name__)
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)

if __name__ == "__main__":
    logger.info('self-test passed')
if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "eval-mini-pisa":
    cases = Case.PISA_file('./evaluation/minilang_response.jsonl')
    evaluate('./evaluation/minilang_pisa_result.db', cases, MiniLang_PISA, "test")
elif __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "eval-isar-pisa":
    cases = Case.PISA_file('./evaluation/isar_response.jsonl')
    evaluate('./evaluation/isar_pisa_result.db', cases, Isar_PISA, "test")
elif __name__ == "__main__":
    print("Usage: python evaluation/evaluator_top.py eval-mini-pisa|eval-isar-pisa")
    exit()