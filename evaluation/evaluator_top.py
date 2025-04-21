#!/bin/env python3
import sys
from evaluation import evaluate_and_save, Case, MiniLang_PISA, Isar_PISA, report_evaluation
from tools.server import launch_servers
import logging

logger = logging.getLogger(__name__)
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)

if __name__ == "__main__":
    if len(sys.argv) > 1:
        match sys.argv[1]:
            case "eval-mini-pisa":
                launch_servers()
                cases = Case.PISA_file('./evaluation/minilang_response.jsonl')
                evaluate_and_save('./evaluation/minilang_pisa_result.db', cases, MiniLang_PISA)
                report_evaluation('./evaluation/minilang_response.jsonl', './evaluation/minilang_pisa_result.db')
            case "eval-mini-no-SH-pisa":
                launch_servers()
                cases = Case.PISA_file('./evaluation/minilang-no-SH_response.jsonl')
                evaluate_and_save('./evaluation/minilang-no-SH_pisa_result.db', cases, MiniLang_PISA)
                report_evaluation('./evaluation/minilang-no-SH_response.jsonl', './evaluation/minilang-no-SH_pisa_result.db')
            case "eval-isar-SH*-pisa":
                launch_servers()
                cases = Case.PISA_file('./evaluation/isar-SH*_response.jsonl')
                evaluate_and_save('./evaluation/isar-SH*_pisa_result.db', cases, lambda addr: Isar_PISA(addr, libs=['Auto_Sledgehammer.Auto_Sledgehammer']))
                report_evaluation('./evaluation/isar-SH*_response.jsonl', './evaluation/isar-SH*_pisa_result.db')
            case "eval-isar-pisa":
                launch_servers()
                cases = Case.PISA_file('./evaluation/isar_response.jsonl')
                evaluate_and_save('./evaluation/isar_pisa_result.db', cases, Isar_PISA)
                report_evaluation('./evaluation/isar_response.jsonl', './evaluation/isar_pisa_result.db')
            case 'report-mini-pisa':
                report_evaluation('./evaluation/minilang_response.jsonl', './evaluation/minilang_pisa_result.db')
            case 'report-isar-pisa':
                report_evaluation('./evaluation/isar_response.jsonl', './evaluation/isar_pisa_result.db')
            case _:
                print("Usage: python evaluation/evaluator_top.py eval-mini-pisa|eval-isar-pisa")
                exit()
    else:
        print("Usage: python evaluation/evaluator_top.py eval-mini-pisa|eval-isar-pisa")
        exit()
