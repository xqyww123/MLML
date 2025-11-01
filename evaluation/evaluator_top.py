#!/bin/env python3
import sys
from evaluation import evaluate_and_save, Case, MiniLang_PISA, Isar_PISA, report_evaluation, MiniLang, Isar
from tools.server import launch_servers
import logging
import os

logger = logging.getLogger(__name__)
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)

def clean_mash(result_path):
    # Ask user if they want to clean mash state
    if not os.path.exists(result_path):
        # If the result path doesn't exist, clean the mash state
        # This helps prevent issues with cached state from previous runs
        try:
            logger.info("Cleaning mash state before evaluation")
            script_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'tools', 'clean_mash.sh')
            exit_code = os.system(script_path)
            if exit_code != 0:
                logger.warning(f"Failed to clean mash state, exit code: {exit_code}")
        except Exception as e:
            logger.error(f"Error cleaning mash state: {e}")

if __name__ == "__main__":
    if len(sys.argv) > 1:
        match sys.argv[1]:
            case 'mini':
                if len(sys.argv) != 4:
                    print("Usage: ./evaluation/evaluator_top.py mini <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                cases = Case.jsonl(proof_jsonl)
                clean_mash(result_db)
                launch_servers()
                evaluate_and_save(result_db, cases, lambda addr: MiniLang(addr, SH_params="timeout = 30"))
                report_evaluation(proof_jsonl, result_db)
            case 'isar':
                if len(sys.argv) != 4:
                    print("Usage: ./evaluation/evaluator_top.py mini <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                cases = Case.jsonl(proof_jsonl)
                clean_mash(result_db)
                launch_servers()
                evaluate_and_save(result_db, cases, Isar)
                report_evaluation(proof_jsonl, result_db)
            case 'report':
                if len(sys.argv) != 4:
                    print("Usage: ./evaluation/evaluator_top.py mini <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                report_evaluation(proof_jsonl, result_db)
            case "mini-pisa":
                if len(sys.argv) != 4:
                    print("usage: ./evaluation/evaluator_top.py mini-pisa <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                clean_mash(result_db)
                launch_servers()
                cases = Case.jsonl(proof_jsonl)
                evaluate_and_save(result_db, cases, lambda addr: MiniLang_PISA(addr, SH_params="timeout = 30"))
                report_evaluation(proof_jsonl, result_db)
            case "mini-pisa-raw-SH":
                if len(sys.argv) != 4:
                    print("Usage: ./evaluation/evaluator_top.py mini-pisa-raw-SH <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                clean_mash(result_db)
                launch_servers()
                cases = Case.jsonl(proof_jsonl)
                evaluate_and_save(result_db, cases, lambda addr: MiniLang_PISA(addr, SH_params="timeout = 30, mini_use_improved_SH = false"))
                report_evaluation(proof_jsonl, result_db)
            case "mini-pisa-raw-SH-report":
                if len(sys.argv) != 4:
                    print("Usage: ./evaluation/evaluator_top.py mini-pisa-raw-SH <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                report_evaluation(proof_jsonl, result_db)
            case "isar-pisa":
                if len(sys.argv) != 4:
                    print("usage: ./evaluation/evaluator_top.py isar-pisa <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                clean_mash(result_db)
                launch_servers()
                cases = Case.jsonl(proof_jsonl)
                #evaluate_and_save(result_db, cases, Isar_PISA)
                evaluate_and_save(result_db, cases, lambda addr: Isar_PISA(addr, libs=['Auto_Sledgehammer.Auto_Sledgehammer']))
                report_evaluation(proof_jsonl, result_db)
            case "isar-pisa-report":
                if len(sys.argv) != 4:
                    print("usage: ./evaluation/evaluator_top.py isar-pisa <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                report_evaluation(proof_jsonl, result_db)
            # case "eval-mini-pisa":
            #     clean_mash("./evaluation/minilang_pisa_result.db")
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/minilang_response.jsonl')
            #     evaluate_and_save('./evaluation/minilang_pisa_result.db', cases, lambda addr: MiniLang_PISA(addr, SH_params="timeout = 30"))
            #     report_evaluation('./evaluation/minilang_response.jsonl', './evaluation/minilang_pisa_result.db')
            case "eval-mini-DS-pisa":
                clean_mash("./evaluation/minilang-DS_pisa_result.db")
                launch_servers()
                cases = Case.jsonl('./evaluation/minilang-DS_response.jsonl')
                evaluate_and_save('./evaluation/minilang-DS_pisa_result.db', cases, lambda addr: MiniLang_PISA(addr, SH_params="timeout = 30"))
                report_evaluation('./evaluation/minilang-DS_response.jsonl', './evaluation/minilang_pisa-DS_result.db')
            case "eval-mini-hasty-pisa":
                clean_mash("./evaluation/minilang_hasty_pisa_result.db")
                launch_servers()
                cases = Case.jsonl('./evaluation/minilang_response.jsonl')
                evaluate_and_save('./evaluation/minilang_hasty_pisa_result.db', cases, lambda addr: MiniLang_PISA(addr, hasty=True, SH_params="timeout = 10"))
                report_evaluation('./evaluation/minilang_response.jsonl', './evaluation/minilang_hasty_pisa_result.db')
            case "eval-mini-no-SH-soft-pisa":
                clean_mash("./evaluation/minilang-no-SH-soft_pisa_result.db")
                launch_servers()
                cases = Case.jsonl('./evaluation/minilang-no-SH_response.jsonl')
                evaluate_and_save('./evaluation/minilang-no-SH-soft_pisa_result.db', cases, MiniLang_PISA)
                report_evaluation('./evaluation/minilang-no-SH-soft_response.jsonl', './evaluation/minilang-no-SH-soft_pisa_result.db')
            case "eval-mini-DS-no-SH-pisa":
                launch_servers()
                cases = Case.jsonl('./evaluation/minilang-DS-no-SH_response.jsonl')
                evaluate_and_save('./evaluation/minilang-DS-no-SH_pisa_result.db', cases, MiniLang_PISA)
                report_evaluation('./evaluation/minilang-DS-no-SH_response.jsonl', './evaluation/minilang-DS-no-SH_pisa_result.db')
            case "eval-mini-no-SH-pisa":
                launch_servers()
                cases = Case.jsonl('./evaluation/minilang-no-SH_response.jsonl')
                evaluate_and_save('./evaluation/minilang-no-SH_pisa_result.db', cases, MiniLang_PISA)
                report_evaluation('./evaluation/minilang-no-SH_response.jsonl', './evaluation/minilang-no-SH_pisa_result.db')
            case "eval-isar-SH*-pisa":
                clean_mash("./evaluation/isar-SH*_pisa_result.db")
                launch_servers()
                cases = Case.jsonl('./evaluation/isar-SH*_response.jsonl')
                evaluate_and_save('./evaluation/isar-SH*_pisa_result.db', cases, lambda addr: Isar_PISA(addr, libs=['Auto_Sledgehammer.Auto_Sledgehammer']))
                report_evaluation('./evaluation/isar-SH*_response.jsonl', './evaluation/isar-SH*_pisa_result.db')
            case "eval-isar-SH*-DS-pisa":
                clean_mash("./evaluation/isar-SH*-DS_pisa_result.db")
                launch_servers()
                cases = Case.jsonl('./evaluation/isar-SH*-DS_response.jsonl')
                evaluate_and_save('./evaluation/isar-SH*-DS_pisa_result.db', cases, lambda addr: Isar_PISA(addr, libs=['Auto_Sledgehammer.Auto_Sledgehammer']))
                report_evaluation('./evaluation/isar-SH*-DS_response.jsonl', './evaluation/isar-SH*-DS_pisa_result.db')
            case "eval-isar-pisa":
                launch_servers()
                cases = Case.jsonl('./evaluation/isar_response.jsonl')
                evaluate_and_save('./evaluation/isar_pisa_result.db', cases, Isar_PISA)
                report_evaluation('./evaluation/isar_response.jsonl', './evaluation/isar_pisa_result.db')
            case "eval-before_elim_pronouns_connectives":
                launch_servers()
                cases = Case.jsonl('./evaluation/before_elim_pronouns_connectives_response.jsonl')
                evaluate_and_save('./evaluation/before_elim_pronouns_connectives_pisa_result.db', cases, Isar_PISA)
                report_evaluation('./evaluation/before_elim_pronouns_connectives_response.jsonl', './evaluation/before_elim_pronouns_connectives_pisa_result.db')
            case "eval-after_elim_pronouns_connectives":
                launch_servers()
                cases = Case.jsonl('./evaluation/after_elim_pronouns_connectives_response.jsonl')
                evaluate_and_save('./evaluation/after_elim_pronouns_connectives_pisa_result.db', cases, Isar_PISA)
                report_evaluation('./evaluation/after_elim_pronouns_connectives_response.jsonl', './evaluation/after_elim_pronouns_connectives_pisa_result.db')
            case "eval-before_split_proof":
                launch_servers()
                cases = Case.jsonl('./evaluation/before_split_proof_response.jsonl')
                evaluate_and_save('./evaluation/before_split_proof_pisa_result.db', cases, Isar_PISA)
                report_evaluation('./evaluation/before_split_proof_response.jsonl', './evaluation/before_split_proof_pisa_result.db')
            case "eval-after_split_proof":
                launch_servers()
                cases = Case.jsonl('./evaluation/after_split_proof_response.jsonl')
                evaluate_and_save('./evaluation/after_split_proof_pisa_result.db', cases, lambda addr: Isar_PISA(addr, libs=['Minilang_Translator.MS_Translator']))
                report_evaluation('./evaluation/after_split_proof_response.jsonl', './evaluation/after_split_proof_pisa_result.db')
            case "eval-isar-DS-pisa":
                launch_servers()
                cases = Case.jsonl('./evaluation/isar-DS_response.jsonl')
                evaluate_and_save('./evaluation/isar-DS_pisa_result.db', cases, Isar_PISA)
                report_evaluation('./evaluation/isar-DS_response.jsonl', './evaluation/isar-DS_pisa_result.db')
            case 'report-mini-pisa':
                report_evaluation('./evaluation/minilang_response.jsonl', './evaluation/minilang_pisa_result.db')
            case 'report-mini-DS-pisa':
                report_evaluation('./evaluation/minilang-DS_response.jsonl', './evaluation/minilang-DS_pisa_result.db')
            case 'report-isar-SH*-DS-pisa':
                report_evaluation('./evaluation/isar-SH*-DS_response.jsonl', './evaluation/isar-SH*-DS_pisa_result.db')
            case 'report-isar-SH*-pisa':
                report_evaluation('./evaluation/isar-SH*_response.jsonl', './evaluation/isar-SH*_pisa_result.db')
            case 'report-isar-pisa':
                report_evaluation('./evaluation/isar_response.jsonl', './evaluation/isar_pisa_result.db')
            case 'report-tmp':
                report_evaluation('./evaluation/minilang_response.jsonl', './evaluation/minilang-DS_pisa_result.db.30s-500s')
            case _:
                print("Usage: python evaluation/evaluator_top.py eval-mini-pisa|eval-isar-pisa")
                exit()
    else:
        print("Usage: python evaluation/evaluator_top.py eval-mini-pisa|eval-isar-pisa")
        exit()
