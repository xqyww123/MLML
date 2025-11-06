#!/bin/env python3
import sys
from evaluation import *
from data import *
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

def minilang_agent_handler(cls, dataset, category_loader, index_parser, case_fil_format, epilog):
    import argparse
    parser = argparse.ArgumentParser(
        description = f"Evaluate MiniLangAgent for {dataset}",
        epilog = epilog,
        formatter_class=argparse.RawTextHelpFormatter
    )
    parser.add_argument("driver", type=str, help="The agent driver to use, e.g., Gemini")
    parser.add_argument("result_db", type=str, help="The path to which the results are saved. The evaluation will be resumed if the file exists.")
    parser.add_argument("case_category", type=str, nargs="?", default="", help="The category of cases to evaluate (e.g., valid, test). Default: None")
    parser.add_argument("--timeout", "-t", type=int, default=500, help="The overall timeout for each case")
    parser.add_argument("--connection-timeout", type=int, default=1200, help="The timeout for the connection to the server")
    parser.add_argument("--step-limit", "-n", type=int, default=30, help="The maximum number of proof steps for each case")
    parser.add_argument("--parallel-runs", "-p", type=int, default=1, help="The number of parallel runs for each case")
    parser.add_argument("--query-ret-num", type=int, default=30, help="The number of queries to return by the command RETRIVE")
    parser.add_argument("--pass", type=int, dest="pass_num", default=1, help="pass@N, the number of attempts to try independently")
    parser.add_argument("-c", "--cases", action="append", nargs="+", help="One or more cases to evaluate")
    parser.add_argument("-f", "--case-file", help=f"A {case_fil_format} from which to read the cases to evaluate")

    args = parser.parse_args(sys.argv[2:])
    if args.case_category:
        cases = category_loader(args.case_category)
    else:
        cases = []
    if args.cases:
        cases.extend([index_parser(item) for sub in args.cases for item in sub]) 
    if args.case_file:
        with open(args.case_file, "r") as f:
            cases.extend([index_parser(line.strip()) for line in f])
    cases = [Case(item, [args.driver] * args.pass_num) for item in cases]
    if not cases:
        logger.error("No cases to evaluate")
        exit(1)
    result_db = args.result_db
    clean_mash(result_db)
    launch_servers()
    evaluate_and_save(
        result_db, cases,
        lambda addr: cls(
            addr, 
            timeout=args.timeout,
            connection_timeout=args.connection_timeout,
            step_limit=args.step_limit,
            parallel_runs=args.parallel_runs,
            query_ret_num=args.query_ret_num,
        ))


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
            # case 'agent':
            #     if len(sys.argv) != 4:
            #         print("Usage: ./evaluation/evaluator_top.py agent <driver> <result.db>")
            #         exit(1)
            #     proof_jsonl = sys.argv[2]
            #     result_db = sys.argv[3]
            #     cases = Case.jsonl(proof_jsonl)
            #     clean_mash(result_db)
            #     launch_servers()
            #     evaluate_and_save(result_db, cases, MinilangAgent)
            #     report_evaluation(proof_jsonl, result_db)
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

            case 'agent-miniF2F':
                def category_loader(category):
                    return MiniF2F_Data().cases_of(category)
                def index_parser(line):
                    return line
                minilang_agent_handler(MinilangAgent_MiniF2F, "MiniF2F", category_loader, index_parser,\
                    "file of lines of cases,",\
                    "Examples:\n" \
                    "    evaluation/evaluator_top.py agent-miniF2F Gemini result.db valid\n"
                )

            case 'agent-source':
                def category_loader(category):
                    logger.error(f"To use agent-source, you should indicate the Isabelle source of the target proof goals")
                    exit(1)
                def index_parser(line):
                    return line
                minilang_agent_handler(MinilangAgent_Source, "source text", category_loader, index_parser, "jsonl file",\
                    "Examples:\n" \
                    "    evaluation/evaluator_top.py agent-source Gemini result.db --cases \"theory Test imports Main begin theorem \\\"(1::nat) + 1 = 2\\\"\"\n\n" \
                    "    You can also put the proof goals in a file (e.g., cases.lst) where a line is a case; then evaluate them by:\n" \
                    "    evaluation/evaluator_top.py agent-source Gemini result.db --case-file cases.lst\n"
                    )

            # case "eval-mini-pisa":
            #     clean_mash("./evaluation/minilang_pisa_result.db")
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/minilang_response.jsonl')
            #     evaluate_and_save('./evaluation/minilang_pisa_result.db', cases, lambda addr: MiniLang_PISA(addr, SH_params="timeout = 30"))
            #     report_evaluation('./evaluation/minilang_response.jsonl', './evaluation/minilang_pisa_result.db')
            # case "eval-mini-DS-pisa":
            #     clean_mash("./evaluation/minilang-DS_pisa_result.db")
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/minilang-DS_response.jsonl')
            #     evaluate_and_save('./evaluation/minilang-DS_pisa_result.db', cases, lambda addr: MiniLang_PISA(addr, SH_params="timeout = 30"))
            #     report_evaluation('./evaluation/minilang-DS_response.jsonl', './evaluation/minilang_pisa-DS_result.db')
            # case "eval-mini-hasty-pisa":
            #     clean_mash("./evaluation/minilang_hasty_pisa_result.db")
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/minilang_response.jsonl')
            #     evaluate_and_save('./evaluation/minilang_hasty_pisa_result.db', cases, lambda addr: MiniLang_PISA(addr, hasty=True, SH_params="timeout = 10"))
            #     report_evaluation('./evaluation/minilang_response.jsonl', './evaluation/minilang_hasty_pisa_result.db')
            # case "eval-mini-no-SH-soft-pisa":
            #     clean_mash("./evaluation/minilang-no-SH-soft_pisa_result.db")
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/minilang-no-SH_response.jsonl')
            #     evaluate_and_save('./evaluation/minilang-no-SH-soft_pisa_result.db', cases, MiniLang_PISA)
            #     report_evaluation('./evaluation/minilang-no-SH-soft_response.jsonl', './evaluation/minilang-no-SH-soft_pisa_result.db')
            # case "eval-mini-DS-no-SH-pisa":
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/minilang-DS-no-SH_response.jsonl')
            #     evaluate_and_save('./evaluation/minilang-DS-no-SH_pisa_result.db', cases, MiniLang_PISA)
            #     report_evaluation('./evaluation/minilang-DS-no-SH_response.jsonl', './evaluation/minilang-DS-no-SH_pisa_result.db')
            # case "eval-mini-no-SH-pisa":
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/minilang-no-SH_response.jsonl')
            #     evaluate_and_save('./evaluation/minilang-no-SH_pisa_result.db', cases, MiniLang_PISA)
            #     report_evaluation('./evaluation/minilang-no-SH_response.jsonl', './evaluation/minilang-no-SH_pisa_result.db')
            # case "eval-isar-SH*-pisa":
            #     clean_mash("./evaluation/isar-SH*_pisa_result.db")
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/isar-SH*_response.jsonl')
            #     evaluate_and_save('./evaluation/isar-SH*_pisa_result.db', cases, lambda addr: Isar_PISA(addr, libs=['Auto_Sledgehammer.Auto_Sledgehammer']))
            #     report_evaluation('./evaluation/isar-SH*_response.jsonl', './evaluation/isar-SH*_pisa_result.db')
            # case "eval-isar-SH*-DS-pisa":
            #     clean_mash("./evaluation/isar-SH*-DS_pisa_result.db")
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/isar-SH*-DS_response.jsonl')
            #     evaluate_and_save('./evaluation/isar-SH*-DS_pisa_result.db', cases, lambda addr: Isar_PISA(addr, libs=['Auto_Sledgehammer.Auto_Sledgehammer']))
            #     report_evaluation('./evaluation/isar-SH*-DS_response.jsonl', './evaluation/isar-SH*-DS_pisa_result.db')
            # case "eval-isar-pisa":
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/isar_response.jsonl')
            #     evaluate_and_save('./evaluation/isar_pisa_result.db', cases, Isar_PISA)
            #     report_evaluation('./evaluation/isar_response.jsonl', './evaluation/isar_pisa_result.db')
            # case "eval-before_elim_pronouns_connectives":
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/before_elim_pronouns_connectives_response.jsonl')
            #     evaluate_and_save('./evaluation/before_elim_pronouns_connectives_pisa_result.db', cases, Isar_PISA)
            #     report_evaluation('./evaluation/before_elim_pronouns_connectives_response.jsonl', './evaluation/before_elim_pronouns_connectives_pisa_result.db')
            # case "eval-after_elim_pronouns_connectives":
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/after_elim_pronouns_connectives_response.jsonl')
            #     evaluate_and_save('./evaluation/after_elim_pronouns_connectives_pisa_result.db', cases, Isar_PISA)
            #     report_evaluation('./evaluation/after_elim_pronouns_connectives_response.jsonl', './evaluation/after_elim_pronouns_connectives_pisa_result.db')
            # case "eval-before_split_proof":
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/before_split_proof_response.jsonl')
            #     evaluate_and_save('./evaluation/before_split_proof_pisa_result.db', cases, Isar_PISA)
            #     report_evaluation('./evaluation/before_split_proof_response.jsonl', './evaluation/before_split_proof_pisa_result.db')
            # case "eval-after_split_proof":
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/after_split_proof_response.jsonl')
            #     evaluate_and_save('./evaluation/after_split_proof_pisa_result.db', cases, lambda addr: Isar_PISA(addr, libs=['Minilang_Translator.MS_Translator']))
            #     report_evaluation('./evaluation/after_split_proof_response.jsonl', './evaluation/after_split_proof_pisa_result.db')
            # case "eval-isar-DS-pisa":
            #     launch_servers()
            #     cases = Case.jsonl('./evaluation/isar-DS_response.jsonl')
            #     evaluate_and_save('./evaluation/isar-DS_pisa_result.db', cases, Isar_PISA)
            #     report_evaluation('./evaluation/isar-DS_response.jsonl', './evaluation/isar-DS_pisa_result.db')
            # case 'report-mini-pisa':
            #     report_evaluation('./evaluation/minilang_response.jsonl', './evaluation/minilang_pisa_result.db')
            # case 'report-mini-DS-pisa':
            #     report_evaluation('./evaluation/minilang-DS_response.jsonl', './evaluation/minilang-DS_pisa_result.db')
            # case 'report-isar-SH*-DS-pisa':
            #     report_evaluation('./evaluation/isar-SH*-DS_response.jsonl', './evaluation/isar-SH*-DS_pisa_result.db')
            # case 'report-isar-SH*-pisa':
            #     report_evaluation('./evaluation/isar-SH*_response.jsonl', './evaluation/isar-SH*_pisa_result.db')
            # case 'report-isar-pisa':
            #     report_evaluation('./evaluation/isar_response.jsonl', './evaluation/isar_pisa_result.db')
            # case 'report-tmp':
            #     report_evaluation('./evaluation/minilang_response.jsonl', './evaluation/minilang-DS_pisa_result.db.30s-500s')
            case _:
                print("Usage: python evaluation/evaluator_top.py eval-mini-pisa|eval-isar-pisa")
                exit()
    else:
        print("Usage: python evaluation/evaluator_top.py eval-mini-pisa|eval-isar-pisa")
        exit()
