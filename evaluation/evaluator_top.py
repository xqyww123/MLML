#!/bin/env python3
import sys
import asyncio
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

def clean_mash(result_path : str | None):
    # Ask user if they want to clean mash state
    if result_path is not None and not os.path.exists(result_path):
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

def _no_category(msg: str):
    def _loader(_category):
        logger.error(msg)
        exit(1)
    return _loader

def autocorrode_handler(cls, dataset, category_loader, index_parser):
    import argparse
    parser = argparse.ArgumentParser(
        description=f"Evaluate AutoCorrode for {dataset}",
        formatter_class=argparse.RawTextHelpFormatter
    )
    parser.add_argument("--case-category", type=str, nargs="?", default="",
        help="Category of cases (e.g., valid, test)")
    parser.add_argument("--result", "-o", type=str, nargs="?",
        help="Path to save results (SQLite DB). Resumes if exists.")
    parser.add_argument("--timeout-seconds", type=int, default=14400,
        help="Timeout per case in seconds (default: 14400 = 4 hours)")
    parser.add_argument("--workers", "-w", type=int, default=1,
        help="Number of parallel workers (default: 1)")
    parser.add_argument("--display", type=str, default=":99",
        help="X11 DISPLAY (default: :99)")
    parser.add_argument("--isabelle-bin", type=str, default=None,
        help="Path to isabelle binary (auto-detected if omitted)")
    parser.add_argument("--iq-session-dir", type=str, default=None,
        help="Path to iq session directory (auto-detected if omitted)")
    parser.add_argument("--threads", type=int, default=None,
        help="Number of Isabelle threads per worker (default: Isabelle default)")
    parser.add_argument("-c", "--cases", action="append", nargs="+",
        help="One or more cases to evaluate")
    parser.add_argument("-f", "--case-file",
        help="File of cases (one per line)")
    parser.add_argument("--log-dir", type=str, default=None,
        help="Directory to persist per-case Isabelle logs")
    parser.add_argument("--retry-failure", action="store_true", default=False,
        help="Re-evaluate previously failed cases")
    parser.add_argument("--force-retry", action="append", nargs="+",
        help="Cases to force re-evaluate")
    parser.add_argument("--force-retry-file",
        help="File of cases to force re-evaluate (one per line)")
    parser.add_argument("--reverify-failures", action="store_true", default=False,
        help="For each previously-FAILED case, re-run ONLY the REPL verification on the\n"
             "proof the prior run already produced (read from --log-dir); do NOT launch\n"
             "jEdit or re-run the agent. Useful after fixing the verifier (e.g. oracle\n"
             "whitelist). SUCCESS cases are untouched; cases with no saved proof or with\n"
             "sorry still present stay FAILED. Prior cost/response data is preserved.")
    parser.add_argument("--repl-addr", type=str, default="127.0.0.1:6666",
        help="REPL server address (host:port) for independent proof verification.\n"
             "Each proof that passes the sorry check is re-verified via Isa-REPL\n"
             "to confirm it has no errors. (default: 127.0.0.1:6666)")

    args = parser.parse_args(sys.argv[2:])

    cases = []
    if args.case_category:
        cases.extend(category_loader(args.case_category))
    if args.cases:
        cases.extend([index_parser(item) for sub in args.cases for item in sub])
    if args.case_file:
        with open(args.case_file, "r") as f:
            cases.extend([index_parser(line.strip()) for line in f if line.strip()])
    cases = [Case(item, ["autocorrode"]) for item in cases]
    if not cases:
        logger.error("No cases to evaluate")
        exit(1)

    force_retry_cases = []
    if args.force_retry:
        force_retry_cases.extend([index_parser(item) for sub in args.force_retry for item in sub])
    if args.force_retry_file:
        with open(args.force_retry_file, "r") as f:
            force_retry_cases.extend([index_parser(line.strip()) for line in f if line.strip()])
    force_retry_set = frozenset(force_retry_cases)

    worker_ids = [f"w{i}" for i in range(args.workers)]
    result_db = args.result

    log_dir = args.log_dir
    if log_dir is None and result_db is not None:
        log_dir = os.path.splitext(result_db)[0] + "-logs"
        logger.info(f"Auto log dir: {log_dir}")

    async def _run():
        await evaluate_and_save(
            result_db, cases,
            lambda wid: cls(
                wid,
                isabelle_bin=args.isabelle_bin,
                iq_session_dir=args.iq_session_dir,
                timeout_seconds=args.timeout_seconds,
                display=args.display,
                threads=args.threads,
                log_dir=log_dir,
                repl_addr=args.repl_addr,
            ),
            retry_failure=args.retry_failure,
            force_retry=force_retry_set,
            server_instances=worker_ids,
            reverify_failures=args.reverify_failures)
    asyncio.run(_run())

def minilang_agent_handler(cls, dataset, category_loader, index_parser, case_fil_format, epilog):
    import argparse
    parser = argparse.ArgumentParser(
        description = f"Evaluate MiniLangAgent for {dataset}",
        epilog = epilog,
        formatter_class=argparse.RawTextHelpFormatter
    )
    parser.add_argument("driver", type=str, help="Driver in format DRIVER[.ARG], e.g., Claude.opus-4-6")
    parser.add_argument("--case-category", type=str, nargs="?", default="", help="The category of cases to evaluate (e.g., valid, test). Default: None")
    parser.add_argument("--result", "-o", type=str, nargs="?", help="The path to which the results are saved. The evaluation will be resumed if the file exists.")
    parser.add_argument("--timeout", "-t", type=int, default=500, help="The overall timeout for each case")
    parser.add_argument("--connection-timeout", type=int, default=1200, help="The timeout for the connection to the server")
    parser.add_argument("--timeout-seconds", type=int, default=14400, help="The overall timeout in seconds for each case (default: 14400)")
    parser.add_argument("--max-tool-calls", type=int, default=10000, help="The maximum number of tool calls for each case (default: 10000)")
    parser.add_argument("--max-retries", type=int, default=8, help="The maximum number of retries for each case (default: 8)")
    parser.add_argument("--pass", type=int, dest="pass_num", default=1, help="pass@N, the number of attempts to try independently")
    parser.add_argument("--log-dir", type=str, default=None, help="Directory for agent invocation logs (default: use Isabelle config)")
    parser.add_argument("--retrieval-forking", type=str, default=None,
        choices=["with_ctxt", "without_ctxt", "cheaper_no_ctxt"],
        help="Retrieval forking mode (default: with_ctxt)")
    parser.add_argument("--interactive-retrieval", type=str, default=None,
        choices=["no", "yes", "yes_recursive"],
        help="Interactive retrieval mode (default: no)")
    parser.add_argument("-c", "--cases", action="append", nargs="+", help="One or more cases to evaluate")
    parser.add_argument("-f", "--case-file", help=f"A {case_fil_format} from which to read the cases to evaluate")
    parser.add_argument("--retry-failure", action="store_true", default=False,
        help="Re-evaluate cases that previously failed (default: skip them)")
    parser.add_argument("--force-retry", action="append", nargs="+",
        help="Cases to force re-evaluate regardless of previous result")
    parser.add_argument("--force-retry-file",
        help="A file of cases (one per line) to force re-evaluate regardless of previous result")

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
    force_retry_cases = []
    if args.force_retry:
        force_retry_cases.extend([index_parser(item) for sub in args.force_retry for item in sub])
    if args.force_retry_file:
        with open(args.force_retry_file, "r") as f:
            force_retry_cases.extend([index_parser(line.strip()) for line in f if line.strip()])
    force_retry_set = frozenset(force_retry_cases)

    result_db = args.result
    clean_mash(result_db)
    async def _run():
        await launch_servers()
        await evaluate_and_save(
        result_db, cases,
        lambda addr: cls(
            addr,
            timeout=args.timeout,
            connection_timeout=args.connection_timeout,
            timeout_seconds=args.timeout_seconds,
            max_tool_calls=args.max_tool_calls,
            max_retries=args.max_retries,
            log_dir=args.log_dir,
            retrieval_forking=args.retrieval_forking,
            interactive_retrieval=args.interactive_retrieval,
        ),
        retry_failure=args.retry_failure,
        force_retry=force_retry_set)
    asyncio.run(_run())


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
                async def _run():
                    await launch_servers()
                    await evaluate_and_save(result_db, cases, lambda addr: MiniLang(addr, SH_params="timeout = 30"))
                asyncio.run(_run())
                report_evaluation(proof_jsonl, result_db)
            case 'isar':
                if len(sys.argv) != 4:
                    print("Usage: ./evaluation/evaluator_top.py isar <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                cases = Case.jsonl(proof_jsonl)
                clean_mash(result_db)
                async def _run():
                    await launch_servers()
                    await evaluate_and_save(result_db, cases, Isar)
                asyncio.run(_run())
                report_evaluation(proof_jsonl, result_db)
            case 'SH-embed':
                if len(sys.argv) != 4:
                    print("Usage: ./evaluation/evaluator_top.py SH-embed <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                cases = Case.jsonl(proof_jsonl)
                clean_mash(result_db)
                async def _run():
                    await launch_servers()
                    await evaluate_and_save(result_db, cases, lambda addr: MiniLang(addr, SH_params="timeout=60, mini_use_improved_SH=false, fact_filter=embd"))
                asyncio.run(_run())
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
                cases = Case.jsonl(proof_jsonl)
                async def _run():
                    await launch_servers()
                    await evaluate_and_save(result_db, cases, lambda addr: MiniLang_PISA(addr, SH_params="timeout = 30"))
                asyncio.run(_run())
                report_evaluation(proof_jsonl, result_db)
            case "mini-pisa-raw-SH":
                if len(sys.argv) != 4:
                    print("Usage: ./evaluation/evaluator_top.py mini-pisa-raw-SH <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                clean_mash(result_db)
                cases = Case.jsonl(proof_jsonl)
                async def _run():
                    await launch_servers()
                    await evaluate_and_save(result_db, cases, lambda addr: MiniLang_PISA(addr, SH_params="timeout = 30, mini_use_improved_SH = false"))
                asyncio.run(_run())
                report_evaluation(proof_jsonl, result_db)
            case "mini-pisa-raw-SH-report":
                if len(sys.argv) != 4:
                    print("Usage: ./evaluation/evaluator_top.py mini-pisa-raw-SH <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                report_evaluation(proof_jsonl, result_db)
            case 'SH-embed-pisa':
                if len(sys.argv) != 4:
                    print("Usage: ./evaluation/evaluator_top.py SH-embed-pisa <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                clean_mash(result_db)
                cases = Case.jsonl(proof_jsonl)
                async def _run():
                    await launch_servers()
                    await evaluate_and_save(result_db, cases, lambda addr: MiniLang_PISA(addr, SH_params="timeout=60, mini_use_improved_SH=false, fact_filter=embd"))
                asyncio.run(_run())
                report_evaluation(proof_jsonl, result_db)
            case "isar-pisa":
                if len(sys.argv) != 4:
                    print("usage: ./evaluation/evaluator_top.py isar-pisa <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                clean_mash(result_db)
                cases = Case.jsonl(proof_jsonl)
                async def _run():
                    await launch_servers()
                    await evaluate_and_save(result_db, cases, lambda addr: Isar_PISA(addr, libs=['Auto_Sledgehammer.Auto_Sledgehammer']))
                asyncio.run(_run())
                report_evaluation(proof_jsonl, result_db)
            case "isar-pisa-report":
                if len(sys.argv) != 4:
                    print("usage: ./evaluation/evaluator_top.py isar-pisa <proof.jsonl> <result.db>")
                    exit(1)
                proof_jsonl = sys.argv[2]
                result_db = sys.argv[3]
                report_evaluation(proof_jsonl, result_db)

            case 'agent-miniF2F':
                minilang_agent_handler(MinilangAgent_MiniF2F, "MiniF2F",
                    lambda category: MiniF2F_Data().cases_of(category),
                    lambda line: line,
                    "file of lines of cases,",
                    "Examples:\n"
                    "    evaluation/evaluator_top.py agent-miniF2F Gemini --result result.db --case-category valid\n"
                )

            case 'agent-putnam':
                minilang_agent_handler(pick_putnam_cls(MinilangAgent_PutnamBench), "PutnamBench",
                    lambda category: PutnamBench_Data().cases_of(category),
                    lambda line: line,
                    "file of lines of cases,",
                    "Examples:\n"
                    "    evaluation/evaluator_top.py agent-putnam Claude.opus-4-6 --result result.db --case-category test\n"
                )

            case 'agent-ntp4vc':
                minilang_agent_handler(MinilangAgent_NTPVC, "NTP4VC",
                    lambda category: NTPVC_Data().cases_of(category),
                    lambda line: line,
                    "file of lines of cases,",
                    "Examples:\n"
                    "    evaluation/evaluator_top.py agent-ntp4vc Claude.opus-4-6 --result result.db --case-category frama_c\n"
                )

            case 'autocorrode-miniF2F':
                from evaluation.autocorrode import AutoCorrode_MiniF2F
                autocorrode_handler(AutoCorrode_MiniF2F, "MiniF2F",
                    lambda category: MiniF2F_Data().cases_of(category),
                    lambda line: line)

            case 'autocorrode-putnam':
                from evaluation.autocorrode import AutoCorrode_PutnamBench
                autocorrode_handler(AutoCorrode_PutnamBench, "PutnamBench",
                    lambda category: PutnamBench_Data().cases_of(category),
                    lambda line: line)

            case 'agent-source':
                minilang_agent_handler(MinilangAgent_Source, "source text",
                    _no_category("To use agent-source, you should indicate the Isabelle source of the target proof goals"),
                    lambda line: line,
                    "jsonl file",
                    "Examples:\n"
                    "    evaluation/evaluator_top.py agent-source Gemini --result result.db --cases \"theory Test imports Main begin theorem \\\"(1::nat) + 1 = 2\\\"\"\n\n"
                    "    You can also put the proof goals in a file (e.g., cases.lst) where a line is a case; then evaluate them by:\n"
                    "    evaluation/evaluator_top.py agent-source Gemini --result result.db --case-file cases.lst\n"
                )

            case 'agent-pisa':
                minilang_agent_handler(MinilangAgent_PISA, "PISA",
                    _no_category("PISA dataset does not support categories. Use --cases or --case-file instead."),
                    int,
                    "file of lines of PISA case indices (integers 0-2999)",
                    "Examples:\n"
                    "    evaluation/evaluator_top.py agent-pisa ClaudeCode --result result.db --cases 0 1 2\n"
                )

            case 'agent-afp':
                def _afp_index_parser(line):
                    from IsaREPL import Position
                    return Position.from_s(line)
                minilang_agent_handler(MinilangAgent_AFP, "AFP",
                    _no_category("AFP dataset does not support categories. Use --cases or --case-file instead."),
                    _afp_index_parser,
                    "file of lines of AFP positions (file:line format)",
                    "Examples:\n"
                    "    evaluation/evaluator_top.py agent-afp ClaudeCode --result result.db --cases /path/to/Theory.thy:42\n"
                )

            case 'agent':
                minilang_agent_handler(MinilangAgent, "file:line:column",
                    _no_category("Generic agent mode does not support categories. Use --cases or --case-file instead."),
                    lambda line: line,
                    "file of lines of file:line:column locations",
                    "Examples:\n"
                    "    evaluation/evaluator_top.py agent ClaudeCode --result result.db --cases path/to/Theory.thy:42:0\n"
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
