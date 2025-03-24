import json
import os
import sys
from IsaREPL import Client, Position, REPLFail
from Isa_Mini import Mini
import csv
import logging
from enum import Enum
from data import prelude_of, PISA_DATA
from sqlitedict import SqliteDict
import threading
import concurrent.futures
import queue  # Add standard queue module
import time
from .server import SERVERS, SERVER_INSTANCES

logger = logging.getLogger(__name__)
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)

class Result(Enum):
    SUCCESS = "SUCCESS"
    FAIL = "FAIL"
    CASE_NOT_AVAILABLE = "CASE_NOT_AVAILABLE"

class CaseNotAvailable(Exception):
    """Exception raised when a test case is not available."""
    def __init__(self, message="The requested test case is not available"):
        self.message = message
        super().__init__(self.message)

def PISA_prelude(index):
    try:
        pos_before, pos, statement = PISA_DATA[index]
        prelude = prelude_of(pos_before.file, pos_before.line)
        return prelude
    except KeyError:
        raise CaseNotAvailable(f"MiniLang_PISA: case {index} not available")

class MiniLang_Base:
    def __init__(self, addr):
        self.addr = addr
        self.mini = Mini(self.addr, 'HOL')
        self.timeout = 900 * 1000

    def __enter__(self):
        if self.mini:
            self.mini.__enter__()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        if self.mini:
            self.mini.__exit__(exc_type, exc_value, traceback)
        return None
    
    def start_case(self, category, index):
        raise NotImplementedError("start_case must be implemented by subclass")
    
    def validate(self, category, index, srcs):
        try:
            self.start_case(category, index)
        except CaseNotAvailable:
            return (Result.CASE_NOT_AVAILABLE, None)
        result = (Result.FAIL, None)
        for src in srcs:
            try:
                _, finished = self.mini.eval(src, self.timeout)
                if finished:
                    result = (Result.SUCCESS, None)
                    break
            except REPLFail as E:
                result = (Result.FAIL, E)
                pass
        return result

    def move_to(self, file, line, column):
        file = os.path.abspath(file)
        self.mini.move_to(file, line, column)

    def reset_eval(self, src):
        self.mini.set_theory_and_goal(src)

    def reset(self):
        if self.mini:
            self.mini.close()
        self.mini = Mini(self.addr, 'HOL')

class MiniLang_PISA(MiniLang_Base):
    def start_case(self, category, index):
        if category != "test":
            raise ValueError(f"MiniLang_PISA: only support test category")
        try:
            pos_before, pos, statement = PISA_DATA[index]
        except KeyError:
            raise CaseNotAvailable(f"MiniLang_PISA: case {index} not available")
        self.move_to(pos.file, pos.line, pos.column)
    

#    @classmethod
#    def print_state(response):
#        ret, finished = response
#        state = Mini.parse_prooftree(ret[2])
#        new_items = Mini.parse_item(ret[0])
#        logger.info(json.dumps(state, indent=2))
#        if ret[1]:
#            logger.info('enter case ' + ret[1])
#        if ret[0][0] or ret[0][1]:
#            logger.info('newly introduced: ' + json.dumps(new_items, indent=2))
#        if finished:
#            logger.info('All goals are proven')
#
#    def pretty_print(self, src):
#        MiniLang_PISA.print_state(self.eval(src))


class Isar_Base:
    def __init__(self, addr):
        self.addr = addr
        self.repl = Client(addr, 'HOL')
        self.repl.record_state("init")

    def __enter__(self):
        self.repl.__enter__()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.repl.__exit__(exc_type, exc_value, traceback)
        return None

    def move_to(self, file, line, column=0):
        self.repl.rollback("init")
        self.repl.eval_file (os.path.abspath(file), line, column)
    
    def reset_eval(self, src):
        self.repl.rollback("init")
        self.repl.eval(src)

    def start_case(self, category, index):
        raise NotImplementedError("start_case must be implemented by subclass")

    def validate(self, category, index, srcs):
        try:
            self.start_case(category, index)
        except CaseNotAvailable:
            return (Result.CASE_NOT_AVAILABLE, None)
        result = (Result.FAIL, None)
        for src in srcs:
            try:
                response, error = self.repl.eval(src, timeout=600000)
                if error:
                    result = (Result.FAIL, error)
                elif response and not response[-1][3][3]:
                    result = (Result.SUCCESS, None)
                    break
            except REPLFail as E:
                result = (Result.FAIL, E)
                pass
        return result

    def reset(self):
        if self.repl:
            self.repl.close()
        self.repl = Client(self.addr, 'HOL')
        self.repl.record_state("init")

class Isar_PISA(Isar_Base):
    def start_case(self, category, index):
        if category != "test":
            raise ValueError(f"Isar_PISA: only support test category")
        try:
            pos_before, pos, statement = PISA_DATA[index]
        except KeyError:
            raise CaseNotAvailable(f"Isar_PISA: case {index} not available")
        self.move_to(pos.file, pos.line, pos.column)


#if __name__ == "__main__":
#    logger.info('self-testing')
#
#    with MiniLang_PISA("127.0.0.1:6666") as test:
#        assert(test.validate("test", 0, ["END"])[0] == Result.SUCCESS)
#        assert(test.validate("test", 29, ["END"])[0] == Result.CASE_NOT_AVAILABLE)
#        assert(test.validate("test", 1, ["UNFOLD echelon_form_upt_k_def END WITH assms"])[0] == Result.SUCCESS)
#
#    with Isar_PISA("127.0.0.1:6666") as test:
#        assert(test.validate("test", 0, ["by simp"])[0] == Result.SUCCESS)
#        assert(test.validate("test", 29, ["by simp"])[0] == Result.CASE_NOT_AVAILABLE)
#        assert(test.validate("test", 1, ["using assms unfolding echelon_form_upt_k_def by auto"])[0] == Result.SUCCESS)


def preprocess_MiniF2F(addr):
    with Client(addr, 'HOL') as c:
        def parse(path):
            with open(path, 'r', encoding='utf-8') as file:
                commands = c.fast_lex(file.read())
            # Find the first theorem command
            theorem_index = -1
            for idx, (_, command) in enumerate(commands):
                if command.strip().startswith("theorem"):
                    theorem_index = idx
                    break

            if theorem_index == -1:
                raise Exception(f"MiniF2F: No theorem found in {path}")
            
            src = '\n'.join([command[1] for command in commands[:theorem_index+1]])
            return src
        def mk_dataset(path):
            validate_files = [f for f in os.listdir(path)]
            validation_set = {}
            for file in validate_files:
                src = parse(f'{path}/{file}')
                name, _ = os.path.splitext(os.path.basename(file))
                validation_set[name] = src
            return validation_set
        validate_set = mk_dataset('./data/miniF2F/isabelle/valid')
        test_set = mk_dataset('./data/miniF2F/isabelle/test')
        with open('data/miniF2F_validation.json', 'w', encoding='utf-8') as f:
            json.dump(validate_set, f, ensure_ascii=False, indent=4)
        with open('data/miniF2F_test.json', 'w', encoding='utf-8') as f:
            json.dump(test_set, f, ensure_ascii=False, indent=4)

if not os.path.isfile('data/miniF2F_validation.json') or not os.path.isfile('data/miniF2F_test.json'):
    preprocess_MiniF2F("127.0.0.1:6666")

if __name__ == "__main__":
    with open('data/miniF2F_validation.json', 'r', encoding='utf-8') as f:
        MINIF2F_VALIDATION = json.load(f)
    with open('data/miniF2F_test.json', 'r', encoding='utf-8') as f:
        MINIF2F_TEST = json.load(f)

class MiniLang_MiniF2F(MiniLang_Base):
    def start_case(self, category, index):
        if category not in ["test", "valid"]:
            raise ValueError(f"MiniLang_MiniF2F: only support test and valid category")
        dataset = MINIF2F_VALIDATION if category == "valid" else MINIF2F_TEST
        try:
            src = dataset[index]
        except KeyError:
            raise CaseNotAvailable(f"MiniLang_MiniF2F: case {index} not available")
        self.reset_eval(src)

class Isar_MiniF2F(Isar_Base):
    def start_case(self, category, index):
        if category not in ["test", "valid"]:
            raise ValueError(f"Isar_MiniF2F: only support test and valid category") 
        dataset = MINIF2F_VALIDATION if category == "valid" else MINIF2F_TEST
        try:
            src = dataset[index]
        except KeyError:
            raise CaseNotAvailable(f"Isar_MiniF2F: case {index} not available")
        self.reset_eval(src)

#if __name__ == "__main__":
#    logger.info('self-testing MiniF2F')
#    with MiniLang_MiniF2F("127.0.0.1:6666") as test:
#        assert(test.validate("valid", "aime_1983_p9", [
#            r"""DEFINE y where "y=x * sin x"
#            HAVE fact0: "12 \<le> (9 * y^2 + 4) / y" 
#                HAVE fact1: "y>0" UNFOLD y_def END WITH sin_gt_zero assms
#                HAVE fact2: "0 \<le> (3 * y - 2)^2" END
#            END WITH fact1 fact2 field_simps power2_eq_square
#            UNFOLD y_def
#            END WITH fact0 power2_eq_square algebra_simps
#            """
#            ])[0] == Result.SUCCESS)
#
#    with Isar_MiniF2F("127.0.0.1:6666") as test:
#        assert(test.validate("valid", "aime_1983_p9", [
#            r""" proof -
#    define y where "y=x * sin x"
#    have "12 \<le> (9 * y^2 + 4) / y" 
#    proof -
#        have "y>0" using assms unfolding y_def 
#        by (simp add: sin_gt_zero)
#        moreover have "0 \<le> (3 * y - 2)^2" by auto
#        ultimately show ?thesis unfolding power2_eq_square
#        by (auto simp:field_simps)
#    qed
#    then show ?thesis unfolding y_def 
#        by (auto simp:power2_eq_square algebra_simps)
#    qed"""
#        ])[0] == Result.SUCCESS)

class Case:
    def __init__(self, index, code):
        self.index = index
        self.code = code

    @staticmethod
    def PISA_file(response_path):
        ret = []
        with open(response_path, "r", encoding="utf-8") as f: 
                for line in f:
                    data = json.loads(line)
                    ret.append(Case(data["index"], data["response"]))
        return ret


def evaluate(result_path, cases, evaluator, category):
    # Setup shared variables with thread-safe access
    success = 0
    unavailable = 0
    total = 0
    results = {}
    lock = threading.Lock()

    def log_state():
        with lock:
            success_rate = success / (total-unavailable) if total - unavailable > 0 else 0
            unavailable_rate = unavailable / total if total > 0 else 0
            logger.info(f"Success: {success_rate:.3f}, Unavailable: {unavailable_rate:.3f}")
            
    # Create a task queue from all cases
    task_queue = queue.Queue()
    for case in cases:
        task_queue.put(case)

    logger.info(f"Starting {evaluator.__name__} evaluation of {len(cases)} {category} cases. The result will be saved to {result_path}")
    with SqliteDict(result_path, autocommit=True) as db:
        def eval_server(server_addr):
            nonlocal success, unavailable, total, results
            while not task_queue.empty():
                logger.info(f"Connecting to server {server_addr}")
                try:
                    with evaluator(server_addr) as test:
                        while True:
                            try:
                                # Get next task from queue with timeout
                                case : Case = task_queue.get(timeout=1)
                            except queue.Empty:
                                # No more tasks in queue
                                return
                            
                            try:
                                logger.info(f"Server {server_addr} evaluating {case.index}")
                                
                                # Check if result already exists in database
                                if case.index in db and db[case.index] != Result.CASE_NOT_AVAILABLE and db[case.index] != 0:
                                    result, err = db[case.index]
                                else:
                                    try:
                                        result, err = test.validate(category, case.index, [case.code])
                                        db[case.index] = (result, err)
                                    except REPLFail as E:
                                        test.reset()
                                        logger.error(f"REPLFail error: {E}")
                                        result = Result.CASE_NOT_AVAILABLE
                            except Exception as e:
                                logger.error(f"Error processing case {case.index}: {str(e)}")
                                # Put the task back in the queue to retry
                                task_queue.put(case)
                                break
                            finally:
                                # Mark task as done
                                task_queue.task_done()
                                    
                            with lock:
                                # Update statistics
                                if result == Result.SUCCESS:
                                    success += 1
                                elif result == Result.CASE_NOT_AVAILABLE:
                                    unavailable += 1
                                
                                total += 1
                                results[case.index] = result
                                
                            log_state()
                except ConnectionRefusedError:
                    logger.error(f"Fail to connect to {server_addr}. Retrying in 10 seconds...")
                    time.sleep(10)
                except Exception as e:
                    logger.error(f"Worker thread for server {server_addr} encountered an error: {str(e)}. Retrying in 10 seconds...")
                    time.sleep(10)
        
        # Create and start worker threads for each server
        threads = []
        for server_addr in SERVER_INSTANCES:
            thread = threading.Thread(target=eval_server, args=(server_addr,))
            thread.daemon = True  # Make threads daemon so they exit if main thread exits
            threads.append(thread)
            thread.start()
            
        # Wait for all threads to complete
        for thread in threads:
            thread.join()

    logger.info(f"Evaluation complete. Processed {total}/{len(cases)} cases.")
    log_state()
    return results

