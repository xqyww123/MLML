import json
import os
import sys
from IsaREPL import Client, Position, REPLFail
from Isa_Mini import Mini
import csv
import logging
from enum import Enum
from data.isabelle import prelude_of, PISA_DATA, get_ISAR_PROOFS, get_MINIF2F_VALIDATION, get_MINIF2F_TEST
from sqlitedict import SqliteDict
import threading
import concurrent.futures
import queue  # Add standard queue module
import time
from tools.server import launch_servers, SERVERS
from typing import Callable, Tuple

logger = logging.getLogger(__name__)
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)

launch_servers()

SERVER_INSTANCES = []
for server, data in SERVERS.items():
    SERVER_INSTANCES.extend([server] * data["num-evaluator"])

class Status(Enum):
    SUCCESS = "SUCCESS"
    FAIL = "FAIL"
    CASE_NOT_AVAILABLE = "CASE_NOT_AVAILABLE"
    NOT_FINISHED = "NOT_FINISHED"

class Result:
    def __init__(self, status : Status, error : Exception | None):
        self.status = status
        self.error = error

    def __str__(self):
        return f"{self.status} {self.error}"

class CaseNotAvailable(Exception):
    """Exception raised when a test case is not available."""
    def __init__(self, message="The requested test case is not available"):
        self.message = message
        super().__init__(self.message)

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

class Evaluator:
    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        return None
    
    def all_cases(self) -> enumerate[Case]:
        raise NotImplementedError("all_cases must be implemented by subclass")
    
    def start_case(self, index) -> None:
        raise NotImplementedError("start_case must be implemented by subclass")
    
    def validate(self, index, srcs : enumerate[str]) -> Result:
        raise NotImplementedError("validate must be implemented by subclass")

    def reset(self) -> None:
        raise NotImplementedError("reset must be implemented by subclass")

class MiniLang_Base(Evaluator):
    def __init__(self, addr):
        self.addr = addr
        self.mini = Mini(self.addr, 'HOL', ML_base_injection=False)
        self.timeout = 900 * 1000

    def __enter__(self):
        if self.mini:
            self.mini.__enter__()
        super().__enter__()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        if self.mini:
            self.mini.__exit__(exc_type, exc_value, traceback)
        super().__exit__(exc_type, exc_value, traceback)
        return None
    
    def validate(self, index, srcs):
        try:
            self.start_case(index)
        except CaseNotAvailable:
            return Result(Status.CASE_NOT_AVAILABLE, None)
        result = Result(Status.FAIL, None)
        for src in srcs:
            try:
                _, finished = self.mini.eval(src, self.timeout)
                if finished:
                    result = Result(Status.SUCCESS, None)
                    break
            except REPLFail as E:
                result = Result(Status.FAIL, E)
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
        self.mini = Mini(self.addr, 'HOL', ML_base_injection=False)

class MiniLang_PISA(MiniLang_Base):
    def all_cases(self):
        return range(len(PISA_DATA))

    def start_case(self, index):
        """
        index is the index of the case in the PISA dataset, from 0 to 2999
        """
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


class Isar_Base(Evaluator):
    def __init__(self, addr):
        self.addr = addr
        self.repl = Client(addr, 'HOL')
        self.repl.record_state("init")

    def __enter__(self):
        self.repl.__enter__()
        super().__enter__()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.repl.__exit__(exc_type, exc_value, traceback)
        super().__exit__(exc_type, exc_value, traceback)
        return None

    def move_to(self, file, line, column=0):
        self.repl.rollback("init")
        self.repl.file (os.path.abspath(file), line, column, cache_position=True, use_cache=True)
    
    def reset_eval(self, src):
        self.repl.rollback("init")
        self.repl.eval(src)

    def validate(self, index, srcs):
        try:
            self.start_case(index)
        except CaseNotAvailable:
            return Result(Status.CASE_NOT_AVAILABLE, None)
        result = Result(Status.FAIL, None)
        for src in srcs:
            try:
                response, error = self.repl.eval(src, timeout=600000)
                if error:
                    result = Result(Status.FAIL, error)
                elif response and not response[-1][3][3]:
                    result = Result(Status.SUCCESS, None)
                    break
            except REPLFail as E:
                result = Result(Status.FAIL, E)
                pass
        return result

    def reset(self):
        if self.repl:
            self.repl.close()
        self.repl = Client(self.addr, 'HOL')
        self.repl.record_state("init")

class Isar_PISA(Isar_Base):
    def all_cases(self):
        return range(len(PISA_DATA))

    def start_case(self, index : int):
        """
        index is the index of the case in the PISA dataset, from 0 to 2999
        """
        try:
            pos_before, pos, statement = PISA_DATA[index]
        except KeyError:
            raise CaseNotAvailable(f"Isar_PISA: case {index} not available")
        self.move_to(pos.file, pos.line, pos.column)

class Isar(Isar_Base):
    def all_cases(self):
        ISAR_PROOFS = get_ISAR_PROOFS()
        return ISAR_PROOFS.keys()

    def start_case(self, index : Position):
        """
        index is the position of the target goal to be evaluated.
        You could call `all_cases()` to get the positions of all available training cases.
        """
        ISAR_PROOFS = get_ISAR_PROOFS()
        if index not in ISAR_PROOFS:
            raise ValueError(f"Isar: {index} is not a training case")
        self.move_to(index.file, index.line)


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

class MiniLang_MiniF2F(MiniLang_Base):
    def start_case(self, index : Tuple[str, int]):
        category, idx = index
        if category not in ["test", "valid"]:
            raise ValueError(f"Isar_MiniF2F: only support test and valid category") 
        dataset = get_MINIF2F_VALIDATION() if category == "valid" else get_MINIF2F_TEST()
        try:
            src = dataset[idx]
        except KeyError:
            raise CaseNotAvailable(f"MiniLang_MiniF2F: case {index} not available")
        self.reset_eval(src)

class Isar_MiniF2F(Isar_Base):
    def start_case(self, index : Tuple[str, int]):
        category, idx = index
        if category not in ["test", "valid"]:
            raise ValueError(f"Isar_MiniF2F: only support test and valid category") 
        dataset = get_MINIF2F_VALIDATION() if category == "valid" else get_MINIF2F_TEST()
        try:
            src = dataset[idx]
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


class Request:
    def __init__(
            self, 
            case : Case, 
            evaluator : Evaluator, 
            callback, # : Callable[[Request, Result], None], 
            retry=5
        ): # type: ignore
        self.case = case
        self.callback = callback
        self.evaluator = evaluator
        self.retry = retry

def evaluation_engine():
    task_queue = queue.Queue()

    def eval_server(server_addr):
        while True:
            try:
                while True:
                    try:
                        # Get next task from queue with timeout
                        req : Request = task_queue.get(timeout=1)
                    except queue.Empty:
                        # No more tasks in queue
                        time.sleep(1)
                        continue
                    
                    try:
                        logger.info(f"Server {server_addr} evaluating {req.case.index}")
                        evaluator = req.evaluator(server_addr)
                        try:
                            result = evaluator.validate(req.case.index, [req.case.code])
                            req.callback(req, result)
                        except REPLFail as E:
                            evaluator.reset()
                            logger.error(f"REPLFail error @ {req.case.index}: {E}")
                    except ConnectionError:
                        logger.error(f"Fail to connect to {server_addr}. Retrying in 10 seconds...")
                        task_queue.put(req)
                        time.sleep(10)
                    except Exception as e:
                        logger.error(f"Error processing case {req.case.index}: {str(e)}")
                        if req.retry > 0:
                            req.retry -= 1
                            task_queue.put(req)
                            break
                        else:
                            req.callback(Result(Status.CASE_NOT_AVAILABLE, e))
                    finally:
                        task_queue.task_done()
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
        
    return (task_queue, threads)

(task_queue, evaluator_threads) = evaluation_engine()

def evaluate(case : Case, evaluator : Evaluator, retry=5) -> concurrent.futures.Future[Result]:
    future = concurrent.futures.Future()

    def callback(req : Request, result : Result):
        if not future.done():
            future.set_result(result)
    
    task_queue.put(Request(case, evaluator, callback, retry=retry))
    return future

def evaluate_and_save(result_path : str, cases : list[Case], evaluator : Evaluator):
    success = 0
    unavailable = 0
    total = 0
    results = {}
    lock = threading.Lock()
    futures = []

    with SqliteDict(result_path, autocommit=True) as db:
        def callback(case : Case, result : Result):
            nonlocal success, unavailable, total, results
            with lock:
                db[case.index] = result
                db.commit()

                if result.status == Status.SUCCESS:
                    success += 1
                elif result.status == Status.CASE_NOT_AVAILABLE:
                    unavailable += 1
                    
                total += 1
                results[case.index] = result
                
                success_rate = success / (total-unavailable) if total - unavailable > 0 else 0
                unavailable_rate = unavailable / total if total > 0 else 0
                logger.info(f"Success: {success_rate:.3f}, Unavailable: {unavailable_rate:.3f}")

        for case in cases:
            if case.index in db and db[case.index].status != Status.CASE_NOT_AVAILABLE:
                results[case.index] = db[case.index]
                callback(case, db[case.index])
            else:
                future = evaluate(case, evaluator,  retry=5)
                future.add_done_callback(lambda f: callback(case, f.result()))
                futures.append(future)

        for future in futures:
            future.result()

    return results


# examples of evaluation
#   evaluate('./evaluation/isar_result.db',          cases, Isar,          "training")
#   evaluate('./evaluation/minilang_pisa_result.db', cases, MiniLang_PISA, "test")
#   evaluate('./evaluation/isar_pisa_result.db',     cases, Isar_PISA,     "test")
# where cases is a list of Case objects