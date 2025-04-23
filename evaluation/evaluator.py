import json
import os
import sys
from IsaREPL import Client, Position, REPLFail
from Isa_Mini import Mini
import csv
import logging
from enum import Enum
from data.isabelle import CaseNotAvailable, PISA_Data, get_MINIF2F_VALIDATION, get_MINIF2F_TEST, MiniF2F_Data, AFP_Data
from sqlitedict import SqliteDict
import threading
import concurrent.futures
import queue  # Add standard queue module
import time
from tools.server import SERVERS
from typing import Callable, Tuple

logger = logging.getLogger(__name__)
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)

SERVER_INSTANCES = []
for server, data in SERVERS.items():
    SERVER_INSTANCES.extend([server] * data["num-evaluator"])

class Status(Enum):
    SUCCESS = "SUCCESS"
    FAIL = "FAIL"
    CASE_NOT_AVAILABLE = "CASE_NOT_AVAILABLE"

class Result:
    def __init__(self, status : Status, error : Exception | None):
        self.status = status
        self.error = error

    def __str__(self):
        return f"{self.status} {self.error}"

class Case:
    def __init__(self, index, proof):
        self.index = index
        self.code = proof

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
    
    def all_cases(self): # -> enumerate[Index]:
        raise NotImplementedError("all_cases must be implemented by subclass")

    def validate(self, index, src : str) -> Result:
        raise NotImplementedError("validate must be implemented by subclass")
    
    def start_case(self, index) -> None:
        raise NotImplementedError("start_case must be implemented by subclass")

    def reset(self) -> None:
        raise NotImplementedError("reset must be implemented by subclass")

class MiniLang_Base(Evaluator):
    def __init__(self, addr, *args, **kwargs):
        self.addr = addr
        self.mini = Mini(self.addr, 'HOL', ML_base_injection=False, timeout=900, *args, **kwargs)
        self._timeout = 900 * 1000

    def __enter__(self):
        if self.mini:
            self.mini.__enter__()
        super().__enter__()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        if self.mini:
            self.mini.__exit__(exc_type, exc_value, traceback)
            self.mini = None
        super().__exit__(exc_type, exc_value, traceback)
        return None

    def close(self):
        if self.mini:
            self.mini.close()
            self.mini = None
    
    def validate(self, index, src):
        try:
            self.start_case(index)
        except CaseNotAvailable:
            return Result(Status.CASE_NOT_AVAILABLE, None)
        try:
            _, finished = self.mini.eval(src, self._timeout)
            if finished:
                return Result(Status.SUCCESS, None)
            else:
                return Result(Status.FAIL, "Proof not finished")
        except REPLFail as E:
            return Result(Status.FAIL, E)
        except TimeoutError as E:
            return Result(Status.FAIL, E)

    def move_to(self, file, line, column):
        file = os.path.abspath(file)
        self.mini.move_to(file, line, column)

    def reset_eval(self, src):
        self.mini.set_theory_and_goal(src)

    def reset(self):
        if self.mini:
            self.mini.close()
        self.mini = Mini(self.addr, 'HOL', ML_base_injection=False)

class MiniLang_PISA(MiniLang_Base, PISA_Data):

    def __init__(self, addr, *args, **kwargs):
        MiniLang_Base.__init__(self, addr, *args, **kwargs)
        PISA_Data.__init__(self)

    def __exit__(self, exc_type, exc_value, traceback):
        PISA_Data.__exit__(self, exc_type, exc_value, traceback)
        MiniLang_Base.__exit__(self, exc_type, exc_value, traceback)
        return None
    
    def __enter__(self):
        PISA_Data.__enter__(self)
        MiniLang_Base.__enter__(self)
        return self
    
    def close(self):
        PISA_Data.close(self)
        MiniLang_Base.close(self)

    def start_case(self, index : int):
        """
        index is the index of the case in the PISA dataset, from 0 to 2999
        """
        try:
            pos = self.proof_pos_of(index)
        except KeyError:
            raise CaseNotAvailable(index, f"MiniLang_PISA: case {index} not available")
        try:
            self.move_to(pos.file, pos.line, pos.column)
        except REPLFail as E:
            raise CaseNotAvailable(index, f"MiniLang_PISA: case {index} not available")
    
class MiniLang_AFP(MiniLang_Base, AFP_Data):

    def __init__(self, addr, *args, **kwargs):
        MiniLang_Base.__init__(self, addr, *args, **kwargs)
        AFP_Data.__init__(self)

    def __enter__(self):
        AFP_Data.__enter__(self)
        MiniLang_Base.__enter__(self)
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        AFP_Data.__exit__(self, exc_type, exc_value, traceback)
        MiniLang_Base.__exit__(self, exc_type, exc_value, traceback)
        return None

    def close(self):
        AFP_Data.close(self)
        MiniLang_Base.close(self)

    def start_case(self, index : Position):
        try:
            pos = self.proof_pos_of(index)
        except KeyError:
            raise CaseNotAvailable(index, f"MiniLang_AFP: case {index} not available")
        try:
            self.move_to(pos.file, pos.line, pos.column)
        except REPLFail as E:
            raise CaseNotAvailable(index, f"MiniLang_AFP: case {index} not available")

class Isar_Base(Evaluator):

    def __init__(self, addr, libs=[]):
        self.addr = addr
        self.repl = Client(addr, 'HOL')
        self.repl.record_state("init")
        if libs:
            self.repl.add_lib(libs)

    def __enter__(self):
        self.repl.__enter__()
        super().__enter__()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.repl.__exit__(exc_type, exc_value, traceback)
        super().__exit__(exc_type, exc_value, traceback)
        return None

    def close(self):
        self.repl.close()

    def move_to(self, file, line, column=0):
        self.repl.rollback("init")
        self.repl.file (os.path.abspath(file), line, column, cache_position=False, use_cache=False)
    
    def reset_eval(self, src):
        self.repl.rollback("init")
        self.repl.eval(src)

    def validate(self, index, src):
        try:
            self.start_case(index)
        except CaseNotAvailable:
            return Result(Status.CASE_NOT_AVAILABLE, None)
        try:
            response, error = self.repl.eval(src, timeout=900000, cmd_timeout=15000)
            if error:
                return Result(Status.FAIL, error)
            elif response and not response[-1][3][3]:
                return Result(Status.SUCCESS, None)
            else:
                return Result(Status.FAIL, "Proof not finished")
        except REPLFail as E:
            return Result(Status.FAIL, E)
        except TimeoutError as E:
            return Result(Status.FAIL, E)

    def reset(self):
        if self.repl:
            self.repl.close()
        self.repl = Client(self.addr, 'HOL')
        self.repl.record_state("init")

class Isar_PISA(Isar_Base, PISA_Data):

    def __init__(self, addr, *args, **kwargs):
        Isar_Base.__init__(self, addr, *args, **kwargs)
        PISA_Data.__init__(self)

    def __exit__(self, exc_type, exc_value, traceback):
        PISA_Data.__exit__(self, exc_type, exc_value, traceback)
        Isar_Base.__exit__(self, exc_type, exc_value, traceback)
        return None
    
    def __enter__(self):
        PISA_Data.__enter__(self)
        Isar_Base.__enter__(self)
        return self

    def close(self):
        PISA_Data.close(self)
        Isar_Base.close(self)

    def start_case(self, index : int):
        pos = self.proof_pos_of(index)
        try:
            self.move_to(pos.file, pos.line, pos.column)
        except REPLFail as E:
            raise CaseNotAvailable(index, f"Isar_PISA: case {index} not available")

class Isar_AFP(Isar_Base, AFP_Data):

    def __init__(self, addr, *args, **kwargs):
        Isar_Base.__init__(self, addr, *args, **kwargs)
        AFP_Data.__init__(self)

    def __exit__(self, exc_type, exc_value, traceback):
        AFP_Data.__exit__(self, exc_type, exc_value, traceback)
        Isar_Base.__exit__(self, exc_type, exc_value, traceback)
        return None
    
    def __enter__(self):
        AFP_Data.__enter__(self)
        Isar_Base.__enter__(self)
        return self

    def close(self):
        AFP_Data.close(self)
        Isar_Base.close(self)

    def start_case(self, index : Position):
        pos = self.proof_pos_of(index)
        try:
            self.move_to(pos.file, pos.line, pos.column)
        except REPLFail as E:
            raise CaseNotAvailable(index, f"Isar_AFP: case {index} not available")

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

class MiniLang_MiniF2F(MiniLang_Base, MiniF2F_Data):

    def __init__(self, addr, *args, **kwargs):
        MiniLang_Base.__init__(self, addr, *args, **kwargs)
        MiniF2F_Data.__init__(self)

    def __exit__(self, exc_type, exc_value, traceback):
        MiniF2F_Data.__exit__(self, exc_type, exc_value, traceback)
        MiniLang_Base.__exit__(self, exc_type, exc_value, traceback)
        return None

    def __enter__(self):
        MiniF2F_Data.__enter__(self)
        MiniLang_Base.__enter__(self)
        return self
    
    def close(self):
        MiniF2F_Data.close(self)
        MiniLang_Base.close(self)

    def start_case(self, index : Tuple[str, str]):
        category, idx = index
        if category not in ["test", "valid"]:
            raise ValueError(f"Isar_MiniF2F: only support test and valid category") 
        dataset = get_MINIF2F_VALIDATION() if category == "valid" else get_MINIF2F_TEST()
        try:
            src = dataset[idx]
        except KeyError:
            raise CaseNotAvailable(f"MiniLang_MiniF2F: case {index} not available")
        try:
            self.reset_eval(src)
        except REPLFail as E:
            raise CaseNotAvailable(f"MiniLang_MiniF2F: case {index} not available")

class Isar_MiniF2F(Isar_Base, MiniF2F_Data):

    def __init__(self, addr, *args, **kwargs):
        Isar_Base.__init__(self, addr, *args, **kwargs)
        MiniF2F_Data.__init__(self)

    def __exit__(self, exc_type, exc_value, traceback):
        MiniF2F_Data.__exit__(self, exc_type, exc_value, traceback)
        Isar_Base.__exit__(self, exc_type, exc_value, traceback)
        return None
    
    def __enter__(self):
        MiniF2F_Data.__enter__(self)
        Isar_Base.__enter__(self)
        return self
    
    def close(self):
        MiniF2F_Data.close(self)
        Isar_Base.close(self)

    def start_case(self, index : Tuple[str, str]):
        category, idx = index
        if category not in ["test", "valid"]:
            raise ValueError(f"Isar_MiniF2F: only support test and valid category") 
        dataset = get_MINIF2F_VALIDATION() if category == "valid" else get_MINIF2F_TEST()
        try:
            src = dataset[idx]
        except KeyError:
            raise CaseNotAvailable(f"Isar_MiniF2F: case {index} not available")
        try:
            self.reset_eval(src)
        except REPLFail as E:
            raise CaseNotAvailable(f"Isar_MiniF2F: case {index} not available")

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

def report_evaluation(response_path : str, result_path : str):
    responses = {}
    with open(response_path, "r", encoding="utf-8") as f:
        for line in f:
            data = json.loads(line)
            responses[str(data["index"])] = data["response"]
    with open(result_path + '.csv', "w", encoding="utf-8") as f:
        csv_writer = csv.writer(f)
        csv_writer.writerow(["index", "status", "error", "response"])
        with SqliteDict(result_path) as db:
            for key, result in db.items():
                csv_writer.writerow([key, result.status, result.error, responses[key]])

def evaluate_and_save(result_path : str, cases : list[Case], evaluator : Evaluator): # -> Dict[Index, Result]
    # Setup shared variables with thread-safe access
    success = 0
    unavailable = 0
    total = 0
    results = {}
    lock = threading.Lock()

    # Create a task queue from all cases
    task_queue = queue.Queue()
    for case in cases:
        task_queue.put(case)

    remaining_cases = task_queue.qsize()
    def log_state():
        nonlocal remaining_cases
        with lock:
            success_rate = success / (total-unavailable) if total - unavailable > 0 else 0
            unavailable_rate = unavailable / total if total > 0 else 0
            logger.info(f"Success: {success_rate:.3f}, Unavailable: {unavailable_rate:.3f}, Remaining: {remaining_cases}")


    logger.info(f"Starting {evaluator.__name__} evaluation of {len(cases)} cases. The result will be saved to {result_path}")
    with SqliteDict(result_path, autocommit=True) as db:
        def eval_server(server_addr):
            nonlocal success, unavailable, total, results, remaining_cases
            while not task_queue.empty():
                logger.info(f"Connecting to server {server_addr}")
                try:
                    with evaluator(server_addr) as test:
                        while True:
                            try:
                                # Get next task from queue with timeout
                                case : Case = task_queue.get(timeout=1)
                            except queue.Empty:
                                if remaining_cases == 0:
                                    return
                                else:
                                    time.sleep(1)
                                    continue
                            
                            try:
                                logger.info(f"Server {server_addr} evaluating {case.index}")
                                
                                # Check if result already exists in database
                                if case.index in db and db[case.index].status != Status.CASE_NOT_AVAILABLE:
                                    result = db[case.index]
                                else:
                                    try:
                                        result = test.validate(case.index, case.code)
                                        db[case.index] = result
                                    except REPLFail as E:
                                        logger.error(f"REPLFail error @ {case.index}: {E}")
                                        result = Result(Status.FAIL, str(E))
                                        db[case.index] = result
                                        try:
                                            test.reset()
                                        except REPLFail as E:
                                            break
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
                                if result.status == Status.SUCCESS:
                                    success += 1
                                elif result.status == Status.CASE_NOT_AVAILABLE:
                                    unavailable += 1

                                remaining_cases -= 1
                                total += 1
                                results[case.index] = result

                            log_state()
                            if result.status == Status.CASE_NOT_AVAILABLE:
                                break

                except ConnectionRefusedError:
                    logger.error(f"Fail to connect to {server_addr}. Retrying in 60 seconds...")
                    time.sleep(60)
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

