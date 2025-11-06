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
import traceback
from tools.server import SERVERS
from typing import Callable, Tuple
import msgpack as mp

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
    def __init__(self, status : Status, errors : list[Exception | str], elapsed_time : list[float]):
        self.status = status
        self.errors = errors
        self.elapsed_time = elapsed_time

    def __str__(self):
        return f"{self.status} ({self.elapsed_time}) {self.errors}"

class Case:
    def __init__(self, index, code : str | list[str]):
        if not isinstance(code, str) and not isinstance(code, list):
            raise TypeError(f"code must be a string or a list, but got {type(code)}")
        self.index = index
        self.code = code

    @staticmethod
    def jsonl(response_path):
        ret = []
        with open(response_path, "r", encoding="utf-8") as f: 
                for line in f:
                    data = json.loads(line)
                    if "response" in data:
                        proofs = data["response"]
                    elif "responses" in data:
                        proofs = data["responses"]
                    else:
                        raise Exception("What the fuck where is my response?")
                    if not isinstance(proofs, list):
                        proofs = [proofs]
                    def filter(prf):
                        if prf.startswith('PROOF:\n'):
                            return prf[7:]
                        else:
                            return prf
                    ret.append(Case(data["index"], [filter(p) for p in proofs]))
        return ret

class Evaluator:
    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        return None
    
    def all_cases(self): # -> enumerate[Index]:
        raise NotImplementedError("all_cases must be implemented by subclass")

    def validate(self, index, proofs : str | list[str]) -> Result:
        """
        When proofs is a list:
          This method evaluates the proofs sequentially from the first to the last.
          The method returns success immediately once the first successful proof is found.
          If the method returns after evaluating the n-th proof,
          the returned result.errors is a list {E_i}_(i<n) containing the failure reason E_i
          for every previous i-th proof. E_i is either a string or an exception.
        When proofs is a string:
          The returned result.errors is either None if the proof succeeds, or a string or exception
          explaining why the proof fails.
        """
        raise NotImplementedError("validate must be implemented by subclass")
    
    def start_case(self, index) -> None:
        raise NotImplementedError("start_case must be implemented by subclass")

class MiniLang_Base(Evaluator):
    def __init__(self, addr, timeout=500, connection_timeout=1200, *args, **kwargs):
        self.addr = addr
        self._timeout = timeout
        self.mini = Mini(self.addr, 'HOL', ML_base_injection=False, timeout=max(connection_timeout, timeout + 20), *args, **kwargs)

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
    
    def validate(self, index, proofs):
        try:
            self.start_case(index)
        except CaseNotAvailable:
            return Result(Status.CASE_NOT_AVAILABLE, ["Case not available"], [])
        if isinstance(proofs, str):
            proofs = [proofs]
        if len(proofs) > 1:
            self.mini.record('EVAL')
        errors = []
        times = []
        for i, code in enumerate(proofs):
            if i > 0:
                self.mini.rollback('EVAL')
            start_time = time.time()
            try:
                _, finished = self.mini.eval(code, self._timeout * 1000, timeout_cmd=5000)
                times.append(time.time() - start_time)
                if finished:
                    return Result(Status.SUCCESS, errors, times)
                else:
                    errors.append("Proof not finished")
            except REPLFail as E:
                times.append(time.time() - start_time)
                errors.append(E)
            except TimeoutError as E:
                times.append(time.time() - start_time)
                errors.append(E)
        return Result(Status.FAIL, errors, times)

    def move_to(self, file, line, column):
        file = os.path.abspath(file)
        self.mini.move_to(file, line, column)

    def reset_eval(self, src):
        self.mini.set_theory_and_goal(src)

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
        except CaseNotAvailable:
            logger.error(f"Case Not Available: {index} AAAAAA")
            raise
        except KeyError:
            logger.error(f"Case Not Available: {index} is not in the dateset")
            raise CaseNotAvailable(index, f"MiniLang_PISA: case {index} not available")
        try:
            self.move_to(pos.file, pos.line, pos.column)
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(index, f"MiniLang_PISA: case {index} not available")
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
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
            logger.error(f"Case Not Available: {index} is not in the dateset")
            raise CaseNotAvailable(index, f"MiniLang_AFP: case {index} not available")
        try:
            self.move_to(pos.file, pos.line, pos.column)
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(index, f"MiniLang_AFP: case {index} not available")
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(index, f"MiniLang_AFP: case {index} not available")

class MiniLang(MiniLang_Base):

    def start_case(self, index : str):
        """
        index is a string of format <file>:<line>:[column]
        """
        match index.split(':'):
            case (file, line, column):
                pass
            case (file, line):
                column = 0
            case _:
                raise ValueError(f"Invalid index: {index}")
        try:
            self.move_to(file, int(line), int(column))
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(index, f"MiniLang: case {index} not available")
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(index, f"MiniLang: case {index} not available")

import re

class Isar_Base(Evaluator):

    def __init__(self, addr, libs=[], timeout=500, connection_timeout=1200):
        self.addr = addr
        self.repl = Client(addr, 'HOL', timeout=max(connection_timeout, timeout + 20))
        self._timeout = timeout
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

    def validate(self, index, proofs):
        try:
            self.start_case(index)
        except CaseNotAvailable:
            return Result(Status.CASE_NOT_AVAILABLE, ["Case not available"], [])
        if isinstance(proofs, str):
            proofs = [proofs]
        if len(proofs) > 1:
            self.repl.record_state('EVAL')
        errors = []
        times = []
        for i, code in enumerate(proofs):
            if i > 0:
                self.repl.rollback('EVAL')
            try:
                has_sorry = self.contains_sorry(code)
                start_time = time.time()
                if has_sorry:
                    error = 'Contains sorry'
                    response = None
                else:
                    response, error = self.repl.eval(code, timeout=self._timeout * 1000, cmd_timeout=15000)
                times.append(time.time() - start_time)
                if error:
                    errors.append(error)
                elif response and not response[-1][3][3]:
                    return Result(Status.SUCCESS, errors, times)
                else:
                    errors.append("Proof not finished")
            except REPLFail as E:
                errors.append(E)
            except TimeoutError as E:
                errors.append(E)
        return Result(Status.FAIL, errors, times)

    @classmethod
    def locate_proof_goal(cls, file : str):
        line_num = 0
        with open(file, "r", encoding="utf-8") as f:
            for i, line in enumerate(f, 1):
                if line.strip() == "sorry":
                    if line_num == 0:
                        line_num = i
                    else:
                        return None
        return line_num if line_num > 0 else None
    
    @classmethod
    def filter_comment(cls, code):
        output = []
        comment_level = 0 
        for i, c in enumerate(code):
            if c == '(' and i+1 < len(code) and code[i+1] == '*':
                comment_level += 1
            if comment_level == 0:
                output.append(c)
            elif c == ')' and i > 0 and code[i-1] == '*':
                comment_level -= 1
        return ''.join(output)

    @classmethod
    def contains_sorry(cls, code):
        if '(*' in code:
            code = cls.filter_comment(code)
        # Check for \<sorry\> or \<admitted\> in the code using regex
        if re.search(r'\bsorry\b', code) or re.search(r'\badmit\b', code):
            return True
        return False

class MinilangAgent_Base(Isar_Base):
    def __init__(self, addr, timeout=500, connection_timeout=1200,
                step_limit=30, parallel_runs=1, query_ret_num=30):
        self._budget = (step_limit, timeout, parallel_runs, query_ret_num)
        super().__init__(addr, timeout=timeout, connection_timeout=connection_timeout, libs=[])
        self.repl.set_trace(False)
        self.repl.load_theory(['Minilang_Agent.Minilang_Agent'])

    def validate(self, index, proofs):
        try:
            self.start_case(index)
        except CaseNotAvailable:
            return Result(Status.CASE_NOT_AVAILABLE, ["Case not available"], [])
        if isinstance(proofs, str):
            proofs = [proofs]
        elif isinstance(proofs, list) and all(isinstance(p, str) for p in proofs):
            pass
        else:
            raise ValueError(f"Invalid proofs: {proofs}")

        errors = []
        times = []
        for i, driver in enumerate(proofs):
            if i > 0:
                self.repl.rollback('EVAL')
            try:
                self.repl.run_app('MiniLang_Agent')
                mp.pack((driver, self._budget), self.repl.cout)
                self.repl.cout.flush()
                (success, elapsed, cpu_time) = Client._parse_control_(self.repl.unpack.unpack())
                times.append(elapsed)
                if success:
                    return Result(Status.SUCCESS, errors, times)
                else:
                    errors.append(f"Driver {driver} fails")
            except REPLFail as E:
                errors.append(E)
            except TimeoutError as E:
                errors.append(E)
        return Result(Status.FAIL, errors, times)


class REPL_PISA_Mixin:
    def start_case(self, index : int):
        try:
            pos = self.proof_pos_of(index)
        except KeyError:
            logger.error(f"Case Not Available: {index} is not in the dateset")
            raise CaseNotAvailable(index, f"Isar_PISA: case {index} not available")
        try:
            self.move_to(pos.file, pos.line, pos.column)
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(index, f"Isar_PISA: case {index} not available")
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(index, f"Isar_PISA: case {index} not available")

class Isar_PISA(REPL_PISA_Mixin, Isar_Base, PISA_Data):

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


class MinilangAgent_PISA(REPL_PISA_Mixin, MinilangAgent_Base, PISA_Data):
    def __init__(self, addr, *args, **kwargs):
        MinilangAgent_Base.__init__(self, addr, *args, **kwargs)
        PISA_Data.__init__(self)

    def __exit__(self, exc_type, exc_value, traceback):
        PISA_Data.__exit__(self, exc_type, exc_value, traceback)
        MinilangAgent_Base.__exit__(self, exc_type, exc_value, traceback)
        return None
    
    def __enter__(self):
        PISA_Data.__enter__(self)
        MinilangAgent_Base.__enter__(self)
        return self

    def close(self):
        PISA_Data.close(self)
        MinilangAgent_Base.close(self)

class REPL_AFP_Mixin:

    def start_case(self, index : Position):
        try:
            pos = self.proof_pos_of(index)
        except KeyError:
            logger.error(f"Case Not Available: {index} is not in the dateset")
            raise CaseNotAvailable(index, f"Isar_AFP: case {index} not available")
        try:
            self.move_to(pos.file, pos.line, pos.column)
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(index, f"Isar_AFP: case {index} not available")
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(index, f"Isar_AFP: case {index} not available")


class Isar_AFP(REPL_AFP_Mixin, Isar_Base, AFP_Data):

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


class MinilangAgent_AFP(REPL_AFP_Mixin, MinilangAgent_Base, AFP_Data):

    def __init__(self, addr, *args, **kwargs):
        MinilangAgent_Base.__init__(self, addr, *args, **kwargs)
        AFP_Data.__init__(self)

    def __exit__(self, exc_type, exc_value, traceback):
        AFP_Data.__exit__(self, exc_type, exc_value, traceback)
        MinilangAgent_Base.__exit__(self, exc_type, exc_value, traceback)
        return None
    
    def __enter__(self):
        AFP_Data.__enter__(self)
        MinilangAgent_Base.__enter__(self)
        return self

    def close(self):
        AFP_Data.close(self)
        MinilangAgent_Base.close(self)


class REPL_FileLine_Mixin:

    def start_case(self, index : str):
        """
        index is a string of format <file>:<line>:[column]
        """
        match index.split(':'):
            case (file, line, column):
                pass
            case (file, line):
                column = 0
            case (file,):
                if file.startswith("data"):
                    file = "/home/xero/Current/NTP4Verif/" + file
                line = type(self).locate_proof_goal(file)
                if line is None:
                    raise ValueError(f"Invalid index: {index}")
                column = 0
        try:
            self.move_to(file, int(line), int(column))
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(index, f"Isar: case {index} not available")
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(index, f"Isar: case {index} not available")
    

class Isar(REPL_FileLine_Mixin, Isar_Base):
    pass

class MinilangAgent(REPL_FileLine_Mixin, MinilangAgent_Base):
    pass


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

class MiniF2F_Mixin:
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._data = MiniF2F_Data()

    def start_case(self, index : str):
        try:
            src = self._data.prelude_and_statement_of(index)
        except KeyError:
            logger.error(f"Case Not Available: {index} is not in the dateset")
            raise CaseNotAvailable(f"{self.__class__.__name__}: case {index} not available")
        try:
            self.reset_eval(src)
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(f"{self.__class__.__name__}: case {index} not available")
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(f"{self.__class__.__name__}: case {index} not available")

class MiniLang_MiniF2F(MiniF2F_Mixin, MiniLang_Base):
    pass

class Isar_MiniF2F(MiniF2F_Mixin, Isar_Base):
    pass

class MinilangAgent_MiniF2F(MiniF2F_Mixin, MinilangAgent_Base):
    pass

class SourceText_Mixin:
    def start_case(self, index : str):
        try:
            self.reset_eval(index)
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(f"{self.__class__.__name__}: case {index} not available")
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(f"{self.__class__.__name__}: case {index} not available")

class MiniLang_Source(SourceText_Mixin, MiniLang_Base):
    pass

class Isar_Source(SourceText_Mixin, Isar_Base):
    pass

class MinilangAgent_Source(SourceText_Mixin, MinilangAgent_Base):
    pass

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
            if "response" in data:
                prf = data["response"]
            elif "responses" in data:
                prf = data["responses"]
            else:
                raise Exception ("No responses field")
            responses[str(data["index"])] = prf
    with open(result_path + '.csv', "w", encoding="utf-8") as f:
        csv_writer = csv.writer(f)
        csv_writer.writerow(["index", "status", "pass", "elapsed time", "error", "response"])
        with SqliteDict(result_path) as db:
            for key, result in db.items():
                try:
                    err = '\n\n'.join([str(e) for e in result.errors])
                except AttributeError:
                    err = result.error
                csv_writer.writerow([key, result.status, len(result.errors), str(result.elapsed_time), err, responses[key]])

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
            logger.info(f"Success: {success_rate:.5f}, Unavailable: {unavailable_rate:.5f}, Remaining: {remaining_cases}")


    logger.info(f"Starting {evaluator.__name__} evaluation of {len(cases)} cases. The result will be saved to {result_path}")
    with SqliteDict(result_path) as db:
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
                                        db.commit()
                                    except REPLFail as E:
                                        logger.error(f"REPLFail error @ {case.index}: {E}")
                                        result = Result(Status.CASE_NOT_AVAILABLE, [str(E)], [])
                                        db[case.index] = result
                                        db.commit()
                                        break
                            except Exception as e:
                                logger.error(f"Error processing case {case.index}: {str(e)}")
                                logger.error(f"Traceback:\n{traceback.format_exc()}")
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

