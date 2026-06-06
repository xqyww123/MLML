import json
import os
import sys
from IsaREPL import Client, Position, REPLFail
from IsaMini.REPL import REPL as MiniREPL
import csv
import logging
from typing import TypedDict
from enum import Enum
from data.isabelle import CaseNotAvailable, PISA_Data, get_MINIF2F_VALIDATION, get_MINIF2F_TEST, MiniF2F_Data, AFP_Data, PutnamBench_Data, NTPVC_Data
from sqlitedict import SqliteDict
import asyncio
import time
import traceback
from tools.server import SERVERS
from typing import Callable, Tuple, TYPE_CHECKING
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
    def __init__(self, status : Status, errors : list[Exception | str], elapsed_time : list[float], data : dict | None = None):
        self.status = status
        self.errors = errors
        self.elapsed_time = elapsed_time
        self.data = data

    def __str__(self):
        s = f"{self.status} ({self.elapsed_time}) {self.errors}"
        if self.data:
            s += f" data={self.data}"
        return s

    def __getattr__(self, name):
        if name == 'data':
            return None
        raise AttributeError(f"'Result' object has no attribute {name!r}")

class AgentCostData(TypedDict, total=False):
    input_tokens: int
    cache_creation_tokens: int
    cache_read_tokens: int
    output_tokens: int
    cost_usd: float
    tool_calls: int
    api_requests: int
    elapsed: int
    model_time: float
    isabelle_time: float
    quota_wait_time: float

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
    async def __aenter__(self):
        return self

    async def __aexit__(self, exc_type, exc_value, traceback):
        return None

    def all_cases(self): # -> enumerate[Index]:
        raise NotImplementedError("all_cases must be implemented by subclass")

    async def validate(self, index, proofs : str | list[str]) -> Result:
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

    async def start_case(self, index) -> None:
        raise NotImplementedError("start_case must be implemented by subclass")

class MiniLang_Base(Evaluator):
    def __init__(self, addr, timeout=500, connection_timeout=1200, *args, **kwargs):
        self.addr = addr
        self._timeout = timeout
        self._connection_timeout = connection_timeout
        self._args = args
        self._kwargs = kwargs
        self.mini: MiniREPL = None  # type: ignore[assignment]  # set in __aenter__

    async def __aenter__(self):
        self.mini = MiniREPL(self.addr, 'HOL', ML_base_injection=False,
                        timeout=max(self._connection_timeout, self._timeout + 20),
                        *self._args, **self._kwargs)
        await self.mini.__aenter__()
        await super().__aenter__()
        return self

    async def __aexit__(self, exc_type, exc_value, traceback):
        if self.mini:
            await self.mini.__aexit__(exc_type, exc_value, traceback)
            self.mini = None  # type: ignore[assignment]
        await super().__aexit__(exc_type, exc_value, traceback)
        return None

    async def close(self):
        if self.mini:
            await self.mini.close()
            self.mini = None  # type: ignore[assignment]

    async def validate(self, index, proofs):
        try:
            await self.start_case(index)
        except CaseNotAvailable:
            return Result(Status.CASE_NOT_AVAILABLE, ["Case not available"], [])
        if isinstance(proofs, str):
            proofs = [proofs]
        if len(proofs) > 1:
            await self.mini.record('EVAL')
        errors = []
        times = []
        for i, code in enumerate(proofs):
            if i > 0:
                await self.mini.rollback('EVAL')
            start_time = time.time()
            try:
                _, finished = await self.mini.eval(code, self._timeout * 1000, timeout_cmd=5000)
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

    async def move_to(self, file, line, column):
        file = os.path.abspath(file)
        await self.mini.move_to(file, line, column)

    async def reset_eval(self, src):
        await self.mini.set_theory_and_goal(src)

class MiniLang_PISA(MiniLang_Base, PISA_Data):

    def __init__(self, addr, *args, **kwargs):
        MiniLang_Base.__init__(self, addr, *args, **kwargs)
        PISA_Data.__init__(self)

    async def __aexit__(self, exc_type, exc_value, traceback):
        await PISA_Data.__aexit__(self, exc_type, exc_value, traceback)
        await MiniLang_Base.__aexit__(self, exc_type, exc_value, traceback)
        return None

    async def __aenter__(self):
        await PISA_Data.__aenter__(self)
        await MiniLang_Base.__aenter__(self)
        return self

    async def close(self):
        await PISA_Data.close(self)
        await MiniLang_Base.close(self)

    async def start_case(self, index : int):
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
            await self.move_to(pos.file, pos.line, pos.column)
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

    async def __aenter__(self):
        await AFP_Data.__aenter__(self)
        await MiniLang_Base.__aenter__(self)
        return self

    async def __aexit__(self, exc_type, exc_value, traceback):
        await AFP_Data.__aexit__(self, exc_type, exc_value, traceback)
        await MiniLang_Base.__aexit__(self, exc_type, exc_value, traceback)
        return None

    async def close(self):
        await AFP_Data.close(self)
        await MiniLang_Base.close(self)

    async def start_case(self, index : Position):
        try:
            pos = self.proof_pos_of(index)
        except KeyError:
            logger.error(f"Case Not Available: {index} is not in the dateset")
            raise CaseNotAvailable(index, f"MiniLang_AFP: case {index} not available")
        try:
            await self.move_to(pos.file, pos.line, pos.column)
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(index, f"MiniLang_AFP: case {index} not available")
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(index, f"MiniLang_AFP: case {index} not available")

class MiniLang(MiniLang_Base):

    async def start_case(self, index : str):
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
            await self.move_to(file, int(line), int(column))
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
        self._libs = libs
        self._timeout = timeout
        self._connection_timeout = connection_timeout
        self.repl: Client = None  # type: ignore[assignment]  # set in __aenter__

    async def __aenter__(self):
        self.repl = Client(self.addr, 'HOL', timeout=max(self._connection_timeout, self._timeout + 20))
        await self.repl.__aenter__()
        await self.repl.record_state("init")
        if self._libs:
            await self.repl.add_lib(self._libs)
        await super().__aenter__()
        return self

    async def __aexit__(self, exc_type, exc_value, traceback):
        if self.repl:
            await self.repl.__aexit__(exc_type, exc_value, traceback)
        await super().__aexit__(exc_type, exc_value, traceback)
        return None

    async def close(self):
        if self.repl:
            self.repl.close()

    async def move_to(self, file, line, column=0):
        await self.repl.rollback("init")
        await self.repl.file(os.path.abspath(file), line, column, cache_position=False, use_cache=False)

    async def reset_eval(self, src):
        await self.repl.rollback("init")
        await self.repl.eval(src)

    async def validate(self, index, proofs):
        try:
            await self.start_case(index)
        except CaseNotAvailable:
            return Result(Status.CASE_NOT_AVAILABLE, ["Case not available"], [])
        if isinstance(proofs, str):
            proofs = [proofs]
        if len(proofs) > 1:
            await self.repl.record_state('EVAL')
        errors = []
        times = []
        for i, code in enumerate(proofs):
            if i > 0:
                await self.repl.rollback('EVAL')
            try:
                has_sorry = self.contains_sorry(code)
                start_time = time.time()
                if has_sorry:
                    errors.append('Contains sorry')
                    response = None
                else:
                    try:
                        response = await self.repl.eval(code, timeout=self._timeout * 1000, cmd_timeout=15000)
                    except REPLFail as E:
                        errors.append(E)
                        times.append(time.time() - start_time)
                        continue
                times.append(time.time() - start_time)
                if response and not response[-1].flags.has_goal:
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
    def _strip_comments(cls, code):
        if '(*' in code:
            code = cls.filter_comment(code)
        return code

    @classmethod
    def contains_sorry(cls, code, original_code=None):
        code = cls._strip_comments(code)
        if re.search(r'\bsorry\b', code) or re.search(r'\badmit\b', code) or re.search(r'\boops\b', code):
            return True
        if re.search(r'\\<proof>', code):
            return True
        if re.search(r'Skip_Proof|cheat_tac', code):
            return True
        orig_count = len(re.findall(r'\baxiomatization\b', cls._strip_comments(original_code))) if original_code else 0
        if len(re.findall(r'\baxiomatization\b', code)) > orig_count:
            return True
        return False

class MinilangAgent_Base(Isar_Base):
    # Extra Isabelle libraries loaded into the REPL before evaluation.
    # Subclasses may override to change the loaded libraries (e.g. NTP4VC must
    # not load MathBench_Prover, whose huge math corpus pollutes the namespace).
    _LIBS = ['MathBench_Prover.MathBench_Prover', 'Minilang_Agent.Minilang_Agent']

    _invocation_serial = 0
    _invocation_serial_lock = asyncio.Lock()

    @classmethod
    async def _make_invocation_id(cls):
        async with cls._invocation_serial_lock:
            cls._invocation_serial += 1
            serial = cls._invocation_serial
        ms = int(time.time() * 1000)
        hex_ms = format(ms, 'x')
        return f"{hex_ms[-9:]}_{format(serial, 'x')}"

    def __init__(self, addr, timeout=500, connection_timeout=1200,
                timeout_seconds=14400, max_tool_calls=10000, max_retries=8,
                log_dir=None, retrieval_forking=None, interactive_retrieval=None,
                auto_interpret_for_embedding=False):
        super().__init__(addr, libs=type(self)._LIBS,
                         timeout=max(60, timeout_seconds), connection_timeout=max(60, timeout_seconds))
        self._cfg = auto_interpret_for_embedding
        self._budget = (timeout_seconds, max_tool_calls, max_retries)
        self._log_dir = log_dir
        self._retrieval_forking = retrieval_forking
        self._interactive_retrieval = interactive_retrieval

    async def __aenter__(self):
        await super().__aenter__()
        await self.repl.set_trace(False)
        return self

    async def validate(self, index, proofs):
        try:
            await self.start_case(index)
        except CaseNotAvailable:
            return Result(Status.CASE_NOT_AVAILABLE, ["Case not available"], [])
        if isinstance(proofs, str):
            proofs = [proofs]
        elif isinstance(proofs, list) and all(isinstance(p, str) for p in proofs):
            pass
        else:
            raise ValueError(f"Invalid proofs: {proofs}")

        # Isabelle's AoA_use_proof_cache defaults to true (the AoA driver looks up
        # a previously cached proof for the goal). Disable it for all agent
        # evaluations so every case is solved by a fresh agent run rather than a
        # cache hit. Declared on the open proof context before record_state so the
        # EVAL snapshot carries it and pass@N rollbacks preserve it.
        await self.repl.config(['AoA_use_proof_cache = false'])

        if len(proofs) > 1:
            await self.repl.record_state('EVAL')
        errors = []
        times = []
        costs = []
        log_ids = []
        for i, driver in enumerate(proofs):
            if i > 0:
                await self.repl.rollback('EVAL')
            try:
                await self.repl.run_app('Minilang.AoA')
                invocation_id = await self._make_invocation_id()
                log_ids.append(invocation_id)
                await self.repl._write((
                    invocation_id, driver,
                    (self._cfg, self._budget), self._log_dir,
                    self._retrieval_forking, self._interactive_retrieval
                ))
                (status, elapsed, cpu_time, detail, cost_tuple) = Client._parse_control_(await self.repl._feed_and_unpack())
                times.append(elapsed)
                cost_data: AgentCostData = {
                    "input_tokens": cost_tuple[0],
                    "cache_creation_tokens": cost_tuple[1],
                    "cache_read_tokens": cost_tuple[2],
                    "output_tokens": cost_tuple[3],
                    "cost_usd": cost_tuple[4],
                    "tool_calls": cost_tuple[5],
                    "api_requests": -1,
                    "elapsed": elapsed,
                    "isabelle_time": cost_tuple[6],
                    "model_time": cost_tuple[7],
                    "quota_wait_time": cost_tuple[8],
                }
                costs.append(cost_data)
                if status == "success":
                    return Result(Status.SUCCESS, errors, times, data={"log_ids": log_ids, "costs": costs})
                elif status == "remote_error":
                    det = f": {detail}" if detail else ""
                    errors.append(f"Driver {driver}: remote calling failure{det} (elapsed={elapsed}ms, cpu={cpu_time}ms)")
                elif status in ("surrender", "refute", "resource_exhausted"):
                    det = f": {detail}" if detail else ""
                    errors.append(f"Driver {driver}: {status}{det} (elapsed={elapsed}ms, cpu={cpu_time}ms)")
                else:
                    errors.append(f"Driver {driver}: unknown status '{status}' (elapsed={elapsed}ms, cpu={cpu_time}ms)")
            except REPLFail as E:
                if E.args[0].startswith("Failed to launch the Agent Manager."):
                    raise
                else:
                    errors.append(E)
            except TimeoutError as E:
                errors.append(E)
        return Result(Status.FAIL, errors, times, data={"log_ids": log_ids, "costs": costs})


class REPL_PISA_Mixin:
    if TYPE_CHECKING:
        def proof_pos_of(self, index: int) -> Position: ...
        async def move_to(self, file: str, line: int, column: int = 0) -> None: ...

    async def start_case(self, index : int):
        try:
            pos = self.proof_pos_of(index)
        except KeyError:
            logger.error(f"Case Not Available: {index} is not in the dateset")
            raise CaseNotAvailable(index, f"Isar_PISA: case {index} not available")
        try:
            await self.move_to(pos.file, pos.line, pos.column)
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

    async def __aexit__(self, exc_type, exc_value, traceback):
        await PISA_Data.__aexit__(self, exc_type, exc_value, traceback)
        await Isar_Base.__aexit__(self, exc_type, exc_value, traceback)
        return None

    async def __aenter__(self):
        await PISA_Data.__aenter__(self)
        await Isar_Base.__aenter__(self)
        return self

    async def close(self):
        await PISA_Data.close(self)
        await Isar_Base.close(self)


class MinilangAgent_PISA(REPL_PISA_Mixin, MinilangAgent_Base, PISA_Data):

    def __init__(self, addr, *args, **kwargs):
        MinilangAgent_Base.__init__(self, addr, *args, **kwargs)
        PISA_Data.__init__(self)

    async def __aexit__(self, exc_type, exc_value, traceback):
        await PISA_Data.__aexit__(self, exc_type, exc_value, traceback)
        await MinilangAgent_Base.__aexit__(self, exc_type, exc_value, traceback)
        return None

    async def __aenter__(self):
        await PISA_Data.__aenter__(self)
        await MinilangAgent_Base.__aenter__(self)
        return self

    async def close(self):
        await PISA_Data.close(self)
        await MinilangAgent_Base.close(self)

class REPL_AFP_Mixin:
    if TYPE_CHECKING:
        def proof_pos_of(self, index: Position) -> Position: ...
        async def move_to(self, file: str, line: int, column: int = 0) -> None: ...

    async def start_case(self, index : Position):
        try:
            pos = self.proof_pos_of(index)
        except KeyError:
            logger.error(f"Case Not Available: {index} is not in the dateset")
            raise CaseNotAvailable(index, f"Isar_AFP: case {index} not available")
        try:
            await self.move_to(pos.file, pos.line, pos.column)
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

    async def __aexit__(self, exc_type, exc_value, traceback):
        await AFP_Data.__aexit__(self, exc_type, exc_value, traceback)
        await Isar_Base.__aexit__(self, exc_type, exc_value, traceback)
        return None

    async def __aenter__(self):
        await AFP_Data.__aenter__(self)
        await Isar_Base.__aenter__(self)
        return self

    async def close(self):
        await AFP_Data.close(self)
        await Isar_Base.close(self)


class MinilangAgent_AFP(REPL_AFP_Mixin, MinilangAgent_Base, AFP_Data):

    def __init__(self, addr, *args, **kwargs):
        MinilangAgent_Base.__init__(self, addr, *args, **kwargs)
        AFP_Data.__init__(self)

    async def __aexit__(self, exc_type, exc_value, traceback):
        await AFP_Data.__aexit__(self, exc_type, exc_value, traceback)
        await MinilangAgent_Base.__aexit__(self, exc_type, exc_value, traceback)
        return None

    async def __aenter__(self):
        await AFP_Data.__aenter__(self)
        await MinilangAgent_Base.__aenter__(self)
        return self

    async def close(self):
        await AFP_Data.close(self)
        await MinilangAgent_Base.close(self)


class REPL_FileLine_Mixin:
    if TYPE_CHECKING:
        async def move_to(self, file: str, line: int, column: int = 0) -> None: ...
        @classmethod
        def locate_proof_goal(cls, file: str) -> int | None: ...

    async def start_case(self, index : str):
        """
        index is a string of format <file>:<line>:[column]
        """
        match index.split(':'):
            case (file, line, column):
                pass
            case (file, line):
                column = 0
            case (file,):
                line = type(self).locate_proof_goal(file)
                if line is None:
                    raise ValueError(f"Invalid index: {index}")
                column = 0
            case _:
                raise ValueError(f"Invalid index: {index}")
        try:
            await self.move_to(file, int(line), int(column))
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
    if TYPE_CHECKING:
        async def reset_eval(self, src: str) -> None: ...

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._data = MiniF2F_Data()

    async def start_case(self, index : str):
        try:
            src = self._data.prelude_and_statement_of(index)
        except KeyError:
            logger.error(f"Case Not Available: {index} is not in the dataset")
            raise CaseNotAvailable(index, f"MiniF2F: case {index} not available")
        try:
            await self.reset_eval(src)
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(index, f"MiniF2F: case {index} not available")
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(index, f"MiniF2F: case {index} not available")

class MiniLang_MiniF2F(MiniF2F_Mixin, MiniLang_Base):
    pass

class Isar_MiniF2F(MiniF2F_Mixin, Isar_Base):
    pass

class MinilangAgent_MiniF2F(MiniF2F_Mixin, MinilangAgent_Base):
    pass

class PutnamBench_Mixin:
    if TYPE_CHECKING:
        async def reset_eval(self, src: str) -> None: ...

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._data = PutnamBench_Data()

    async def start_case(self, index: str):
        try:
            src = self._data.prelude_and_statement_of(index)
        except KeyError:
            logger.error(f"Case Not Available: {index} is not in the dataset")
            raise CaseNotAvailable(index, f"PutnamBench: case {index} not available")
        try:
            await self.reset_eval(src)
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(index, f"PutnamBench: case {index} not available")
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(index, f"PutnamBench: case {index} not available")

class MiniLang_PutnamBench(PutnamBench_Mixin, MiniLang_Base):
    pass

class Isar_PutnamBench(PutnamBench_Mixin, Isar_Base):
    pass

class MinilangAgent_PutnamBench(PutnamBench_Mixin, MinilangAgent_Base):
    pass

class SourceText_Mixin:
    if TYPE_CHECKING:
        async def reset_eval(self, src: str) -> None: ...

    async def start_case(self, index : str):
        try:
            await self.reset_eval(index)
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(index, f"SourceText: case {index} not available")
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(index, f"SourceText: case {index} not available")

class MiniLang_Source(SourceText_Mixin, MiniLang_Base):
    pass

class Isar_Source(SourceText_Mixin, Isar_Base):
    pass

class MinilangAgent_Source(SourceText_Mixin, MinilangAgent_Base):
    pass

class NTPVC_Mixin:
    if TYPE_CHECKING:
        async def move_to(self, file: str, line: int, column: int = 0) -> None: ...
        @classmethod
        def locate_proof_goal(cls, file: str) -> int | None: ...

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._data = NTPVC_Data()

    async def start_case(self, index: str):
        try:
            file = self._data.file_of(index)
        except KeyError:
            logger.error(f"Case Not Available: {index} is not in the dataset")
            raise CaseNotAvailable(index, f"NTPVC: case {index} not available")
        line = type(self).locate_proof_goal(file)
        if line is None:
            raise CaseNotAvailable(index, f"NTPVC: no unique sorry in {index}")
        try:
            await self.move_to(file, line, 0)
        except TimeoutError as E:
            logger.error(f"Case Not Available: TimeoutError @ {index}: {E}")
            raise CaseNotAvailable(index, f"NTPVC: case {index} not available")
        except REPLFail as E:
            logger.error(f"Case Not Available: REPLFail error @ {index}: {E}")
            raise CaseNotAvailable(index, f"NTPVC: case {index} not available")

class Isar_NTPVC(NTPVC_Mixin, Isar_Base):
    pass

class MinilangAgent_NTPVC(NTPVC_Mixin, MinilangAgent_Base):
    # NTP4VC theorems are why3-generated and use short bound-variable names
    # (e.g. or, sl, sr) that collide with constants dragged in by
    # MathBench_Prover's math corpus. Load only the agent language.
    _LIBS = ['Minilang_Agent.Minilang_Agent']

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

async def evaluate_and_save(result_path : str | None, cases : list[Case], evaluator, retry_failure : bool = False, force_retry : frozenset = frozenset(), server_instances : list[str] | None = None, reverify_failures : bool = False): # -> Dict[Index, Result]
    # Setup shared variables with asyncio-safe access
    success = 0
    unavailable = 0
    total = 0
    results = {}
    lock = asyncio.Lock()

    # Create a task queue from all cases
    task_queue = asyncio.Queue()
    for case in cases:
        task_queue.put_nowait(case)

    remaining_cases = task_queue.qsize()
    async def log_state():
        nonlocal remaining_cases
        async with lock:
            success_rate = success / (total-unavailable) if total - unavailable > 0 else 0
            unavailable_rate = unavailable / total if total > 0 else 0
            logger.info(f"Success: {success_rate:.5f}, Unavailable: {unavailable_rate:.5f}, Remaining: {remaining_cases}")


    logger.info(f"Starting {getattr(evaluator, '__qualname__', getattr(evaluator, '__name__', repr(evaluator)))} evaluation of {len(cases)} cases. The result will be saved to {result_path}")
    async def execute(db):
        async def eval_server(server_addr):
            nonlocal success, unavailable, total, results, remaining_cases
            while not task_queue.empty():
                logger.info(f"Connecting to server {server_addr}")
                try:
                    test = evaluator(server_addr)
                    async with test:
                        while True:
                            try:
                                # Get next task from queue with timeout
                                case : Case = await asyncio.wait_for(task_queue.get(), timeout=1)
                            except asyncio.TimeoutError:
                                if remaining_cases == 0:
                                    return
                                else:
                                    await asyncio.sleep(1)
                                    continue

                            try:
                                logger.info(f"Server {server_addr} evaluating {case.index}")

                                # Check if result already exists in database
                                cached = db[case.index] if (db is not None and case.index in db) else None
                                if reverify_failures and cached is not None and cached.status == Status.FAIL and hasattr(test, "revalidate"):
                                    # Re-run ONLY the verification step on the proof a
                                    # prior run produced; do not re-run the agent.
                                    try:
                                        result = await test.revalidate(case.index, cached)
                                        if db is not None:
                                            db[case.index] = result
                                            db.commit()
                                    except REPLFail as E:
                                        logger.error(f"REPLFail error @ {case.index}: {E}")
                                        result = Result(Status.CASE_NOT_AVAILABLE, [str(E)], [])
                                        if db is not None:
                                            db[case.index] = result
                                            db.commit()
                                        break
                                elif cached is not None and case.index not in force_retry and (cached.status == Status.SUCCESS or (cached.status == Status.FAIL and not retry_failure)):
                                    result = cached
                                else:
                                    try:
                                        result = await test.validate(case.index, case.code)
                                        if db is not None:
                                            db[case.index] = result
                                            db.commit()
                                    except REPLFail as E:
                                        logger.error(f"REPLFail error @ {case.index}: {E}")
                                        result = Result(Status.CASE_NOT_AVAILABLE, [str(E)], [])
                                        if db is not None:
                                            db[case.index] = result
                                            db.commit()
                                        break
                            except Exception as e:
                                logger.error(f"Error processing case {case.index}: {str(e)}")
                                logger.error(f"Traceback:\n{traceback.format_exc()}")
                                # Put the task back in the queue to retry
                                await task_queue.put(case)
                                break
                            finally:
                                # Mark task as done
                                task_queue.task_done()

                            async with lock:
                                # Update statistics
                                if result.status == Status.SUCCESS:
                                    success += 1
                                elif result.status == Status.CASE_NOT_AVAILABLE:
                                    unavailable += 1

                                remaining_cases -= 1
                                total += 1
                                results[case.index] = result

                            await log_state()
                            if result.status == Status.CASE_NOT_AVAILABLE:
                                break

                except ConnectionRefusedError:
                    logger.error(f"Fail to connect to {server_addr}. Retrying in 10 seconds...")
                    await asyncio.sleep(10)
                except Exception as e:
                    logger.error(f"Worker task for server {server_addr} encountered an error: {str(e)}. Retrying in 10 seconds...")
                    await asyncio.sleep(10)

        # Create and start worker tasks for each server
        tasks = []
        instances = server_instances if server_instances is not None else SERVER_INSTANCES
        for server_addr in instances:
            task = asyncio.create_task(eval_server(server_addr))
            tasks.append(task)

        # Wait for all tasks to complete
        await asyncio.gather(*tasks)

    if result_path is not None:
        with SqliteDict(result_path) as db:
            await execute(db)
    else:
        await execute(None)
    logger.info(f"Evaluation complete. Processed {total}/{len(cases)} cases.")
    await log_state()
    return results
