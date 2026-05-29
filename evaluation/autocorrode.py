import asyncio
import json
import logging
import os
import re
import shutil
import tempfile
import time

from IsaREPL import Client as REPLClient, REPLFail
from data.isabelle import CaseNotAvailable, MiniF2F_Data, PutnamBench_Data
from .evaluator import Evaluator, Result, Status, AgentCostData, Isar_Base

logger = logging.getLogger(__name__)

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Per-million-token pricing: (input, cached_input, output)
MODEL_PRICING: dict[str, tuple[float, float, float]] = {
    "gpt-5.5":       (2.0,  0.5,  8.0),
    "gpt-4.1":       (2.0,  0.5,  8.0),
    "gpt-4.1-mini":  (0.4,  0.1,  1.6),
    "gpt-4.1-nano":  (0.1,  0.025, 0.4),
    "gpt-4o":        (2.5,  1.25, 10.0),
    "o3":            (2.0,  0.5,  8.0),
    "o4-mini":       (1.1,  0.275, 4.4),
    "claude-sonnet-4-5-20250514": (3.0, 0.3, 15.0),
    "claude-opus-4-5-20250414":   (15.0, 1.5, 75.0),
}

def compute_cost_usd(model: str, uncached: int, cached: int, output: int) -> float:
    key = model.removeprefix("openai/")
    if key not in MODEL_PRICING:
        logger.warning(f"Unknown model '{model}' for pricing, cost_usd will be 0")
        return 0.0
    inp_price, cached_price, out_price = MODEL_PRICING[key]
    return (uncached * inp_price + cached * cached_price + output * out_price) / 1_000_000


def _detect_isabelle_bin():
    for candidate in [
        os.path.join(PROJECT_ROOT, "contrib", "Isabelle2025-2", "bin", "isabelle"),
        shutil.which("isabelle"),
    ]:
        if candidate and os.path.isfile(candidate):
            return candidate
    raise FileNotFoundError(
        "Cannot find isabelle binary. Set --isabelle-bin explicitly."
    )


def _detect_iq_session_dir():
    candidate = os.path.join(PROJECT_ROOT, "contrib", "AutoCorrode", "iq")
    if os.path.isdir(candidate):
        return candidate
    raise FileNotFoundError(
        "Cannot find iq session directory. Set --iq-session-dir explicitly."
    )


class AutoCorrode_Base(Evaluator):

    def __init__(self, worker_id: str, *,
                 isabelle_bin: str | None = None,
                 iq_session_dir: str | None = None,
                 timeout_seconds: int = 3600,
                 display: str = ":99",
                 threads: int | None = None,
                 log_dir: str | None = None,
                 repl_addr: str = "127.0.0.1:6666"):
        self._worker_id = worker_id
        self._isabelle_bin = isabelle_bin or _detect_isabelle_bin()
        self._iq_session_dir = iq_session_dir or _detect_iq_session_dir()
        self._timeout_seconds = timeout_seconds
        self._display = display
        self._threads = threads
        self._log_dir = log_dir
        self._tmpdir: str | None = None
        self._repl_addr = repl_addr
        self._repl: REPLClient | None = None
        self._baseline_props: list | None = None
        self._baseline_axioms: list | None = None

    async def __aenter__(self):
        if not self._log_dir:
            self._tmpdir = tempfile.mkdtemp(prefix=f"autocorrode_{self._worker_id}_")
            logger.info(f"Worker {self._worker_id}: temp dir {self._tmpdir}")
        self._repl = REPLClient(self._repl_addr, 'HOL', timeout=600)
        await self._repl.__aenter__()
        await self._repl.record_state("init")
        logger.info(f"Worker {self._worker_id}: REPL verification client connected to {self._repl_addr}")
        return self

    async def __aexit__(self, exc_type, exc_value, traceback):
        if self._repl:
            try:
                self._repl.close()
            except Exception:
                pass
            self._repl = None
        if self._tmpdir and os.path.isdir(self._tmpdir):
            shutil.rmtree(self._tmpdir, ignore_errors=True)
            self._tmpdir = None

    def _get_theory_content(self, index: str) -> str:
        raise NotImplementedError

    def _session_name(self) -> str:
        return "iq"

    def _session_dirs(self) -> list[str]:
        return [self._iq_session_dir]

    def _inject_import(self) -> str | None:
        return None

    def _import_dir(self) -> str | None:
        return None

    def all_cases(self):
        raise NotImplementedError

    async def start_case(self, index):
        pass

    def _oracle_whitelist(self) -> list[str]:
        return []

    async def _snapshot_goals(self, original_source: str) -> tuple[bool, str]:
        assert self._repl is not None
        self._baseline_props = None
        self._baseline_axioms = None
        try:
            await self._repl.set_register_thy(False)
            await self._repl.rollback("init")
            response = await self._repl.eval(
                original_source,
                timeout=120000,
                cmd_timeout=30000,
                import_dir=self._import_dir(),
            )
            if response is not None:
                for cmd_out in response:
                    if cmd_out.errors:
                        await self._repl.set_register_thy(True)
                        return False, "Snapshot eval errors: " + "; ".join(
                            str(e) for e in cmd_out.errors[:5])
            await self._repl.run_app("verify_proof")
            await self._repl._write("snapshot")
            result = REPLClient._parse_control_(await self._repl._feed_and_unpack())
            self._baseline_props = result[0]
            self._baseline_axioms = result[1]
            await self._repl.set_register_thy(True)
            return True, ""
        except REPLFail as e:
            try:
                await self._repl.set_register_thy(True)
            except Exception:
                pass
            return False, f"Snapshot failed: {e}"
        except Exception as e:
            try:
                await self._repl.set_register_thy(True)
            except Exception:
                pass
            return False, f"Snapshot error: {e}"

    async def _verify_via_repl(self, final_thy: str) -> tuple[bool, str]:
        assert self._repl is not None
        try:
            await self._repl.set_register_thy(False)
            await self._repl.rollback("init")
            response = await self._repl.eval(
                final_thy,
                timeout=120000,
                cmd_timeout=30000,
                import_dir=self._import_dir(),
            )
            if response is None:
                return False, "REPL returned no output"
            all_errors = []
            for cmd_out in response:
                if cmd_out.errors:
                    all_errors.extend(cmd_out.errors)
            if all_errors:
                return False, "; ".join(str(e) for e in all_errors[:5])
            if self._baseline_props is None:
                return False, "Baseline snapshot unavailable, cannot verify"
            await self._repl.run_app("verify_proof")
            await self._repl._write("verify")
            await self._repl._write((self._baseline_props, self._baseline_axioms,
                                     self._oracle_whitelist()))
            result = REPLClient._parse_control_(await self._repl._feed_and_unpack())
            goal_preserved, goal_results, bad_oracles, oracles_ok, new_axioms, axioms_ok = result
            errors = []
            if not goal_preserved:
                mutated = [name for name, ok in goal_results if not ok]
                errors.append(f"Goal mutation detected in: {', '.join(mutated)}")
            if not oracles_ok:
                oracle_names = [o.decode("utf-8") if isinstance(o, bytes) else str(o)
                                for o in bad_oracles]
                errors.append(f"Untrusted oracles: {', '.join(oracle_names)}")
            if not axioms_ok:
                axiom_names = [a.decode("utf-8") if isinstance(a, bytes) else str(a)
                               for a in new_axioms]
                errors.append(f"New axioms injected: {', '.join(axiom_names)}")
            if errors:
                return False, "; ".join(errors)
            return True, ""
        except REPLFail as e:
            return False, str(e)
        except TimeoutError:
            return False, "REPL verification timed out"
        except Exception as e:
            return False, f"REPL verification error: {e}"

    async def validate(self, index, proofs):
        try:
            content = self._get_theory_content(index)
        except (KeyError, CaseNotAvailable):
            return Result(Status.CASE_NOT_AVAILABLE, ["Case not available"], [])

        inject = self._inject_import()
        if inject:
            content = re.sub(
                r'(imports)\s+',
                rf'\1\n  {inject}\n  ',
                content, count=1)

        m = re.match(r'\s*theory\s+(\S+)', content)
        if not m:
            return Result(Status.FAIL, ["Cannot parse theory name from content"], [])
        theory_name = m.group(1)

        thm_match = re.search(r'(?:theorem|lemma|proposition)\s+(\S+)\s*:', content)
        if not thm_match:
            return Result(Status.FAIL, ["Cannot parse theorem name from content"], [])
        thm_name = thm_match.group(1)

        if self._log_dir:
            safe_index = str(index).replace("/", "_").replace("\\", "_")
            work_dir = os.path.join(self._log_dir, safe_index)
            os.makedirs(work_dir, exist_ok=True)
        else:
            assert self._tmpdir is not None, "validate() called outside async context manager"
            work_dir = self._tmpdir

        thy_path = os.path.join(work_dir, f"{theory_name}.thy")
        original_with_sorry = content + "\n  sorry\nend\n"
        with open(thy_path, "w", encoding="utf-8") as f:
            f.write(original_with_sorry)

        snap_ok, snap_err = await self._snapshot_goals(original_with_sorry)
        if not snap_ok:
            logger.warning(f"Worker {self._worker_id}: snapshot failed for {index}: {snap_err}")

        result_file = os.path.join(work_dir, f"result_{theory_name}.json")

        mash_dir = f"/run/screen/repl_tmps/autocorrode_{self._worker_id}"
        os.makedirs(mash_dir, exist_ok=True)

        env = os.environ.copy()
        env["DISPLAY"] = self._display
        env["IQ_MCP_ALLOWED_ROOTS"] = work_dir
        env["MASH_STATE_PATH"] = os.path.join(mash_dir, "mash_state")
        env["ASSISTANT_BATCH_PROMPT"] = f"Complete the proof of theorem {thm_name}"
        env["ASSISTANT_BATCH_RESULT_FILE"] = result_file

        start_time = time.time()
        cmd = [self._isabelle_bin, "jedit"]
        for d in self._session_dirs():
            cmd.extend(["-d", d])
        if self._threads is not None:
            cmd.extend(["-o", f"threads={self._threads}"])
        cmd.extend(["-l", self._session_name(), thy_path])
        log_path = os.path.join(work_dir, f"isabelle_{theory_name}.log")
        log_file = open(log_path, "w")
        timed_out = False
        try:
            proc = await asyncio.create_subprocess_exec(
                *cmd,
                env=env,
                stdout=log_file,
                stderr=asyncio.subprocess.STDOUT,
            )
            try:
                await asyncio.wait_for(proc.wait(), timeout=self._timeout_seconds)
            except asyncio.TimeoutError:
                timed_out = True
                logger.warning(f"Worker {self._worker_id}: killing timed-out process for {index}")
                proc.kill()
                await proc.wait()
        finally:
            log_file.close()

        elapsed_s = time.time() - start_time

        elapsed_ms = int(elapsed_s * 1000)
        cost: AgentCostData = {"elapsed": elapsed_ms, "api_requests": -1}
        response_text = ""
        agent_status = "unknown"

        if os.path.isfile(result_file):
            try:
                with open(result_file, "r", encoding="utf-8") as f:
                    rj = json.load(f)
                agent_status = rj.get("status", "unknown")
                response_text = rj.get("response", rj.get("error", ""))
                input_tokens = rj.get("prompt_tokens", 0)
                cached_tokens = rj.get("cached_tokens", 0)
                uncached_tokens = input_tokens - cached_tokens
                output_tokens = rj.get("completion_tokens", 0)
                model = rj.get("model", "unknown")
                cost_usd = compute_cost_usd(model, uncached_tokens, cached_tokens, output_tokens)
                cost = AgentCostData(
                    input_tokens=input_tokens,
                    cache_creation_tokens=0,
                    cache_read_tokens=cached_tokens,
                    output_tokens=output_tokens,
                    cost_usd=cost_usd,
                    api_requests=rj.get("api_requests", -1),
                    tool_calls=rj.get("tool_calls", -1),
                    elapsed=rj.get("elapsed_ms", elapsed_ms),
                )
            except Exception as e:
                logger.error(f"Worker {self._worker_id}: failed to parse result JSON: {e}")
                agent_status = "result_parse_error"

        if agent_status == "error" and os.path.isfile(log_path):
            with open(log_path, "r", encoding="utf-8") as f:
                log_tail = f.read()[-2000:]
            logger.error(f"Worker {self._worker_id}: Isabelle log tail for {index}:\n{log_tail}")

        def _make_data():
            return {"costs": [cost], "response": response_text,
                    "agent_status": agent_status}

        if timed_out:
            return Result(Status.FAIL, [f"Evaluator timeout ({self._timeout_seconds}s)"],
                          [elapsed_s], data=_make_data())

        if os.path.isfile(thy_path):
            with open(thy_path, "r", encoding="utf-8") as f:
                final_thy = f.read()
            sorry_present = Isar_Base.contains_sorry(final_thy, original_code=content)
        else:
            sorry_present = True
            final_thy = None

        status = Status.SUCCESS if not sorry_present else Status.FAIL
        errors = []
        if sorry_present:
            errors.append(f"Agent status: {agent_status}, sorry still present")
        elif final_thy:
            verified, verify_error = await self._verify_via_repl(final_thy)
            if not verified:
                status = Status.FAIL
                errors.append(f"REPL verification failed: {verify_error}")
            else:
                logger.info(f"Worker {self._worker_id}: REPL verification passed for {index}")

        return Result(status, errors, [elapsed_s], data=_make_data())


MINIF2F_PROVER_DIR = os.path.join(PROJECT_ROOT, "tasks", "MiniF2F_Prover")


class AutoCorrode_MiniF2F_Mixin:
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._data = MiniF2F_Data()

    def _get_theory_content(self, index: str) -> str:
        return self._data.prelude_and_statement_of(index)

    def _session_name(self) -> str:
        return "MiniF2F_Prover"

    def _session_dirs(self) -> list[str]:
        return [self._iq_session_dir, MINIF2F_PROVER_DIR]

    def _inject_import(self) -> str | None:
        return "MiniF2F_Prover.MiniF2F_Prover"

    def _import_dir(self) -> str | None:
        return MINIF2F_PROVER_DIR

    def all_cases(self):
        return self._data.all_cases()

    def cases_of(self, category: str):
        return self._data.cases_of(category)


class AutoCorrode_PutnamBench_Mixin:
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._data = PutnamBench_Data()

    def _get_theory_content(self, index: str) -> str:
        return self._data.prelude_and_statement_of(index)

    def all_cases(self):
        return self._data.all_cases()

    def cases_of(self, category: str):
        return self._data.cases_of(category)


class AutoCorrode_MiniF2F(AutoCorrode_MiniF2F_Mixin, AutoCorrode_Base):
    pass


class AutoCorrode_PutnamBench(AutoCorrode_PutnamBench_Mixin, AutoCorrode_Base):
    pass
