import asyncio
import json
import logging
import os
import random
import re
import shutil
import tempfile
import time

from IsaREPL import Client as REPLClient, REPLFail
from data.isabelle import CaseNotAvailable, MiniF2F_Data, PutnamBench_Data
from .evaluator import Evaluator, Result, Status, AgentCostData, Isar_Base

logger = logging.getLogger(__name__)

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# jEdit settings dir. Isabelle's bundled jedit/etc/settings hardcodes
# JEDIT_SETTINGS to $ISABELLE_HOME_USER/jedit, so every headless worker shares
# this one directory. Its `properties` file gets clobbered across runs, which
# triggers a keymap-merge modal dialog at jEdit startup that blocks the prover
# session forever. Restoring `properties` from a known-good `properties.bak`
# before each launch keeps every jEdit starting from a clean baseline.
JEDIT_SETTINGS_DIR = os.path.expanduser("~/.isabelle/Isabelle2025-2/jedit")

# Per-million-token pricing: (input, cached_read, output, cache_write)
#   cached_read  = price of a cache HIT (cache_read_input_tokens).
#   cache_write  = price of a cache CREATION (cache_creation_input_tokens), which is
#                  per-provider, NOT a universal multiple of input:
#                    * Anthropic charges 1.25x base input for the default 5-minute
#                      ephemeral TTL this plugin uses (it never requests "ttl":"1h"
#                      = 2x), e.g. Opus 6.25 = 1.25x5, Sonnet 3.75 = 1.25x3.
#                    * OpenAI has no cache-write charge at all (caching is free to
#                      create; only reads are discounted) -> 0.0.
# NB: Opus 4.5/4.6/4.7/4.8 ALL price at input $5 / output $25 (verified against the
# official pricing page 2026-06-23). Only the deprecated Opus 4.1 / Opus 4 are the
# old $15 / $75 — do NOT copy that row onto a 4.5+ model (a prior table did, which
# over-counted Opus 4.8 cost by 3x).
MODEL_PRICING: dict[str, tuple[float, float, float, float]] = {
    "gpt-5.5":       (2.0,  0.5,  8.0,  0.0),
    "gpt-4.1":       (2.0,  0.5,  8.0,  0.0),
    "gpt-4.1-mini":  (0.4,  0.1,  1.6,  0.0),
    "gpt-4.1-nano":  (0.1,  0.025, 0.4, 0.0),
    "gpt-4o":        (2.5,  1.25, 10.0, 0.0),
    "o3":            (2.0,  0.5,  8.0,  0.0),
    "o4-mini":       (1.1,  0.275, 4.4, 0.0),
    "claude-sonnet-4-5-20250514": (3.0, 0.3, 15.0, 3.75),
    "claude-opus-4-5-20250414":   (5.0, 0.5, 25.0, 6.25),
    "claude-opus-4-6":            (5.0, 0.5, 25.0, 6.25),
    "claude-opus-4-7":            (5.0, 0.5, 25.0, 6.25),
    "claude-opus-4-8":            (5.0, 0.5, 25.0, 6.25),
    "claude-sonnet-4-6":          (3.0,  0.3, 15.0, 3.75),
}

def compute_cost_usd(model: str, uncached: int, cached: int, output: int,
                     cache_creation: int = 0) -> float:
    key = model.removeprefix("openai/")
    if key not in MODEL_PRICING:
        logger.warning(f"Unknown model '{model}' for pricing, cost_usd will be 0")
        return 0.0
    inp_price, cached_price, out_price, cache_write_price = MODEL_PRICING[key]
    return (uncached * inp_price + cached * cached_price
            + cache_creation * cache_write_price + output * out_price) / 1_000_000


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
        await self._repl.load_theory(["MLML_Verify.MLML_Verify"])
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

    def _include_sessions(self) -> list[str]:
        return []

    def _jedit_extra_imports(self) -> str | None:
        return None

    def all_cases(self):
        raise NotImplementedError

    async def start_case(self, index):
        pass

    def _oracle_whitelist(self) -> list[str]:
        return []

    def _restore_jedit_properties(self) -> None:
        """Copy properties.bak over properties in the shared $JEDIT_SETTINGS
        dir before launching jEdit, so a clobbered properties file can't
        trigger the keymap-merge dialog that hangs the prover. Missing backup
        or copy errors are logged but never abort the run."""
        backup = os.path.join(JEDIT_SETTINGS_DIR, "properties.bak")
        target = os.path.join(JEDIT_SETTINGS_DIR, "properties")
        if not os.path.isfile(backup):
            logger.warning(f"Worker {self._worker_id}: no jEdit properties "
                           f"backup at {backup}; skipping restore")
            return
        try:
            shutil.copyfile(backup, target)
            logger.info(f"Worker {self._worker_id}: restored jEdit properties "
                        f"from {backup}")
        except Exception as e:
            logger.warning(f"Worker {self._worker_id}: failed to restore jEdit "
                           f"properties: {e}")

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
        # The agent sometimes drops the theory-closing `end` when it rewrites
        # the proof (it replaces the `sorry\nend` tail but only restores the
        # proof). An otherwise-complete proof then fails verification because
        # `Toplevel.end_theory` reports "Malformed theory" on an unclosed
        # theory. Re-append `end` when it is absent so a finished proof still
        # counts as verified.
        if not re.search(r'\bend\b\s*\Z', final_thy):
            final_thy = final_thy.rstrip() + "\nend\n"
            logger.info(f"Worker {self._worker_id}: appended missing 'end' "
                        f"to theory before verification")
        try:
            await self._repl.set_register_thy(False)
            await self._repl.rollback("init")
            response = await self._repl.eval(
                final_thy,
                timeout=600000,
                # Per-command (single statement) wall-clock cap, scoped to THIS
                # validator eval only: it travels in the \x05eval request and the
                # server applies it per-call without persisting, so it does not
                # affect the agent's REPL, other evaluators, or other clients on
                # the shared server. 180s is long enough for legitimately slow
                # proof steps yet trips slow-burn memory bombs (e.g. presburger
                # on large coefficients) before they exhaust the heap.
                cmd_timeout=180000,
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

        jedit_extra = self._jedit_extra_imports()
        if jedit_extra:
            jedit_content = re.sub(
                r'(imports)\s+',
                rf'\1\n  {jedit_extra}\n  ',
                content, count=1)
            jedit_with_sorry = jedit_content + "\n  sorry\nend\n"
        else:
            jedit_with_sorry = original_with_sorry

        with open(thy_path, "w", encoding="utf-8") as f:
            f.write(jedit_with_sorry)

        snap_ok, snap_err = await self._snapshot_goals(original_with_sorry)
        if not snap_ok:
            logger.warning(f"Worker {self._worker_id}: snapshot failed for {index}: {snap_err}")

        result_file = os.path.join(work_dir, f"result_{theory_name}.json")

        mash_dir = os.path.join(PROJECT_ROOT, "cache", "repl_tmps", f"autocorrode_{self._worker_id}")
        os.makedirs(mash_dir, exist_ok=True)

        env = os.environ.copy()
        env["DISPLAY"] = self._display
        env["IQ_MCP_ALLOWED_ROOTS"] = work_dir
        # Give each worker a distinct I/Q MCP base port so concurrent jEdit
        # instances don't all contend for the default 8765. Spacing of 100
        # matches the plugin's MAX_PORT_SCAN so per-worker scan ranges (each
        # base..base+100) don't overlap. The plugin still scans upward from
        # this base on BindException as a safety net.
        worker_idx = int((re.findall(r"\d+", self._worker_id) or ["0"])[0])
        env["IQ_MCP_PORT"] = str(8765 + worker_idx * 100)
        env["MASH_STATE_PATH"] = os.path.join(mash_dir, "mash_state")
        env["ASSISTANT_BATCH_PROMPT"] = f"Complete the proof of theorem {thm_name}"
        env["ASSISTANT_BATCH_RESULT_FILE"] = result_file

        # Temporary: stagger concurrent jEdit startups (random 1-10s) to ease
        # contention on the shared $ISABELLE_HOME_USER state. Before start_time so
        # it is not counted in elapsed.
        await asyncio.sleep(random.uniform(1.0, 10.0))

        self._restore_jedit_properties()

        start_time = time.time()
        cmd = [self._isabelle_bin, "jedit"]
        for d in self._session_dirs():
            cmd.extend(["-d", d])
        for s in self._include_sessions():
            cmd.extend(["-i", s])
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
                uncached_tokens = rj.get("uncached_prompt_tokens", 0)
                cached_tokens = rj.get("cached_tokens", 0)
                cache_creation_tokens = rj.get("cache_creation_tokens", 0)
                output_tokens = rj.get("completion_tokens", 0)
                model = rj.get("model", "unknown")
                cost_usd = compute_cost_usd(model, uncached_tokens, cached_tokens,
                                            output_tokens, cache_creation_tokens)
                # Canonical DB format: input_tokens = uncached only; cache_read and
                # cache_creation are the separate cache portions the plugin reports
                # (AssistantPlugin.usageJson emits "cache_creation_tokens"). It is
                # nonzero only for Anthropic models that actually used prompt caching;
                # OpenAI has no cache-creation concept and always reports 0.
                cost = AgentCostData(
                    input_tokens=uncached_tokens,
                    cache_creation_tokens=cache_creation_tokens,
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
            jedit_extra = self._jedit_extra_imports()
            if jedit_extra:
                final_thy_for_repl = re.sub(
                    rf'^\s*{re.escape(jedit_extra)}\s*\n',
                    '', final_thy, count=1, flags=re.MULTILINE)
            else:
                final_thy_for_repl = final_thy
            sorry_present = Isar_Base.contains_sorry(final_thy, original_code=content)
        else:
            sorry_present = True
            final_thy = None
            final_thy_for_repl = None

        status = Status.SUCCESS if not sorry_present else Status.FAIL
        errors = []
        if sorry_present:
            errors.append(f"Agent status: {agent_status}, sorry still present")
        elif final_thy_for_repl:
            verified, verify_error = await self._verify_via_repl(final_thy_for_repl)
            if not verified:
                status = Status.FAIL
                errors.append(f"REPL verification failed: {verify_error}")
            else:
                logger.info(f"Worker {self._worker_id}: REPL verification passed for {index}")

        return Result(status, errors, [elapsed_s], data=_make_data())

    async def revalidate(self, index, old_result):
        """Re-run ONLY the REPL verification on the proof a prior run already
        produced, reusing the saved final theory and the prior cost/response
        data. Does NOT launch jEdit or re-run the agent. Used by
        --reverify-failures to cheaply re-check failed cases against an updated
        verifier (e.g. a fixed oracle whitelist)."""
        old_data = old_result.data if isinstance(old_result, Result) else None
        old_elapsed = old_result.elapsed_time if isinstance(old_result, Result) else []

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
            return Result(Status.FAIL, ["Cannot parse theory name from content"],
                          old_elapsed, data=old_data)
        theory_name = m.group(1)

        if not self._log_dir:
            return Result(Status.FAIL,
                          ["Reverify needs --log-dir (no saved theory to re-check)"],
                          old_elapsed, data=old_data)
        safe_index = str(index).replace("/", "_").replace("\\", "_")
        thy_path = os.path.join(self._log_dir, safe_index, f"{theory_name}.thy")
        if not os.path.isfile(thy_path):
            return Result(Status.FAIL,
                          [f"Reverify: no saved theory at {thy_path}"],
                          old_elapsed, data=old_data)

        with open(thy_path, "r", encoding="utf-8") as f:
            final_thy = f.read()
        jedit_extra = self._jedit_extra_imports()
        if jedit_extra:
            final_thy_for_repl = re.sub(
                rf'^\s*{re.escape(jedit_extra)}\s*\n',
                '', final_thy, count=1, flags=re.MULTILINE)
        else:
            final_thy_for_repl = final_thy

        if Isar_Base.contains_sorry(final_thy, original_code=content):
            return Result(Status.FAIL,
                          ["Reverify: sorry still present in saved theory"],
                          old_elapsed, data=old_data)

        original_with_sorry = content + "\n  sorry\nend\n"
        snap_ok, snap_err = await self._snapshot_goals(original_with_sorry)
        if not snap_ok:
            return Result(Status.FAIL, [f"Reverify: snapshot failed: {snap_err}"],
                          old_elapsed, data=old_data)

        verified, verify_error = await self._verify_via_repl(final_thy_for_repl)
        if verified:
            logger.info(f"Worker {self._worker_id}: reverify PASSED for {index}")
            return Result(Status.SUCCESS, [], old_elapsed, data=old_data)
        logger.info(f"Worker {self._worker_id}: reverify still FAILS for {index}: {verify_error}")
        return Result(Status.FAIL, [f"REPL verification failed: {verify_error}"],
                      old_elapsed, data=old_data)


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

    def _include_sessions(self) -> list[str]:
        return ["iq"]

    def _jedit_extra_imports(self) -> str | None:
        return "iq.Isar_Explore"

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
