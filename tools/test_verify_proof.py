"""Integration tests for the verify_proof REPL app."""

import asyncio
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'contrib', 'Isa-REPL'))
from IsaREPL import Client, REPLFail


REPL_ADDR = "127.0.0.1:6666"

# -- Test theories ----------------------------------------------------------

SORRY_THEORY = """\
theory Test_Verify
  imports Main
begin
theorem test_thm: "1 + 1 = (2::nat)"
  sorry
end
"""

VALID_PROOF_THEORY = """\
theory Test_Verify
  imports Main
begin
theorem test_thm: "1 + 1 = (2::nat)"
  by simp
end
"""

MUTATED_GOAL_THEORY = """\
theory Test_Verify
  imports Main
begin
theorem test_thm: "True"
  by simp
end
"""

AXIOM_INJECTION_THEORY = """\
theory Test_Verify
  imports Main
begin
axiomatization where evil_ax: False
theorem test_thm: "1 + 1 = (2::nat)"
  by simp
end
"""

MULTI_SORRY_THEORY = """\
theory Test_Verify
  imports Main
begin
lemma helper_a: "True"
  sorry
lemma helper_b: "1 = (1::nat)"
  sorry
end
"""

MULTI_PARTIAL_FIX_THEORY = """\
theory Test_Verify
  imports Main
begin
lemma helper_a: "True"
  by simp
lemma helper_b: "1 = (1::nat)"
  sorry
end
"""


# -- Helpers ----------------------------------------------------------------

async def snapshot(c, theory_source, import_dir=None):
    await c.set_register_thy(False)
    await c.rollback("init")
    response = await c.eval(theory_source, timeout=120000, cmd_timeout=30000,
                            import_dir=import_dir)
    if response is not None:
        for cmd_out in response:
            if cmd_out.errors:
                raise RuntimeError(f"Snapshot eval errors: {cmd_out.errors}")
    await c.run_app("verify_proof")
    await c._write("snapshot")
    result = Client._parse_control_(await c._feed_and_unpack())
    await c.set_register_thy(True)
    return result  # (sorry_facts, axioms)


async def verify(c, theory_source, baseline_props, baseline_axioms,
                 oracle_whitelist=None, import_dir=None):
    await c.set_register_thy(False)
    await c.rollback("init")
    response = await c.eval(theory_source, timeout=120000, cmd_timeout=30000,
                            import_dir=import_dir)
    if response is not None:
        for cmd_out in response:
            if cmd_out.errors:
                return {"eval_errors": [str(e) for e in cmd_out.errors]}
    await c.run_app("verify_proof")
    await c._write("verify")
    await c._write((baseline_props, baseline_axioms, oracle_whitelist or []))
    result = Client._parse_control_(await c._feed_and_unpack())
    await c.set_register_thy(True)
    goal_preserved, goal_results, bad_oracles, oracles_ok, new_axioms, axioms_ok = result
    return {
        "goal_preserved": goal_preserved,
        "goal_results": goal_results,
        "bad_oracles": bad_oracles,
        "oracles_ok": oracles_ok,
        "new_axioms": new_axioms,
        "axioms_ok": axioms_ok,
    }


# -- Tests ------------------------------------------------------------------

passed = 0
failed = 0

def check(name, condition, detail=""):
    global passed, failed
    if condition:
        print(f"  PASS: {name}")
        passed += 1
    else:
        print(f"  FAIL: {name} — {detail}")
        failed += 1


async def test_snapshot_captures_sorry(c):
    print("\n[Test 1] Snapshot captures sorry facts")
    sorry_facts, axioms = await snapshot(c, SORRY_THEORY)
    check("sorry_facts is non-empty", len(sorry_facts) > 0,
          f"got {len(sorry_facts)} facts")
    names = [f[0] if isinstance(f[0], str) else f[0].decode() for f in sorry_facts]
    check("test_thm in sorry_facts",
          any("test_thm" in n for n in names), f"names: {names}")
    check("axioms captured", isinstance(axioms, list), f"type: {type(axioms)}")


async def test_valid_proof_passes(c):
    print("\n[Test 2] Valid proof passes all checks")
    sorry_facts, axioms = await snapshot(c, SORRY_THEORY)
    result = await verify(c, VALID_PROOF_THEORY, sorry_facts, axioms)
    if "eval_errors" in result:
        check("eval succeeds", False, f"errors: {result['eval_errors']}")
        return
    check("goal_preserved", result["goal_preserved"] is True,
          f"got {result['goal_preserved']}")
    check("oracles_ok", result["oracles_ok"] is True,
          f"bad_oracles: {result['bad_oracles']}")
    check("axioms_ok", result["axioms_ok"] is True,
          f"new_axioms: {result['new_axioms']}")


async def test_sorry_detected(c):
    print("\n[Test 3] Sorry still present is detected")
    sorry_facts, axioms = await snapshot(c, SORRY_THEORY)
    result = await verify(c, SORRY_THEORY, sorry_facts, axioms)
    if "eval_errors" in result:
        check("eval succeeds", False, f"errors: {result['eval_errors']}")
        return
    check("oracles_ok is False", result["oracles_ok"] is False,
          f"got {result['oracles_ok']}")
    oracle_names = [o.decode() if isinstance(o, bytes) else str(o)
                    for o in result["bad_oracles"]]
    check("skip_proof in bad_oracles",
          any("skip_proof" in n for n in oracle_names),
          f"oracles: {oracle_names}")


async def test_goal_mutation_detected(c):
    print("\n[Test 4] Goal mutation detected")
    sorry_facts, axioms = await snapshot(c, SORRY_THEORY)
    result = await verify(c, MUTATED_GOAL_THEORY, sorry_facts, axioms)
    if "eval_errors" in result:
        check("eval succeeds", False, f"errors: {result['eval_errors']}")
        return
    check("goal_preserved is False", result["goal_preserved"] is False,
          f"got {result['goal_preserved']}")
    mutated = [n for n, ok in result["goal_results"] if not ok]
    mutated_str = [m.decode() if isinstance(m, bytes) else str(m) for m in mutated]
    check("test_thm flagged as mutated", len(mutated_str) > 0,
          f"mutated: {mutated_str}")


async def test_axiom_injection_detected(c):
    print("\n[Test 5] Axiom injection detected")
    sorry_facts, axioms = await snapshot(c, SORRY_THEORY)
    result = await verify(c, AXIOM_INJECTION_THEORY, sorry_facts, axioms)
    if "eval_errors" in result:
        check("eval succeeds", False, f"errors: {result['eval_errors']}")
        return
    check("axioms_ok is False", result["axioms_ok"] is False,
          f"got {result['axioms_ok']}")
    new_ax = [a.decode() if isinstance(a, bytes) else str(a)
              for a in result["new_axioms"]]
    check("evil_ax in new_axioms", any("evil" in a for a in new_ax),
          f"new_axioms: {new_ax}")


async def test_registration_isolation(c):
    print("\n[Test 6] set_register_thy isolation (no conflict on second eval)")
    _sorry_facts, _axioms = await snapshot(c, SORRY_THEORY)
    # If snapshot didn't conflict, verify eval of same theory name should also work
    result = await verify(c, VALID_PROOF_THEORY, _sorry_facts, _axioms)
    check("no eval_errors", "eval_errors" not in result,
          f"errors: {result.get('eval_errors')}")


async def test_multi_sorry(c):
    print("\n[Test 7] Multiple sorry theorems — partial fix")
    sorry_facts, axioms = await snapshot(c, MULTI_SORRY_THEORY)
    names = [f[0] if isinstance(f[0], str) else f[0].decode() for f in sorry_facts]
    check("both helpers captured",
          any("helper_a" in n for n in names) and any("helper_b" in n for n in names),
          f"names: {names}")
    result = await verify(c, MULTI_PARTIAL_FIX_THEORY, sorry_facts, axioms)
    if "eval_errors" in result:
        check("eval succeeds", False, f"errors: {result['eval_errors']}")
        return
    check("oracles_ok is False (helper_b still sorry)",
          result["oracles_ok"] is False,
          f"got {result['oracles_ok']}, bad: {result['bad_oracles']}")


# -- Main -------------------------------------------------------------------

async def main():
    async with Client(REPL_ADDR, 'HOL', timeout=600) as c:
        print("Loading MLML_Verify theory (registers the app)...")
        loaded = await c.load_theory(["MLML_Verify.MLML_Verify"])
        print(f"Loaded: {loaded}")
        await c.record_state("init")
        print("Running tests...")

        await test_snapshot_captures_sorry(c)
        await test_valid_proof_passes(c)
        await test_sorry_detected(c)
        await test_goal_mutation_detected(c)
        await test_axiom_injection_detected(c)
        await test_registration_isolation(c)
        await test_multi_sorry(c)

    print(f"\n{'='*50}")
    print(f"Results: {passed} passed, {failed} failed")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
