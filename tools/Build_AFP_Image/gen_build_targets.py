import sys
import os
from data.isabelle import THEORIES, INFLUENCES, SESSIONS, all_theories_in_session, deps_of, session_of, short_name_of

BASE = 'HOL-Library'
BASE_THEORIES = all_theories_in_session(BASE)

# Theories carrying "Example"/"Test"/... markers in their name/path are treated as
# examples and dropped, EXCEPT the following which are genuine content that other
# theories depend on.
EXEMPT_THYS = ['UPF.NormalisationTestSpecification', 'KAT_and_DRA.Conway_Tests',
               'Shadow_DOM.Shadow_DOM_BaseTest', 'HOL-Analysis.Summation_Tests']
# Short names of our own tooling theories that must never enter the image.
EXEMPT_SHORT = ['Isa_REPL', 'Auto_Sledgehammer', 'Minilang', 'MS_Translator',
                'MS_Translator_Top', 'Minilang_Base']

# Theories that cannot be built at all under Isabelle2025-2 + afp-2026, and
# everything that transitively depends on them. In each, `A !! i` is ambiguous
# because both HOL-Library.IArray (IArray.sub) and HOL-Library.Stream
# (Stream.snth) declare `!!` and are both in the theory's import closure (via
# ...->Rank_Nullity_Theorem->Lp->HOL-Probability->Stream). Neither theory is
# reachable from its own session's ROOT, so upstream AFP never builds them; our
# image listed them explicitly and hit the failure.
#
# Verified individually with per-theory probe sessions -- do NOT add a theory
# here on suspicion alone: of 11 theories matching the "IArray+Stream in
# closure and uses !!" pattern, 9 build fine.
CLASH_ROOTS = [# NOTE: the Gram_Schmidt_IArrays / System_Of_Equations_IArrays /
               # Perron_Frobenius_Irreducible `!!`/`sigma` clashes were NOT an
               # afp-2026 defect -- they were caused by a LOCAL patch that had
               # added `Lp.Functional_Spaces` to Rank_Nullity_Theorem, dragging
               # measure theory (Stream, Sigma_Algebra) into every downstream
               # closure. That patch has been reverted (the dead `fun ::
               # real_vector` instance in Rank_Nullity/Miscellaneous.thy is just
               # commented out; Lp's more general instance covers it), so those
               # theories build again and are no longer excluded.
               # Needs the record_proofs=2 HOL-Proofs base (inductive_realizer):
               # "thm_name_of: bad proof of theorem". Same class as XML_Data.
               'HOL-Proofs-Lambda.WeakNorm',
               # `compile_generated_files` does `cp -r mlunta .` where mlunta is
               # resolved relative to the *build* directory; the mlunta/ tree only
               # exists in the Munta_Certificate_Checker session dir, so these can
               # never be built from another session.
               'Munta_Certificate_Checker.Munta_Certificate_Compile_Poly',
               'Munta_Certificate_Checker.Munta_Certificate_Compile_MLton',
               # Read their session-local sat_data/*.xz via a *bare relative*
               # path from a forked ML task ("forked to the background"), so the
               # read resolves against the build directory, not the theory's
               # master dir. Fails from any other session ("BinIO.openIn ...
               # sat_data/kemeny_profiles_5_2.xz: No such file"). The PAPP
               # theories that read the same kind of data use `\<^master_dir> +`
               # and build fine, so this is specific to these two.
               'SWF_Impossibility.Anon_Unan_Stratproof_Impossibility',
               'SWF_Impossibility.Majcons_Stratproof_Impossibility',
               # Theories that need build options our image does not (and should
               # not) set. Their own ROOT grants them via per-theory options or a
               # special base session; a plain session cannot reproduce that.
               #  - Common_Patterns: `theories [quick_and_dirty]`, has 9 `sorry`s
               #    -- must never enter a prover image anyway.
               #  - XML_Data: needs the record_proofs=2 HOL-Proofs base
               #    ("thm_of_proof: partial proof term"). Its two sibling
               #    HOL-Proofs-ex theories build fine and are kept.
               #  - HOL_Light_Import: needs the external HOL_LIGHT_BUNDLE.
               'HOL-Induct.Common_Patterns',
               'HOL-Proofs-ex.XML_Data',
               'HOL-Import.HOL_Light_Import']

def _clash_closure():
    excl = set()
    stack = list(CLASH_ROOTS)
    while stack:
        u = stack.pop()
        if u in excl:
            continue
        excl.add(u)
        stack.extend(INFLUENCES.get(u, ()))
    return excl

CLASH_EXCLUDE = _clash_closure()

def has_examples(thy):
    """True if `thy` looks like an example/test theory that should be dropped."""
    session = session_of(thy)
    exempted = 'Jinja' in thy or 'Prime_Test' in thy or \
                'Elliptic_Test' in thy or 'Rational_Root_Test' in thy or \
                thy in EXEMPT_THYS
    info = THEORIES[thy]
    return not exempted and (\
            'Example' in thy or 'example' in thy or \
            'example' in info['path'] or \
            'Test' in thy or \
            session in ['HOL-Proofs-Extraction'])


def can_use(thy):
    if thy in CLASH_EXCLUDE:
        return False
    ret = INFLUENCES[thy] and \
        short_name_of(thy) not in EXEMPT_SHORT and \
        not has_examples(thy)
    if not ret and INFLUENCES[thy] and any(can_use(ref) for ref in INFLUENCES[thy]):
        print(f'cannot drop {thy} (influences: {INFLUENCES[thy]})')
        ret = True
    return ret


if __name__ == '__main__':
    DEPENDENCIES = {}
    for thy, info in THEORIES.items():
        DEPENDENCIES[thy] = set(info['deps'])

    dep_counts = {}
    ready_thys = set()
    used_thys = set()
    used_sessions = set()

    step_count = 0
    total_work = 0
    def emit_step():
        global step_count
        os.makedirs(f'./tools/Build_AFP_Image/AFP-DEP1/AFP-DEP1-{step_count}', exist_ok=True)
        with open(f'./tools/Build_AFP_Image/AFP-DEP1/AFP-DEP1-{step_count}/ROOT', 'w') as f:
            if step_count == 0:
                f.write(f'session \"AFP-DEP1-{step_count}\" = \"{BASE}\" +\n')
            else:
                f.write(f'session \"AFP-DEP1-{step_count}\" = \"AFP-DEP1-{step_count-1}\" +\n')
            f.write(f'sessions\n')
            for session in used_sessions:
                f.write(f'  \"{session}\"\n')
            f.write(f'theories\n')
            for thy in used_thys:
                f.write(f'  \"{thy}\"\n')
        used_thys.clear()
        used_sessions.clear()
        step_count += 1

    def use_thy(thy):
        global total_work
        if thy not in BASE_THEORIES:
            total_work += 1
            used_thys.add(thy)
            session = session_of(thy)
            if session != '':
                used_sessions.add(session)
            elif thy in SESSIONS:
                # bare (global) theory whose name IS a session -> declare that session
                used_sessions.add(thy)
            if len(used_thys) >= 384:
                emit_step()


    for thy, deps in DEPENDENCIES.items():
        if len(deps) == 0:
            ready_thys.add(thy)

    with open('./tools/Build_AFP_Image/AFP-DEP1/all_theories.lst', 'w') as f:
        while ready_thys:
            best = None
            for thy in ready_thys:
                if session_of(thy) in used_sessions:
                    best = thy
                    ready_thys.remove(thy)
                    break
            if not best:
                best = ready_thys.pop()
            f.write(f'{best}\n')
            use_thy(best)
            for ref in INFLUENCES[best]:
                DEPENDENCIES[ref].remove(best)
                if len(DEPENDENCIES[ref]) == 0 and can_use(ref):
                    ready_thys.add(ref)

    with open('./tools/Build_AFP_Image/AFP-DEP1/ROOTS', 'w') as f:
        for i in range(step_count):
            f.write(f'AFP-DEP1-{i}\n')

    print(f'Total work: {total_work}')
