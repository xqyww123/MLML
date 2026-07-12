#!/usr/bin/env python3
"""Generate the AoA-learning target list from the SESSION heap itself.

THE RULE (single source of truth): a target is a theory that is ALREADY LOADED IN
THE HEAP the fleet REPLs run on (`SESSION`, normally MathBench_Prover). Nothing
else. We ask Isabelle for that set directly -- `Thy_Info.get_names ()` inside
`isabelle ML_process -l SESSION` -- rather than re-deriving it from ROOT files.

Why it MUST be the heap's theories, not "every .thy of every session ROOT mentions":

  * Corpus scope. The heap is exactly the import closure of MathBench_ProverBase,
    i.e. the theories MathBench/Putnam proofs actually build on. A session listed
    under `sessions` in ROOT only makes its theory NAMES resolvable; its other
    theories are never loaded. Scraping whole session directories pulls in
    hundreds of theories nothing depends on (Collections, Word_Lib, Refine_Monadic,
    Abstract-Rewriting, ...) -- off-corpus material whose lessons are useless for
    the goals we actually prove.

  * Key stability (the reason this is not merely cosmetic). Theory_Hash.hash_of
    (contrib/Isabelle_RPC/Tools/theory_hash.ML) hashes a theory by CONTENT --
    xxhash128 of the file plus its parents' hashes, byte-0 LSB cleared -- only when
    `Resources.loaded_theory name` holds, i.e. the theory is in the heap. For any
    other theory it falls back to FNV-1a of the theory NAME with the LSB SET: the
    "WIP" marker, meant for a jEdit buffer whose content is still changing.
    A theory replayed from source that is NOT in the heap therefore gets a
    name-hash. Experience-memory keys are the XOR of their constituent theories'
    hashes, so ONE such constituent makes the whole memory a WIP key -- a key that
    will NOT match the content-hash the same theory gets once it is in a heap. The
    memory then becomes silently unretrievable. Keeping every target in the heap
    keeps every constituent content-hashed, hence every memory persistent and
    keyed identically to what production proving computes.

Usage:
    python tasks/AoA-learning/gen_targets.py [-o targets_full] [--session MathBench_Prover]

Writes one repo-relative theory source path per line. Run it wherever the SESSION
heap is built (the cluster); it needs `isabelle` on PATH.
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# ML run inside the heap: every loaded theory, with the source file it came from
# (same resolution as Theory_Hash.get_theory_file_path: master dir + base name).
_ML = r"""
val _ = List.app (fn n =>
  (let
     val thy = Thy_Info.get_theory n
     val dir = Resources.master_directory thy
     val file = Path.ext "thy" (dir + Path.basic (Long_Name.base_name n))
     val p = File.platform_path (File.full_path dir file)
   in Output.physical_stdout ("THY\t" ^ n ^ "\t" ^ p ^ "\n") end)
  handle _ => ()) (Thy_Info.get_names ());
"""

# Isabelle/HOL theories that define TOOLS, definitional packages, code generation
# or testing infrastructure. They sit in the heap because everything imports them,
# but they carry no mathematics worth learning a proof strategy from.
# Judged by CONTENT, not by name: BNF_Cardinal_Arithmetic / BNF_Wellorder_* are
# genuine cardinal/wellorder mathematics and are deliberately KEPT, while
# Sledgehammer / Nitpick / Code_Target_* / Quickcheck_* are dropped.
_HOL_INFRA = {
    # proof tools and external provers
    "ATP", "Argo", "SMT", "SAT", "Sledgehammer", "Metis", "Meson", "Mirabelle",
    "Nitpick", "Nunchaku", "Try0", "Try0_HOL", "Predicate_Compile",
    "Groebner_Basis", "Numeral_Simprocs", "Semiring_Normalization", "Presburger",
    # counterexample search / random testing
    "Quickcheck_Exhaustive", "Quickcheck_Narrowing", "Quickcheck_Random",
    "Random", "Random_Pred", "Random_Sequence", "Lazy_Sequence", "Limited_Sequence",
    # code generation / reflection / extraction
    "Code_Evaluation", "Code_Numeral", "Extraction", "Typerep",
    # definitional packages
    "Typedef", "Record", "Ctr_Sugar", "Basic_BNF_LFPs", "Basic_BNFs",
    "BNF_Composition", "BNF_Def", "BNF_Fixpoint_Base", "BNF_Greatest_Fixpoint",
    "BNF_Least_Fixpoint", "Lifting", "Lifting_Set", "Transfer", "Quotient",
    "Fun_Def", "Fun_Def_Base", "Partial_Function",
    # bundle theories: imports + setup, no goals
    "Main", "Complex_Main",
    # Library/*
    "Library/Library", "Library/BNF_Axiomatization", "Library/BNF_Corec",
    "Library/Code_Abstract_Nat", "Library/Code_Cardinality", "Library/Code_Lazy",
    "Library/Code_Target_Int", "Library/Code_Target_Nat",
    "Library/Code_Target_Numeral", "Library/Code_Target_Numeral_Float",
    "Library/Code_Test", "Library/Debug", "Library/Old_Datatype",
    "Library/Conditional_Parametricity", "Library/Case_Converter",
    "Library/Simps_Case_Conv", "Library/Pattern_Aliases", "Library/Monad_Syntax",
    "Library/Open_State_Syntax", "Library/State_Monad", "Library/Parallel",
    "Library/Reflection", "Library/Rewrite", "Library/Time_Commands",
    "Library/Quotient_Syntax", "Library/Quotient_Type", "Library/Quotient_List",
    "Library/Quotient_Option", "Library/Quotient_Product", "Library/Quotient_Set",
    "Library/Quotient_Sum",
    # proof-method language / relativisation machinery
    "Eisbach/Eisbach", "Eisbach/Eisbach_Tools",
    "Types_To_Sets/Types_To_Sets", "Types_To_Sets/Examples/Prerequisites",
    "Types_To_Sets/Examples/Group_On_With",
}


def heap_theories(session: str) -> list[tuple[str, str]]:
    """(theory long name, absolute source path) for every theory loaded in SESSION."""
    with tempfile.NamedTemporaryFile("w", suffix=".ML", delete=False) as fh:
        fh.write(_ML)
        ml_file = fh.name
    try:
        proc = subprocess.run(
            ["isabelle", "ML_process", "-l", session, "-f", ml_file, "-r"],
            cwd=REPO, capture_output=True, text=True)
    finally:
        os.unlink(ml_file)
    out = [tuple(line.split("\t")[1:3])
           for line in proc.stdout.splitlines() if line.startswith("THY\t")]
    if not out:
        sys.exit(f"no theories reported by `isabelle ML_process -l {session}`:\n"
                 f"{proc.stdout[-2000:]}\n{proc.stderr[-2000:]}")
    return out  # type: ignore


def select(theories: list[tuple[str, str]]) -> tuple[list[str], dict[str, int]]:
    """Keep the mathematical Isabelle/HOL and AFP theories; drop everything else."""
    kept, dropped = [], {"non-corpus": 0, "HOL infra": 0}
    for _name, path in theories:
        rel = os.path.relpath(path, REPO)
        hol = rel.startswith("contrib/Isabelle2025-2/src/HOL/")
        afp = re.match(r"contrib/afp-[\d-]+/thys/", rel) is not None
        if not (hol or afp):
            # Pure, src/Tools, src/FOL, and our own infrastructure (Isa-REPL,
            # Isabelle_RPC, Minilang, Semantic_Embedding, auto_sledgehammer,
            # MathBench_Prover itself): not a corpus to learn proofs from.
            dropped["non-corpus"] += 1
            continue
        if hol:
            stem = rel[len("contrib/Isabelle2025-2/src/HOL/"):-len(".thy")]
            if stem in _HOL_INFRA:
                dropped["HOL infra"] += 1
                continue
        kept.append(rel)
    return sorted(kept), dropped


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--session", default="MathBench_Prover",
                   help="heap the fleet REPLs run on (learn.py's SESSION)")
    p.add_argument("-o", "--output", default="tasks/AoA-learning/targets_full",
                   help="target list to write (repo-relative)")
    args = p.parse_args()

    theories = heap_theories(args.session)
    kept, dropped = select(theories)

    out = os.path.join(REPO, args.output)
    with open(out, "w") as fh:
        fh.write(f"# AoA-learning targets: the theories loaded in the {args.session} heap,\n"
                 f"# minus Isabelle's tool/package/code-generation theories and our own\n"
                 f"# infrastructure. Generated by tasks/AoA-learning/gen_targets.py -- do not\n"
                 f"# hand-edit; regenerate after changing the session's imports.\n")
        fh.write("\n".join(kept) + "\n")

    n_hol = sum(1 for k in kept if "/src/HOL/" in k)
    print(f"{len(theories)} theories in the {args.session} heap")
    print(f"  dropped {dropped['non-corpus']} non-corpus (Pure / Tools / FOL / our own)")
    print(f"  dropped {dropped['HOL infra']} HOL tool/package/code-generation")
    print(f"  kept {len(kept)}: {n_hol} Isabelle/HOL + {len(kept) - n_hol} AFP -> {args.output}")


if __name__ == "__main__":
    main()
