(*  Title:      Env_Dump.thy

Generate the MathBench_Prover "environment reference" used by
tools/check_putnam_divergence.py. Load this theory in a MathBench-capable
Isabelle session (it imports MathBench_Prover, hence needs its heap), and it
writes three reference files to /tmp:

  /tmp/mathbench_const.tsv     constant short-name -> resolved long name
  /tmp/mathbench_type.tsv      type short-name     -> resolved long name
  /tmp/mathbench_notation.txt  Syntax.print_syntax output (mixfix / 符号)

Then run:  python tools/check_putnam_divergence.py
which dumps the same data for every PutnamBench import combination (via a plain
HOL REPL) and reports every divergence from this reference.

Kept out of MathBench_Prover.thy on purpose, so normal proving loads do not
write to /tmp as a side effect.
*)

theory Env_Dump
  imports MathBench_Prover
begin

ML_file \<open>env_dump.ML\<close>

ML \<open>
Env_Dump.dump_all \<^context>
  {const = "/tmp/mathbench_const.tsv",
   typ = "/tmp/mathbench_type.tsv",
   notation = "/tmp/mathbench_notation.txt"}
\<close>

end
