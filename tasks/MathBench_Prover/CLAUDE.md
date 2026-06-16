# MathBench_Prover

## Building the session heaps

Build both `MathBench_ProverBase` (the heavy AFP heap) and `MathBench_Prover`
(the child that loads the reconciliation + tactics on top) with:

```
source envir.sh    # puts Isabelle2025-2 on PATH
RPC_Host=127.0.0.1:27180 isabelle build -b -o threads=10 -o system_heaps MathBench_Prover MathBench_ProverBase
```

- `-b` writes the heap image; `-o system_heaps` stores it under the Isabelle
  system heap dir; `-o threads=10` parallelises.
- `RPC_Host` points the Isabelle_RPC server that `Auto_Sledgehammer` depends on at
  this address; the server auto-launches if not already running, so just set the
  value — you do not need to start a service yourself.
- `isabelle build MathBench_Prover` builds its parent `MathBench_ProverBase`
  first automatically; listing both just refreshes both heaps.

## Layout

- `Base/MathBench_ProverBase.thy` — the AFP `imports` list (heavy, prebuilt heap).
  New library imports go here; rebuild the heap after editing.
- `MathBench_Prover.thy` — imports the base + `Auto_Sledgehammer`; body holds the
  name/notation reconciliation (`no_notation`/`hide_const`) and proof tooling.
- `ROOT` — session definitions; a new AFP import must also be added to the
  `sessions` clause of `MathBench_ProverBase`.

See the `mathbench-import-reconcile` skill for validating that a new import does
not change any PutnamBench goal term (goal-term gate + divergence radar).
