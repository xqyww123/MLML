# Missing-lemma report — `not_found` library gaps (2026-06-18 fleet run)

Source: `missing_lemma_loop_state/ledger.json` on the cluster, status `not_found`
(genuine library gaps the prover surveyed and the confirmation agent could not
locate in HOL+AFP). 20 ledger entries → **18 distinct lemmas** after collapsing
two near-duplicate pairs. Companion proof goals:
[`MathBench_Missing_Lemmas.thy`](./MathBench_Missing_Lemmas.thy).

**STATUS (updated 2026-06-19): the goal statements in
`MathBench_Missing_Lemmas.thy` now TYPE-CHECK** on the `MathBench_Prover` heap
(parsed/debugged via isabelle-mcp); every proof is left as `sorry`. The English
drafts below were the starting point — some were changed during debugging to use
real heap constants; see the theory header for the exact deviations. Key ones:
ml-0048 weakened to the prime case via `Residues.Legendre` (no Jacobi symbol in
the heap); ml-0059/ml-0050 use an inline `orbit_cycles` definition (no cycle API);
ml-0018 written via `interval_lebesgue_integral lborel`; det_block bordered on
`'n option`. **Type-checking ≠ correctness** — review each statement is the
intended lemma before proving.

Index uses the `$` from `Finite_Cartesian_Product` (vec) and the `\<chi>` matrix
binder — both are made available by `MathBench_Prover.thy`'s notation
reconciliation (it `no_notation`s the JNF/`fds`/`fps` claimants of `$` and
`\<chi>`), which is why the goal theory imports `MathBench_Prover`.

---

## Topic 1 — Plane geometry on `real^2` (putnam_1966_b5)
Env has `Tarskis_Geometry` / `IsaGeoCoq` (real² plane model) + HOL-Analysis
`closed_segment`, `collinear`.

- **ml-0011 `closed_segment_disjoint_if_disjoint_projection`**
  EN: If the x-projection (any fixed coordinate projection) of two closed
  segments are disjoint, the segments are disjoint.
  Why: non-adjacent edges of an x-monotone chain don't intersect.
  Draft: `((λp. p$1) ` closed_segment a b) ∩ ((λp. p$1) ` closed_segment c d) = {}
  ⟹ closed_segment a b ∩ closed_segment c d = {}`.
  Caveat: "or any coordinate projection" is a generalization; pin to the
  1st coordinate (the case actually used).

- **ml-0012 `segment_intersection_separated_by_line`**
  EN: Two closed segments in opposite closed half-planes of a line, with
  nonempty intersection ⟹ the intersection point lies on the line.
  Why: upper-chain vs lower-chain edges don't cross.
  Draft (line as level set of a linear functional `f`):
  `linear f ⟹ (∀x∈closed_segment a b. f x ≤ c) ⟹ (∀x∈closed_segment p q. f x ≥ c)
  ⟹ z ∈ closed_segment a b ∩ closed_segment p q ⟹ f z = c`.

- **ml-0013 `not_collinear_imp_cross_product_nonzero`** (cleanest — EN gives the algebra)
  Draft: `¬ collinear {a,b,c} ⟹ (b$1 - a$1)*(c$2 - a$2) ≠ (b$2 - a$2)*(c$1 - a$1)`
  for `a b c :: real^2`.

## Topic 2 — Convex/measure geometry on `'a::euclidean_space` (putnam_1967_a5)
Used to bound area by diameter. Env has `HOL-Analysis` Lebesgue measure.

- **ml-0014 `Brunn_Minkowski_inequality`**
  EN: `measure(A+B)^(1/n) ≥ measure(A)^(1/n) + measure(B)^(1/n)`, `A+B = {a+b}`.
  Draft: `(measure lebesgue {a+b | a b. a∈A ∧ b∈B}) powr (1/DIM('a)) ≥
  measure lebesgue A powr (1/DIM('a)) + measure lebesgue B powr (1/DIM('a))`.
  Caveat: needs measurability + boundedness/nonemptiness hyps; decide
  `measure` (real, with finiteness) vs `emeasure` (ennreal) — `powr` is real, so
  `measure` is the workable choice. This is a deep theorem (not in HOL/AFP).

- **ml-0016 `isodiametric_inequality`**
  Draft: `S ∈ lmeasurable ⟹ bounded S ⟹
  measure lebesgue S ≤ measure lebesgue (ball (0::'a) (diameter S / 2))`.
  Caveat: also a substantial theorem; same emeasure/measure decision.

## Topic 3 — Iterated/interval integration (putnam_1967_a4)
- **ml-0018 `interval_integral_Fubini`** (swap order over a triangle)
  Survey draft: `(LBINT x=ereal a..ereal b. LBINT y=ereal x..ereal b. f x y)
  = (LBINT y=ereal a..ereal b. LBINT x=ereal a..ereal y. f x y)`.
  Caveat: needs integrability of `f` on the triangle `{(x,y). a≤x≤y≤b}`
  (e.g. `set_integrable` / continuity); HOL has `interval_lebesgue_integral`
  Fubini pieces but not this triangular-swap as a single lemma.

## Topic 4 — Counting solutions in a finite field (putnam_1968_b5)
`'a :: {finite, field}`, `CARD('a) = q`.
- **ml-0022 `card_solutions_product_eq_zero`**
  Draft: `card {(x,y)::'a×'a. x*y = 0} = 2 * CARD('a) - 1`.
- **ml-0023 `card_solutions_product_eq_nonzero`**
  Draft: `k ≠ 0 ⟹ card {(x,y)::'a×'a. x*y = k} = CARD('a) - 1`.
  (Both clean; provable from `field` zero-divisor / multiplicative-group facts.)

## Topic 5 — 2×2 matrices, trace/det (putnam_1969_b6) on `('a::comm_ring_1)^2^2`
Env has `Lie_Groups.Transfer_Cayley_Hamilton` (general Cayley–Hamilton on `'a^'n^'n`).
- **ml-0028 `charpoly_2`** (2×2 Cayley–Hamilton)
  Survey draft: `A ** A = trace A *⇩R A - det A *⇩R mat 1`.
  Caveat: `*⇩R` (scaleR) needs a real_vector; for a general `comm_ring_1` the
  scalar action is matrix scalar mult `*ₛ`/`*k` (or `( *⇩s )`). Likely a corollary
  of the transferred Cayley–Hamilton — check what scalar operator typechecks.
- **ml-0029 `trace_sq_2`**
  Draft: `trace (A ** A) = (trace A)^2 - 2 * det A` for `A :: 'a^2^2`.
  (Clean over the ring; pure trace/det algebra on 2×2.)

## Topic 6 — Formal power series (putnam_1970_a1)
- **ml-0033 `fps_nth_exp_times_cos`**
  EN: nth coeff of `fps_exp a * fps_cos b` is `Re((a+ib)^n)/n!`.
  Draft: `fps_nth (fps_exp a * fps_cos b) n
  = Re ((of_real a + 𝗂 * of_real b)^n) / fact n` with `a b :: real`.
  Caveat: pin the FPS coefficient ring; `fps_cos`/`fps_exp` over `real`, RHS via
  `complex`. May instead want the statement over `complex` FPS directly.

## Topic 7 — Riemann sum → integral (putnam_1970_b1)
- **ml-0035 `uniform_riemann_sum_tendsto_integral`** (the general reusable form)
  Survey draft (good): `continuous_on {a..b} f ⟹
  (λn. ((b - a)/real n) * (∑i=1..n. f (a + real i * (b - a)/real n))) ⇢ integral {a..b} f`
  for `f :: real ⇒ real`, `a < b`. Caveat: add `a ≤ b`; `⇢` = `LIMSEQ`.

## Topic 8 — Determinants of structured matrices on `'a^'n^'n` (putnam_2023_b6)
- **ml-0047 = ml-0075 `det_anti_diagonal`** (DUPLICATE pair)
  EN: det of the anti-diagonal 0/1 matrix = `(-1)^(n*(n-1)/2)`, `n = CARD('n)`.
  Cleanest formalization: the anti-diagonal matrix is the **permutation matrix of
  the reversal permutation** `rev`, so `det = of_int (sign rev)` and
  `sign rev = (-1)^(n*(n-1) div 2)`. Draft:
  `det (χ i j. if j = rev_perm i then 1 else 0) = (-1::'a)^(CARD('n)*(CARD('n)-1) div 2)`
  where `rev_perm` is the order-reversing bijection on `'n`.
  Caveat: "`i+j=n+1`" needs an explicit enumeration `'n ≅ {1..n}`; the
  permutation-matrix route avoids ad-hoc indexing.

- **ml-0046 = ml-0076 `det_block_bordered` (Schur complement)** (DUPLICATE pair)
  EN: `det [A b; c^T d] = det A · (d − c^T A⁻¹ b)` for invertible `A` (size n−1);
  if `A` is its own inverse (anti-diagonal), `= det A · (d − c^T A b)`.
  Caveat: hardest to state for general `'n` — needs a distinguished last index
  and the bordered construction on `'a^'n^'n`. Likely state on `'a^('n::...)` with
  an explicit `n+1` index sum type, or via `HOL-Analysis` block-matrix tooling.
  Flag for Phase-2 design.

## Topic 9 — Permutations / Zolotarev (putnam_2023_b5)
- **ml-0048 `sign_mult_map_int`** (Zolotarev's lemma)
  EN: for odd `n>0`, `sign (x ↦ a*x on ℤ/nℤ) = Jacobi (a, n)`.
  Draft: `coprime a (int n) ⟹ odd n ⟹ 0 < n ⟹
  sign (mult_perm a n) = Jacobi a (int n)` where `mult_perm a n` is the
  permutation of `{0..<n}` (or residues) `x ↦ (a*x) mod n`.
  Caveat: confirm a `Jacobi` symbol exists in HOL-Number_Theory (else define);
  `coprime` precondition is required (else not a permutation).

- **ml-0050 `square_cycle_decomposition`** (operative consequence)
  Full prose (odd cycles persist, even 2k-cycles split into two k-cycles) is
  awkward as one term; state the **consequence actually used**:
  `σ permutes S ⟹ finite S ⟹ even ℓ ⟹
  even (card {C ∈ cycles_of (σ ∘ σ). card C = ℓ})`.
  Caveat: pick the cycle-set API (`HOL-Combinatorics` cycles / `cycle_type`).

- **ml-0058 `sign_negation_map`**
  Survey draft: `sign (λk. if k = n then n else n - k)
  = (if even n then (-1::int)^((n-2) div 2) else (-1::int)^((n-1) div 2))`.
  Caveat: pin the domain (`{1..n}`) and that this is a permutation of it.

- **ml-0059 `square_permutation_even_cycle_count`**
  EN: if `τ = σ²` then for every even `ℓ` the number of `ℓ`-cycles of `τ` is even.
  Draft: `finite S ⟹ (∃σ. σ permutes S ∧ σ ∘ σ = τ) ⟹
  even ℓ ⟹ even (card {C ∈ cycles_of τ. card C = ℓ})`.
  (Generalizes ml-0050; ml-0050 is the σ²-specialised statement.)

---

## Provenance & dedup notes
- Two near-duplicate pairs (`det_anti_diagonal` ml-0047/ml-0075, `det_block_bordered`
  ml-0046/ml-0076) escaped dedup because the adjudication round that would have
  collapsed them was interrupted by the slurmx deadlock (their `unresolvable
  duplicate_of chain` warnings). Treat each pair as ONE lemma.
- ml-0050 and ml-0059 overlap (ml-0050 is the σ² instance of ml-0059's general
  square statement) — prove ml-0059, derive ml-0050.
- ml-0014/ml-0016 (Brunn–Minkowski / isodiametric) are deep theorems not in
  HOL/AFP — substantial proof effort; consider whether the case really needs the
  full inequality or a weaker bound.

## Suggested proving order (easy → hard)
1. ml-0013, ml-0022, ml-0023, ml-0029 (elementary algebra/counting).
2. ml-0035 (Riemann sum — standard HOL-Analysis), ml-0028 (from Cayley–Hamilton),
   ml-0011, ml-0012 (segment geometry).
3. ml-0033 (FPS bookkeeping), ml-0047/0075 (permutation-matrix det),
   ml-0058, ml-0059/0050 (cycle counting), ml-0048 (Zolotarev — may need Jacobi).
4. ml-0018 (triangular Fubini), ml-0046/0076 (Schur complement on `'a^'n^'n`),
   ml-0014, ml-0016 (Brunn–Minkowski / isodiametric — research-grade).
