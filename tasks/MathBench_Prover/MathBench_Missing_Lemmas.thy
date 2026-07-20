(*
  MathBench_Missing_Lemmas.thy

  Proof goals for the `not_found` library gaps surfaced by the missing-lemma
  loop (2026-06-18 fleet run). See MISSING_LEMMAS_REPORT.md for full provenance
  (English, why-needed, source case, caveats).

  STATUS: all statements TYPE-CHECK on the MathBench_Prover heap (parsed/debugged
  via isabelle-mcp, 2026-06-19); every proof is left as `sorry`. Type-checking is
  NOT semantic correctness -- review that each is the intended lemma before
  proving (several carry CAVEAT/TODO notes). Next: replace each `sorry`.

  Formalization decisions made while debugging (deviations from the raw English):
   - ml-0048 (Zolotarev): the heap has Residues.Legendre but NO Jacobi symbol, so
     this is stated for the PRIME case via Legendre (sign_mult_map_int_prime);
     the general odd-n Jacobi version needs a Jacobi symbol defined.
   - ml-0059/ml-0050 (cycle counts): no cycle API in the heap, so an inline
     `orbit_cycles` definition (cycle = orbit under repeated application) is used.
   - ml-0046/76 (det_block_bordered): bordered matrix indexed by `'n option`;
     c^T A^-1 b written as an explicit dot product (the `v*` notation is removed
     in MathBench_Prover).
   - ml-0018 (Fubini): written via the constant `interval_lebesgue_integral lborel`
     (the nested `LBINT ...` binder notation failed to parse).
   - ml-0028 (charpoly_2): over `real^2^2` so scaleR typechecks; generalize later.
  Many `$` / `\<chi>` usages rely on MathBench_Prover's notation reconciliation --
  that is why we import it.

  Two near-duplicate pairs are collapsed to one goal each
  (det_anti_diagonal: ml-0047/0075; det_block_bordered: ml-0046/0076).
  ml-0050 is the sigma^2 instance of ml-0059 -- prove ml-0059, derive ml-0050.
*)

theory MathBench_Missing_Lemmas
  imports MathBench_Prover.MathBench_Prover Minilang_AoA.Minilang_AoA
begin

declare [[auto_interpret_for_embedding=false, AoA_use_proof_cache=true, AoA_driver="ChatGPT.gpt-5.5-high" ]]

section \<open>Topic 1 -- Plane geometry on real^2 (putnam_1966_b5)\<close>

text \<open>ml-0013 not_collinear_imp_cross_product_nonzero (cleanest).\<close>
lemma not_collinear_imp_cross_product_nonzero:
  fixes a b c :: "real^2"
  assumes "\<not> collinear {a, b, c}"
  shows "(b$1 - a$1) * (c$2 - a$2) \<noteq> (b$2 - a$2) * (c$1 - a$1)"
  by aoa

text \<open>ml-0011 closed_segment_disjoint_if_disjoint_projection.
  CAVEAT: "any coordinate projection" pinned to the 1st coordinate.\<close>
lemma closed_segment_disjoint_if_disjoint_projection:
  fixes a b c d :: "real^2"
  assumes "((\<lambda>p. p$1) ` closed_segment a b) \<inter> ((\<lambda>p. p$1) ` closed_segment c d) = {}"
  shows "closed_segment a b \<inter> closed_segment c d = {}"
  by aoa

text \<open>ml-0012 segment_intersection_separated_by_line.
  Line = level set of a linear functional f; opposite closed half-planes.\<close>
lemma segment_intersection_separated_by_line:
  fixes f :: "real^2 \<Rightarrow> real" and z :: "real^2"
  assumes "linear f"
    and "\<forall>x \<in> closed_segment a b. f x \<le> k"
    and "\<forall>x \<in> closed_segment p q. f x \<ge> k"
    and "z \<in> closed_segment a b \<inter> closed_segment p q"
  shows "f z = k"
  sorry


section \<open>Topic 2 -- Convex/measure geometry on euclidean_space (putnam_1967_a5)\<close>

text \<open>ml-0014 Brunn_Minkowski_inequality.
  CAVEAT: deep theorem (not in HOL/AFP); needs measurability/boundedness hyps.
  Using real-valued `measure` (powr is real). Provide minimal hyps as a start.\<close>
lemma Brunn_Minkowski_inequality:
  fixes A B :: "('a::euclidean_space) set"
  assumes "A \<in> lmeasurable" "B \<in> lmeasurable" "A \<noteq> {}" "B \<noteq> {}"
    and "{a + b | a b. a \<in> A \<and> b \<in> B} \<in> lmeasurable"
  shows "(measure lebesgue {a + b | a b. a \<in> A \<and> b \<in> B}) powr (1 / real (DIM('a)))
       \<ge> (measure lebesgue A) powr (1 / real (DIM('a)))
       + (measure lebesgue B) powr (1 / real (DIM('a)))"
  sorry

text \<open>ml-0016 isodiametric_inequality. CAVEAT: substantial theorem.\<close>
lemma isodiametric_inequality:
  fixes S :: "('a::euclidean_space) set"
  assumes "S \<in> lmeasurable" "bounded S"
  shows "measure lebesgue S \<le> measure lebesgue (ball (0::'a) (diameter S / 2))"
  sorry


section \<open>Topic 3 -- Iterated/interval integration (putnam_1967_a4)\<close>

text \<open>ml-0018 interval_integral_Fubini (swap order over the triangle a<=x<=y<=b).
  CAVEAT: needs an integrability hypothesis on f over the triangle.\<close>
lemma interval_integral_Fubini:
  fixes f :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes "a \<le> b"
    \<comment> \<open>TODO: the precise integrability hypothesis (set_integrable on the triangle)\<close>
  shows "interval_lebesgue_integral lborel (ereal a) (ereal b)
           (\<lambda>x. interval_lebesgue_integral lborel (ereal x) (ereal b) (\<lambda>y. f x y))
       = interval_lebesgue_integral lborel (ereal a) (ereal b)
           (\<lambda>y. interval_lebesgue_integral lborel (ereal a) (ereal y) (\<lambda>x. f x y))"
  \<comment> \<open>LBINT x=a..b. g notation; written via the constant to avoid notation issues.\<close>
  sorry


section \<open>Topic 4 -- Counting solutions in a finite field (putnam_1968_b5)\<close>

text \<open>ml-0022 card_solutions_product_eq_zero.\<close>
lemma card_solutions_product_eq_zero:
  "card {(x, y). x * y = (0::'a::{finite,field})} = 2 * CARD('a) - 1"
  sorry

text \<open>ml-0023 card_solutions_product_eq_nonzero.\<close>
lemma card_solutions_product_eq_nonzero:
  fixes k :: "'a::{finite,field}"
  assumes "k \<noteq> 0"
  shows "card {(x, y). x * y = k} = CARD('a) - 1"
  sorry


section \<open>Topic 5 -- 2x2 matrices, trace/det (putnam_1969_b6)\<close>

text \<open>ml-0028 charpoly_2 (2x2 Cayley-Hamilton).
  CAVEAT: scaleR (the real-scalar action, written *_R) needs a real_vector; for a
  general comm_ring_1 use the matrix scalar action instead. Likely a corollary of
  Lie_Groups.Transfer_Cayley_Hamilton. Drafted over real entries so scaleR
  typechecks; generalize in Phase 2.\<close>
lemma charpoly_2:
  fixes A :: "real^2^2"
  shows "A ** A = trace A *\<^sub>R A - det A *\<^sub>R mat 1"
  sorry

text \<open>ml-0029 trace_sq_2.\<close>
lemma trace_sq_2:
  fixes A :: "('a::comm_ring_1)^2^2"
  shows "trace (A ** A) = (trace A)^2 - 2 * det A"
  sorry


section \<open>Topic 6 -- Formal power series (putnam_1970_a1)\<close>

text \<open>ml-0033 fps_nth_exp_times_cos.
  CAVEAT: pin coefficient rings; a,b real, RHS via complex.\<close>
lemma fps_nth_exp_times_cos:
  fixes a b :: real
  shows "fps_nth (fps_exp a * fps_cos b) n
       = Re ((of_real a + \<i> * of_real b)^n) / fact n"
  sorry


section \<open>Topic 7 -- Riemann sum to integral (putnam_1970_b1)\<close>

text \<open>ml-0035 uniform_riemann_sum_tendsto_integral (the general reusable form).\<close>
lemma uniform_riemann_sum_tendsto_integral:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "continuous_on {a..b} f"
  shows "(\<lambda>n. ((b - a) / real n) * (\<Sum>i=1..n. f (a + real i * (b - a) / real n)))
         \<longlonglongrightarrow> integral {a..b} f"
  sorry


section \<open>Topic 8 -- Determinants of structured matrices on 'a^'n^'n (putnam_2023_b6)\<close>

text \<open>ml-0047 = ml-0075 det_anti_diagonal.
  Cleanest route: anti-diagonal 0/1 matrix = permutation matrix of the reversal
  permutation; det = of_int (sign rev) = (-1)^(n*(n-1)/2). The "i+j=n+1" form
  needs an explicit enumeration 'n =~ {1..n}; flagged for Phase 2.
  Draft below uses a reversal permutation `r` on the index type.\<close>
lemma det_anti_diagonal:
  fixes r :: "'n \<Rightarrow> ('n::finite)"
  assumes "bij r" "\<forall>i. r (r i) = i"   \<comment> \<open>r is the order-reversing involution\<close>
  shows "det (\<chi> i j. if j = r i then (1::'a::comm_ring_1) else 0)
       = (- 1)^(CARD('n) * (CARD('n) - 1) div 2)"
  sorry

text \<open>ml-0046 = ml-0076 det_block_bordered (Schur complement).
  CAVEAT: hardest to state for general 'n -- needs a distinguished last index and
  the bordered construction. This is a PLACEHOLDER shape; Phase-2 must redesign
  the indexing (e.g. on 'n + unit, or an explicit Suc n) before it can elaborate.\<close>
lemma det_block_bordered:
  fixes A :: "('a::field)^'n^'n" and b c :: "'a^'n" and d :: 'a
  assumes "invertible A"
  shows "det (\<chi> (i::'n option) (j::'n option).
               case (i, j) of
                 (None, None) \<Rightarrow> d
               | (None, Some j') \<Rightarrow> c $ j'
               | (Some i', None) \<Rightarrow> b $ i'
               | (Some i', Some j') \<Rightarrow> A $ i' $ j')
       = det A * (d - (\<Sum>i\<in>UNIV. c $ i * ((matrix_inv A *v b) $ i)))"
  \<comment> \<open>the scalar (c-transpose)(A-inverse)(b) written as an explicit dot product
       (the v-star vector*matrix notation is removed in MathBench_Prover).\<close>
  sorry


section \<open>Topic 9 -- Permutations / Zolotarev (putnam_2023_b5)\<close>

text \<open>ml-0048 sign_mult_map_int (Zolotarev's lemma).
  The heap has `Residues.Legendre` but NO Jacobi symbol, so we state the PRIME
  case (Zolotarev's original: the sign of x |-> a*x mod p is the Legendre symbol
  (a/p)). The general odd-n version needs a Jacobi symbol (= product of Legendre
  over prime factors of n), to be defined/imported separately.
  CAVEAT: `sign` is on int=>int here; restrict to the permutation of {0..<p}.\<close>
lemma sign_mult_map_int_prime:
  fixes a :: int and p :: nat
  assumes "prime p" "odd p" "coprime a (int p)"
  shows "sign (\<lambda>x. (a * x) mod (int p)) = Legendre a (int p)"
  sorry

text \<open>No cycle-decomposition API in this heap (no cycles_of / cycle_type /
  count_cycles constant), so define the orbit-cycle set inline: the cycle through
  x is its orbit under repeated application of f.\<close>
definition orbit_cycles :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "orbit_cycles f S = (\<lambda>x. {y. \<exists>k. y = (f ^^ k) x}) ` S"

text \<open>ml-0059 square_permutation_even_cycle_count (general; ml-0050 is its sigma^2 case).
  (Renamed cycle variable \<ell> -> l: \<ell> is not a valid inner-syntax identifier.)\<close>
lemma square_permutation_even_cycle_count:
  fixes \<tau> :: "'a \<Rightarrow> 'a"
  assumes "finite S"
    and "\<exists>\<sigma>. \<sigma> permutes S \<and> \<sigma> \<circ> \<sigma> = \<tau>"
    and "even l"
  shows "even (card {C \<in> orbit_cycles \<tau> S. card C = l})"
  sorry

text \<open>ml-0050 square_cycle_decomposition -- the operative consequence (sigma^2 case).
  Derivable from square_permutation_even_cycle_count with tau = sigma o sigma.\<close>
lemma square_cycle_decomposition_even_count:
  fixes \<sigma> :: "'a \<Rightarrow> 'a"
  assumes "\<sigma> permutes S" "finite S" "even l"
  shows "even (card {C \<in> orbit_cycles (\<sigma> \<circ> \<sigma>) S. card C = l})"
  sorry

text \<open>ml-0058 sign_negation_map.
  CAVEAT: pin the domain {1..n} and that this is a permutation of it.\<close>
lemma sign_negation_map:
  fixes n :: int
  shows "sign (\<lambda>k. if k = n then n else n - k)
       = (if even n then (- 1::int)^(nat ((n - 2) div 2))
                    else (- 1::int)^(nat ((n - 1) div 2)))"
    \<comment> \<open>TODO: restrict to the permutation of {1..n}; current lambda is on all int\<close>
  sorry

end
