theory MathBench_Prover
  imports Auto_Sledgehammer.Auto_Sledgehammer MathBench_ProverBase.MathBench_ProverBase
begin

no_notation fds (binder "χ" 10)
no_notation fps_nth (infixl "$" 75)
no_notation fds_nth (infixl "$" 75)
no_notation Matrix.vec_index (infixl "$" 100)
no_notation blinfun_apply (infixl "$" 999)
no_notation fds (binder "\<chi>" 10)
no_notation Matrix.scalar_prod (infix "\<bullet>" 70)
no_notation BNF_Cardinal_Arithmetic.cprod (infixr "*c" 80)
no_notation BNF_Cardinal_Arithmetic.csum (infixr "+c" 65)
no_notation BNF_Cardinal_Arithmetic.cexp (infixr "^c" 90)
no_notation BNF_Wellorder_Constructions.ordIso2 (infix "=o" 50)
no_notation BNF_Wellorder_Constructions.ordLess2 (infix "<o" 50)
no_notation BNF_Wellorder_Constructions.ordLeq2 (infix "<=o" 50)
no_notation matrix_scalar_mult (infixl "*k" 70)
no_notation smult_sq_matrix (infixr "*s" 75)
no_notation matrix_vector_mult_iarray (infixl "*iv" 70)
no_notation vector_matrix_mult_iarray (infixl "v*i" 70)
no_notation vector_matrix_mult (infixl "v*" 70)
no_notation word_sless ("'(<s')")
no_notation word_sless ("(_/ <s _)"  [51, 51] 50)
no_notation word_sle ("'(<=s')")
no_notation word_sle ("(_/ <=s _)" [51, 51] 50)
no_notation Set_Algebras.elt_set_times (infixl "*o" 80)
no_notation Set_Algebras.elt_set_plus (infixl "+o" 70)
no_notation Set_Algebras.elt_set_eq (infix "=o" 50)

no_syntax (ASCII)
  "_Sum_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add" ("(3SUM _. _)" [0, 10] 10)
no_syntax
  "_Sum_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add" ("(3\<Sum>_. _)" [0, 10] 10)
no_translations
  "\<Sum>a. b" \<rightleftharpoons> "CONST Sum_any (\<lambda>a. b)"

hide_type (open) Commutative_Ring.pol Commutative_Ring.polex Commutative_Ring.mon
  Reflective_Field.fexpr Reflective_Field.pexpr Reflective_Field.pexpr1 Reflective_Field.pexpr2
  Matrix.mat Matrix.vec

hide_const (open)
  Commutative_Ring.Pc Commutative_Ring.Pinj Commutative_Ring.PX
  Commutative_Ring.Var Commutative_Ring.Const Commutative_Ring.Add
  Commutative_Ring.Sub Commutative_Ring.Mul Commutative_Ring.Pow Commutative_Ring.Neg
  Commutative_Ring.Mc Commutative_Ring.Minj Commutative_Ring.MX
  Commutative_Ring.mkPinj Commutative_Ring.mkPX
  Commutative_Ring.add Commutative_Ring.mul Commutative_Ring.neg
  Commutative_Ring.sub Commutative_Ring.sqr Commutative_Ring.pow Commutative_Ring.norm
  Commutative_Ring.mkMinj Commutative_Ring.Minj_pred
  Commutative_Ring.mkMX Commutative_Ring.cfactor Commutative_Ring.mfactor
  Commutative_Ring.mon_of_pol Commutative_Ring.mk_monpol_list
  Commutative_Ring.ponesubst Commutative_Ring.pnsubst1 Commutative_Ring.pnsubst
  Commutative_Ring.psubstl1 Commutative_Ring.psubstl Commutative_Ring.pnsubstl
  Reflective_Field.FCnst Reflective_Field.FVar Reflective_Field.FAdd
  Reflective_Field.FSub Reflective_Field.FMul Reflective_Field.FNeg
  Reflective_Field.FDiv Reflective_Field.FPow
  Reflective_Field.PExpr1 Reflective_Field.PExpr2
  Reflective_Field.PCnst Reflective_Field.PVar Reflective_Field.PAdd
  Reflective_Field.PSub Reflective_Field.PNeg
  Reflective_Field.PMul Reflective_Field.PPow
  Reflective_Field.npepow Reflective_Field.npemul Reflective_Field.npeadd
  Reflective_Field.npesub Reflective_Field.npeneg
  Reflective_Field.isin Reflective_Field.split_aux Reflective_Field.fnorm
  MPoly_Type.degree MPoly_Type.monom MPoly_Type.coeff MPoly_Type.smult MPoly_Type.coeffs
  up_ring.monom up_ring.coeff module.smult Unique_Factorization.coprime
  Henstock_Kurzweil_Integration.content
  (* Record selectors: align resolution with PutnamBench (avoid AFP-only winners) *)
  UnivPoly.up_ring.extend UnivPoly.up_ring.fields UnivPoly.up_ring.make
  UnivPoly.up_ring.more UnivPoly.up_ring.more_update UnivPoly.up_ring.truncate
  Module.module.extend Module.module.fields Module.module.make
  Module.module.more Module.module.more_update Module.module.truncate
  Ring.ring.extend Ring.ring.fields Ring.ring.make
  Ring.ring.more Ring.ring.more_update Ring.ring.truncate
  Group.monoid.extend Group.monoid.fields Group.monoid.make
  Group.monoid.more Group.monoid.more_update Group.monoid.truncate
  Group.monoid.mult
  Square_Matrix.det Square_Matrix.trace Square_Matrix.transpose Square_Matrix.row
  Square_Matrix.adjugate Square_Matrix.diag Square_Matrix.map_sq_matrix
  Sturm_Tarski.sign Sturm_Tarski.cross Sturm_Tarski.changes
  Sturm_Tarski.variation Sturm_Tarski.taq
  Sturm_Tarski.sgn_pos_inf Sturm_Tarski.sgn_neg_inf
  Sturm_Tarski.sign_r_pos Sturm_Tarski.jump_poly Sturm_Tarski.cindex_poly
  Sturm_Tarski.smods Sturm_Tarski.changes_poly_at
  Sturm_Tarski.changes_poly_pos_inf Sturm_Tarski.changes_poly_neg_inf
  Sturm_Tarski.changes_itv_smods Sturm_Tarski.changes_gt_smods
  Sturm_Tarski.changes_le_smods Sturm_Tarski.changes_R_smods
  Symmetric_Polynomials.lead_coeff Symmetric_Polynomials.lead_monom
  (* HOL-Algebra: only hide constants NOT used by PutnamBench.
     PutnamBench USES: group, carrier, field, subgroup, generate, comm_group,
     abelian_group, one (\<one>), zero (\<zero>), vangle — keep these OPEN. *)
  Coset.order
  Groups.group_axioms
  Group.group_hom Group.group_isomorphisms
  Group.DirProd Group.submonoid
  Group.hom Group.is_iso Group.mon Group.epi
  Group.Units Group.units_of Group.pow
  Coset.kernel Coset.flatten
  Coset.l_coset Coset.r_coset Coset.r_congruent
  Coset.RCOSETS Coset.SET_INV Coset.FactGroup Coset.trivial_homomorphism
  Ring.ring Ring.cring Ring.semiring
  Ring.ring_hom_cring Ring.abelian_monoid
  Ring.finsum Ring.add_monoid Ring.add_pow Ring.a_inv Ring.a_minus
  Ring.ring.add Ring.ring.zero
  Ideal.ideal Ideal.primeideal Ideal.maximalideal Ideal.principalideal
  Ideal.genideal Ideal.cgenideal
  Congruence.eq_object.eq
  Congruence.elem Congruence.not_elem Congruence.equivalence
  Congruence.eq_classes Congruence.eq_class_of Congruence.eq_closure_of
  Congruence.eq_is_closed Congruence.not_eq Congruence.set_eq Congruence.set_not_eq
  Order.gorder.le Order.lless Order.bottom
  Order.isotone Order.idempotent Order.least Order.greatest Order.commuting
  Order.at_least_at_most Order.inv_gorder Order.is_glb Order.is_lub
  Order.Lower Order.Upper Order.Monotone Order.order_emb
  Order.partial_order Order.total_order
  Order.weak_partial_order Order.weak_partial_order_bottom
  Order.weak_partial_order_top Order.weak_total_order
  Lattice.meet Lattice.supr Lattice.infi
  Lattice.lattice Lattice.bounded_lattice Lattice.LEAST_FP Lattice.GREATEST_FP
  Lattice.join_pres Lattice.meet_pres
  Lattice.lower_semilattice Lattice.upper_semilattice
  Lattice.weak_lattice Lattice.weak_lower_semilattice Lattice.weak_upper_semilattice
  Lattice.weak_bounded_lattice
  FiniteProduct.finprod FiniteProduct.foldD
  FiniteProduct.foldSetD FiniteProduct.foldSetDp FiniteProduct.ACeD FiniteProduct.LCD
  AbelCoset.abelian_group_hom AbelCoset.abelian_subgroup AbelCoset.additive_subgroup
  AbelCoset.A_FactGroup AbelCoset.a_kernel AbelCoset.a_l_coset
  AbelCoset.a_r_congruent AbelCoset.a_r_coset AbelCoset.A_RCOSETS
  AbelCoset.A_SET_INV AbelCoset.set_add
  Generated_Groups.generatep
  Generated_Groups.derived Generated_Groups.derived_set
  Generated_Groups.subgroup_generated
  (* Budan_Fourier / Count_Complex_Roots / Extended_Sturm *)
  BF_Misc.fcompose BF_Misc.proots_count BF_Misc.proots_within
  Budan_Fourier.all_roots_real Budan_Fourier.pders
  Budan_Fourier.changes_itv_der Budan_Fourier.changes_gt_der Budan_Fourier.changes_le_der
  Extended_Sturm.changes_alt Extended_Sturm.cross_alt
  Extended_Sturm.changes_alt_itv_smods Extended_Sturm.changes_alt_poly_at
  Extended_Sturm.cindex_polyE Extended_Sturm.cindex_poly_ubd
  Extended_Sturm.cindexP_pathE Extended_Sturm.cindexP_lineE
  Extended_Sturm.jumpF_polyR Extended_Sturm.jumpF_polyL
  Extended_Sturm.jumpF_poly_top Extended_Sturm.jumpF_poly_bot
  Extended_Sturm.psign_diff Extended_Sturm.psign_aux Extended_Sturm.cdiff_aux
  Count_Line.unbounded_line Count_Line.proots_line Count_Line.proots_line_card
  Count_Line.proots_unbounded_line Count_Line.proots_unbounded_line_card
  Count_Line.no_proots_line
  Count_Circle.proots_ball Count_Circle.proots_ball_card
  Count_Circle.proots_cball Count_Circle.proots_cball_card
  Count_Circle.proots_sphere Count_Circle.proots_sphere_card
  Count_Half_Plane.proots_upper Count_Half_Plane.proots_upper_card
  Count_Half_Plane.proots_half
  Count_Rectangle.proots_rect Count_Rectangle.proots_crect
  Count_Rectangle.proots_rect_border Count_Rectangle.proots_rect_ll
  Count_Rectangle.not_rect_vertex Count_Rectangle.not_rect_vanishing
  (* Angles: angle is locally defined in putnam_1972_b5, safe to hide *)
  Angles.angle
  (* JNF: import reorder insufficient, explicit hide needed *)
  Determinant.det
  Matrix.mat Matrix.row Matrix.col Matrix.scalar_prod Matrix.orthogonal
  Matrix.zero_vec
  (* Cayley_Hamilton: C and X shadow common free variables *)
  Cayley_Hamilton.C Cayley_Hamilton.X
  (* Perm: order shadows Polynomial.order, swap shadows Product_Type.prod.swap *)
  Perm.order Perm.swap
  (* Miscellaneous.linear from Rank_Nullity_Theorem shadows HOL-Analysis linear *)
  Miscellaneous.linear
  (* Diagonal_Subsequence.subseqs shadows List.subseqs *)
  Diagonal_Subsequence.subseqs
  (* MPoly_Type.Var shadows free variable Var *)
  MPoly_Type.Var
  (* Topology class shadows from AFP *)
  Abstract_Topological_Spaces.t0_space
  T1_Spaces.t1_space

declare [[coercion_delete "enat :: nat \<Rightarrow> enat"]]
declare [[coercion_delete "of_nat :: nat \<Rightarrow> ennreal"]]

declare [[smt_oracle, z3_extensions, smt_nat_as_int]]
setup \<open>Context.theory_map (Config.put_generic Pre_Simproc.simplify_timeout_seconds 60)\<close>
declare [[auto_sledgehammer_params = "provers = verit z3 e spass vampire zipperposition cvc5, smt_proofs = true"]]


theorem sqrt_prime_irrational:
  fixes p :: int
  assumes x: "prime p"
  shows "sqrt p \<notin> \<rat>"
proof
  from \<open>prime p\<close> have p: "p > 1"
    using prime_gt_1_int by blast
  assume "sqrt p \<in> \<rat>"
  then obtain m n :: nat
    where n: "n \<noteq> 0"
      and sqrt_rat: "\<bar>sqrt p\<bar> = m / n"
      and "coprime m n" by (rule Rats_abs_nat_div_natE)
  have eq: "m\<^sup>2 = p * n\<^sup>2"
  proof -
    from n and sqrt_rat have "m = \<bar>sqrt p\<bar> * n" by simp
    then have "m\<^sup>2 = (sqrt p)\<^sup>2 * n\<^sup>2" by (simp add: power_mult_distrib)
    also have "(sqrt p)\<^sup>2 = p"
      by (simp add: assms prime_ge_0_int)
    also have "\<dots> * n\<^sup>2 = p * n\<^sup>2" by simp
    finally show ?thesis by linarith
  qed
  have "p dvd m \<and> p dvd n"
  proof
    from eq have "p dvd m\<^sup>2" ..
    with \<open>prime p\<close> show "p dvd m"
      by (simp add: prime_dvd_power_int_iff)
    then obtain k where "m = p * k" ..
    with eq have "p * n\<^sup>2 = p\<^sup>2 * k\<^sup>2"
      by (simp add: power_mult_distrib)
    with p have "n\<^sup>2 = p * k\<^sup>2" by (simp add: power2_eq_square)
    then have "p dvd n\<^sup>2" ..
    with \<open>prime p\<close> show "p dvd n"
      by (metis coprime_dvd_mult_left_iff int_ops(7) power2_eq_square prime_imp_coprime)
  qed
  then have "p dvd gcd m n"
    using \<open>coprime m n\<close> coprime_common_divisor coprime_int_iff by blast
  with \<open>coprime m n\<close> have "p = 1"
    using p by force
  with p show False by simp
qed

lemma multiplicity_code [code]:
  "multiplicity p x =
     (if p = 0 \<or> is_unit p \<or> x = 0 then 0
      else if p dvd x then 1 + multiplicity p (x div p) else 0)"
proof (cases "p = 0 \<or> is_unit p \<or> x = 0")
  case True
  then show ?thesis by (auto simp: multiplicity_unit_left)
next
  case False
  then have h: "p \<noteq> 0" "\<not> is_unit p" "x \<noteq> 0" by auto
  show ?thesis
  proof (cases "p dvd x")
    case False
    with h show ?thesis by (simp add: not_dvd_imp_multiplicity_0)
  next
    case True
    with h have eq: "p * (x div p) = x" by simp
    with h have "x div p \<noteq> 0" by auto
    with h have "multiplicity p (p * (x div p)) = Suc (multiplicity p (x div p))"
      by (intro multiplicity_times_same)
    with eq True h show ?thesis by simp
  qed
qed

ML \<open>
structure Sqrt_Prime_Rat = struct
fun simproc ctxt ct =
  let
    val ((_ $ (_ $ (_ $ bits))) $ _) = Thm.term_of ct
  in
    @{lemma \<open>prime (numeral n :: int) \<Longrightarrow> (sqrt (numeral n :: real) \<in> \<rat>) = False\<close> for n
         by (metis sqrt_prime_irrational[of "numeral n"] of_int_eq_numeral_iff)}
    |> Thm.instantiate' [] [SOME (Thm.cterm_of ctxt bits)]
    |> (fn thm => thm RS @{thm eq_reflection})
    |> SOME
  end
  handle Match => NONE | THM _ => NONE
end
\<close>

simproc_setup sqrt_prime_rat (\<open>sqrt (numeral n) \<in> \<rat>\<close>) =
  \<open>K Sqrt_Prime_Rat.simproc\<close>

ML_file \<open>eval_simproc.ML\<close>

simproc_setup eval_ord ("ord m n") =
  \<open>K (Eval_Simproc.eval_ground 5)\<close>

simproc_setup eval_cong ("[a = b] (mod c)") =
  \<open>K (Eval_Simproc.eval_ground 5)\<close>

simproc_setup eval_coprime ("coprime a b") =
  \<open>K (Eval_Simproc.eval_ground 3)\<close>

simproc_setup eval_totient ("totient n") =
  \<open>K (Eval_Simproc.eval_ground 5)\<close>

simproc_setup eval_multiplicity ("multiplicity p n") =
  \<open>K (Eval_Simproc.eval_ground 5)\<close>

simproc_setup eval_prime_factorization ("prime_factorization n") =
  \<open>K (Eval_Simproc.eval_ground 10)\<close>

simproc_setup eval_squarefree ("squarefree n") =
  \<open>K (Eval_Simproc.eval_ground 3)\<close>

simproc_setup eval_residue_primroot ("residue_primroot n a") =
  \<open>K (Eval_Simproc.eval_ground 5)\<close>

simproc_setup eval_catalan ("catalan n") =
  \<open>K (Eval_Simproc.eval_ground 3)\<close>

simproc_setup eval_bernoulli ("bernoulli n") =
  \<open>K (Eval_Simproc.eval_ground 5)\<close>

simproc_setup eval_Bell ("Bell n") =
  \<open>K (Eval_Simproc.eval_ground 3)\<close>

simproc_setup eval_Stirling ("Stirling n k") =
  \<open>K (Eval_Simproc.eval_ground 3)\<close>

simproc_setup eval_sum ("sum f S") =
  \<open>K (Eval_Simproc.eval_ground 10)\<close>

simproc_setup eval_prod ("prod f S") =
  \<open>K (Eval_Simproc.eval_ground 10)\<close>

simproc_setup eval_fib ("fib n") =
  \<open>K (Eval_Simproc.eval_ground 3)\<close>

simproc_setup eval_fact ("fact n") =
  \<open>K (Eval_Simproc.eval_ground 3)\<close>

simproc_setup eval_choose ("n choose k") =
  \<open>K (Eval_Simproc.eval_ground 3)\<close>

simproc_setup eval_gcd ("gcd a b") =
  \<open>K (Eval_Simproc.eval_ground 3)\<close>

simproc_setup eval_lcm ("lcm a b") =
  \<open>K (Eval_Simproc.eval_ground 3)\<close>

simproc_setup eval_primes_upto ("primes_upto n") =
  \<open>K (Eval_Simproc.eval_ground 5)\<close>

simproc_setup eval_prime ("prime n") =
  \<open>K (Eval_Simproc.eval_ground 3)\<close>

simproc_setup eval_prime_factors ("prime_factors x") =
  \<open>K (Eval_Simproc.eval_ground 10)\<close>

\<comment> \<open>Make HOL-Analysis det executable via Gauss-Jordan on IArrays\<close>
code_datatype set List.coset \<comment> \<open>restore coset as code constructor (undoes Gauss_Jordan/Code_Set.thy)\<close>
code_datatype vec_lambda
lemma vec_nth_vec_lambda_code [code]: "vec_nth (vec_lambda f) i = f i" by simp

simproc_setup eval_det ("det m") =
  \<open>K (Eval_Simproc.eval_ground 10)\<close>

\<comment> \<open>Pre-compile ground evaluation functions to speed up Code_Evaluation\<close>
code_reflect Eval_Reflect
  datatypes multiset = mset
  functions
    "fib" "catalan" "Bell" "Stirling"
    "Binomial.binomial"
    "totient" "primes_upto"
    "gcd :: _ \<Rightarrow> _ \<Rightarrow> _" "lcm :: _ \<Rightarrow> _ \<Rightarrow> _"
    "prime :: _ \<Rightarrow> bool" "coprime :: _ \<Rightarrow> _ \<Rightarrow> bool"
    "squarefree :: _ \<Rightarrow> bool"
    "multiplicity :: _ \<Rightarrow> _ \<Rightarrow> _"

declare Primes.prime_nat_numeral_eq[simp del]

ML_file \<open>ring_field_algebra.ML\<close>
ML_file \<open>sturm_simproc.ML\<close>

simproc_setup ring_field_eq ("(x::'a::comm_ring_1) = y") =
  \<open>K Ring_Field_Algebra.ring_field_simproc\<close>

simproc_setup sturm_forall (\<open>\<forall>x::real. P x\<close>) =
  \<open>K Sturm_Simproc.sturm_simproc\<close>

simproc_setup sturm_card (\<open>card {x::real. P x} = n\<close>) =
  \<open>K Sturm_Simproc.sturm_simproc\<close>

setup \<open>
  map_theory_simpset (fn ctxt =>
    let val ctxt = ctxt addSolver
          (Raw_Simplifier.mk_solver "algebra" Ring_Field_Algebra.algebra_solver)
    in Simplifier.addloop (ctxt, ("field", Ring_Field_Algebra.field_looper)) end)
\<close>

setup \<open>fn thy =>
  let
    val ctxt = Proof_Context.init_global thy
    fun read_pat s =
      let val t = Proof_Context.read_term_pattern ctxt s
          val ctxt' = Proof_Context.augment t ctxt
          val [t'] = Variable.export_terms ctxt' ctxt [t]
      in t' end
    fun mk_eval seconds name pat =
      {name = name, pattern = read_pat pat,
       proc = Eval_Simproc.eval_ground seconds,
       scope = Pre_Simproc.Everywhere} : Pre_Simproc.entry
    val entries = [
      mk_eval  5 "eval_ord" "ord m n",
      mk_eval  5 "eval_cong" "[a = b] (mod c)",
      mk_eval  3 "eval_coprime" "coprime a b",
      mk_eval  5 "eval_totient" "totient n",
      mk_eval  5 "eval_multiplicity" "multiplicity p n",
      mk_eval 10 "eval_prime_factorization" "prime_factorization n",
      mk_eval  3 "eval_squarefree" "squarefree n",
      mk_eval  5 "eval_residue_primroot" "residue_primroot n a",
      mk_eval  3 "eval_catalan" "catalan n",
      mk_eval  5 "eval_bernoulli" "bernoulli n",
      mk_eval  3 "eval_Bell" "Bell n",
      mk_eval  3 "eval_Stirling" "Stirling n k",
      mk_eval 10 "eval_sum" "sum f S",
      mk_eval 10 "eval_prod" "prod f S",
      mk_eval  3 "eval_fib" "fib n",
      mk_eval  3 "eval_fact" "fact n",
      mk_eval  3 "eval_choose" "n choose k",
      mk_eval  3 "eval_gcd" "gcd a b",
      mk_eval  3 "eval_lcm" "lcm a b",
      mk_eval  5 "eval_primes_upto" "primes_upto n",
      mk_eval  3 "eval_prime" "prime n",
      mk_eval 10 "eval_prime_factors" "prime_factors x",
      mk_eval 10 "eval_det" "det m",
      {name = "sqrt_prime_rat",
       pattern = read_pat "sqrt (numeral n) \<in> \<rat>",
       proc = Sqrt_Prime_Rat.simproc,
       scope = Pre_Simproc.Everywhere},
      {name = "ring_field_eq",
       pattern = read_pat "(x::'a::comm_ring_1) = y",
       proc = Ring_Field_Algebra.ring_field_simproc,
       scope = Pre_Simproc.Concl_Only},
      {name = "sturm_forall",
       pattern = read_pat "\<forall>x::real. P x",
       proc = Sturm_Simproc.sturm_simproc,
       scope = Pre_Simproc.Concl_Only},
      {name = "sturm_card",
       pattern = read_pat "card {x::real. P x} = n",
       proc = Sturm_Simproc.sturm_simproc,
       scope = Pre_Simproc.Concl_Only}
    ]
  in Context.theory_map (fold Pre_Simproc.register entries) thy end
\<close>

(*
ML ‹
val ctxt = @{context};
val thy = Proof_Context.theory_of ctxt;
val {const_space, constants, ...} = Consts.dest (Sign.consts_of thy);
val out = TextIO.openOut "/tmp/open_constants.tsv";
val _ = List.app (fn (long_name, _) =>
  let
    val short = Name_Space.extern ctxt const_space long_name
  in
    if not (String.isSubstring "." short) then
      TextIO.output (out, short ^ "\t" ^ long_name ^ "\n")
    else ()
  end) constants;
val _ = TextIO.closeOut out
›
*)

\<comment> \<open>Environment fingerprint dumps (const/type short-name resolution + concrete
  syntax) live in \<^file>\<open>env_dump.ML\<close>; load \<^file>\<open>Env_Dump.thy\<close> in this session to
  emit the MathBench_Prover reference, then run
  \<^verbatim>\<open>python tools/check_putnam_divergence.py\<close> to compare against every
  PutnamBench import combination. The two ML blocks below are the original
  ad-hoc diagnostics, superseded by that tooling and kept commented for
  reference.\<close>

(*
ML ‹
val ctxt = @{context};
val thy = Proof_Context.theory_of ctxt;
val {const_space, constants, ...} = Consts.dest (Sign.consts_of thy);

(* Enumerate ALL constants accessible by a given base name.
   Iteratively intern the base name, record the first match, hide it
   from base-name access (fully=false), and repeat until intern
   returns a hidden ("??."-prefixed) result. *)
fun all_accessible space base =
  let val result = Name_Space.intern space base
  in
    if Long_Name.is_hidden result then []
    else result :: all_accessible (Name_Space.hide false result space) base
  end;

(* Collect all base names that have >1 constant *)
val by_base = fold (fn (long_name, _) =>
    Symtab.map_default (Long_Name.base_name long_name, []) (cons long_name)
  ) constants Symtab.empty;

(* For each such base name, find which constants are actually accessible
   (not hidden by hide_const). Report only genuine conflicts (>1 accessible). *)
val conflicts = Symtab.dest by_base
  |> map_filter (fn (base, _) =>
    let val accessible = all_accessible const_space base
    in if length accessible > 1 then SOME (base, accessible) else NONE end)
  |> sort (string_ord o apply2 fst);

val out = TextIO.openOut "/tmp/conflicting_exposed_constants.tsv";
val _ = List.app (fn (base, accessible) =>
  let val current = Name_Space.intern const_space base
  in List.app (fn long_name =>
    let val mark = if long_name = current then "*" else ""
    in TextIO.output (out, base ^ "\t" ^ long_name ^ "\t" ^ mark ^ "\n") end
  ) accessible end
) conflicts;
val _ = TextIO.closeOut out;

val _ = writeln (string_of_int (length conflicts) ^ " conflicting base names, " ^
  string_of_int (List.foldl (fn ((_, acc), n) => n + length acc) 0 conflicts) ^
  " exposed constants total")
›


ML \<open>
val syn = Proof_Context.syntax_of @{context};
val buf = Unsynchronized.ref ([] : string list);
val old_writeln = ! Private_Output.writeln_fn;
val _ = Private_Output.writeln_fn := (fn ss => buf := implode ss :: ! buf);
val result = Exn.capture Syntax.print_syntax syn;
val _ = Private_Output.writeln_fn := old_writeln;
val _ = Exn.release result;
val content = String.concatWith "\n" (rev (! buf));
val out = TextIO.openOut "/tmp/mathbench_syntax.txt";
val _ = TextIO.output (out, content);
val _ = TextIO.closeOut out
\<close>
*)

end
