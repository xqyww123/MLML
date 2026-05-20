theory MathBench_Prover
  imports
    (* Tool infrastructure *)
    "HOL-Decision_Procs.Reflective_Field"
    Auto_Sledgehammer.Auto_Sledgehammer
    (* HOL bundles *)
    "HOL-Library.Library"
    "HOL-Combinatorics.Combinatorics"
    (* Basic math *)
    "Weighted_Arithmetic_Geometric_Mean.Weighted_Arithmetic_Geometric_Mean"
    Derangements.Derangements
    "Bell_Numbers_Spivey.Bell_Numbers"
    Card_Number_Partitions.Card_Number_Partitions
    Pell.Pell_Algorithm
    Lucas_Theorem.Lucas_Theorem
    "Budan_Fourier.Budan_Fourier"
    "Lifting_the_Exponent.LTE"
    "Bertrands_Postulate.Bertrand"
    (* Analysis / matrices *)
    "Gauss_Jordan.Determinants_IArrays"
    "Catalan_Numbers.Catalan_Numbers"
    Stirling_Formula.Stirling_Formula
    "Fourier.Fourier"
    (* Complex analysis / number theory *)
    Euler_MacLaurin.Euler_MacLaurin_Landau
    Chebyshev_Polynomials.Chebyshev_Polynomials
    Dirichlet_Series.Dirichlet_Series_Analysis
    Linear_Recurrences.Rational_FPS_Asymptotics
    Gaussian_Integers.Gaussian_Integers_Everything
    (* Last: polynomial-related, so Polynomial.degree wins name resolution *)
    Power_Sum_Polynomials.Power_Sum_Polynomials
begin

no_notation fps_nth (infixl "$" 75)
no_notation BNF_Cardinal_Arithmetic.cprod (infixr "*c" 80)
no_notation BNF_Cardinal_Arithmetic.csum (infixr "+c" 65)
no_notation BNF_Cardinal_Arithmetic.cexp (infixr "^c" 90)
no_notation BNF_Wellorder_Constructions.ordIso2 (infix "=o" 50)
no_notation BNF_Wellorder_Constructions.ordLess2 (infix "<o" 50)
no_notation BNF_Wellorder_Constructions.ordLeq2 (infix "<=o" 50)
no_notation matrix_scalar_mult (infixl "*k" 70)
no_notation vector_scalar_mult (infixl "*s" 70)
no_notation matrix_vector_mult_iarray (infixl "*iv" 70)
no_notation vector_matrix_mult_iarray (infixl "v*i" 70)
no_notation matrix_vector_mult (infixl "*v" 70)
no_notation vector_matrix_mult (infixl "v*" 70)
no_notation word_sless ("'(<s')")
no_notation word_sless ("(_/ <s _)"  [51, 51] 50)
no_notation word_sle ("'(<=s')")
no_notation word_sle ("(_/ <=s _)" [51, 51] 50)
no_notation Set_Algebras.elt_set_times (infixl "*o" 80)
no_notation Set_Algebras.elt_set_plus (infixl "+o" 70)
no_notation Set_Algebras.elt_set_eq (infix "=o" 50)

hide_type (open) Commutative_Ring.pol Commutative_Ring.polex Commutative_Ring.mon
  Reflective_Field.fexpr Reflective_Field.pexpr Reflective_Field.pexpr1 Reflective_Field.pexpr2

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
  Sigma_Algebra.measure MPoly_Type.degree

declare [[smt_oracle, z3_extensions, smt_nat_as_int]]
declare [[auto_sledgehammer_params = "provers = verit z3 e spass vampire zipperposition cvc5, smt_proofs = true"]]

lemma strip_Trueprop_eq: \<open>(Trueprop P \<equiv> Trueprop Q) \<Longrightarrow> P \<equiv> Q\<close>
unfolding atomize_eq
proof rule
  assume A: \<open>Trueprop P \<equiv> Trueprop Q\<close>
     and B: P
  from B[unfolded A]
  show "Q" .
next
  assume A: \<open>Trueprop P \<equiv> Trueprop Q\<close>
     and B: Q
  show "P"
    unfolding A
    using B .
qed

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
 
lemma "sqrt 23 \<notin> \<rat>"
  by simp

declare [[ML_debugger]]
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

simproc_setup ring_field_eq ("(x::'a::comm_ring_1) = y") =
  \<open>K Ring_Field_Algebra.ring_field_simproc\<close>

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
       scope = Pre_Simproc.Concl_Only}
    ]
  in Context.theory_map (fold Pre_Simproc.register entries) thy end
\<close>

lemma "prime_factors (1 + 3 * \<i>\<^sub>\<int>) = {2 + \<i>\<^sub>\<int>, 1 + \<i>\<^sub>\<int>}"
  by auto'

end
