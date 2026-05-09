theory MathBench_Prover
  imports
    "HOL-Analysis.Analysis"
    "HOL-Library.Library"
    "HOL-Library.Code_Target_Numeral"
    "HOL-Computational_Algebra.Computational_Algebra"
    "Lifting_the_Exponent.LTE"
    "Polynomial_Factorization.Prime_Factorization"
    "Catalan_Numbers.Catalan_Numbers"
    "Bernoulli.Bernoulli"
    "Bell_Numbers_Spivey.Bell_Numbers"
    "Gauss_Jordan.Determinants_IArrays"
    (*"HOL-Algebra.Algebra"*)
    (*Minilang_Agent.Minilang_Agent*)
    Auto_Sledgehammer.Auto_Sledgehammer
begin

declare [[smt_oracle, z3_extensions, smt_nat_as_int]]
declare [[auto_sledgehammer_params = "provers = verit z3 e spass vampire zipperposition cvc5, smt_proofs = true"]]

lemma strip_Trueprop_eq: ‹(Trueprop P ≡ Trueprop Q) ⟹ P ≡ Q›
unfolding atomize_eq
proof rule
  assume A: ‹Trueprop P ≡ Trueprop Q›
     and B: P
  from B[unfolded A]
  show "Q" .
next
  assume A: ‹Trueprop P ≡ Trueprop Q›
     and B: Q
  show "P"
    unfolding A
    using B .
qed

theorem sqrt_prime_irrational:
  fixes p :: int
  assumes x: "prime p"
  shows "sqrt p ∉ ℚ"
proof
  from ‹prime p› have p: "p > 1"
    using prime_gt_1_int by blast
  assume "sqrt p ∈ ℚ"
  then obtain m n :: nat
    where n: "n ≠ 0"
      and sqrt_rat: "¦sqrt p¦ = m / n"
      and "coprime m n" by (rule Rats_abs_nat_div_natE)
  have eq: "m² = p * n²"
  proof -
    from n and sqrt_rat have "m = ¦sqrt p¦ * n" by simp
    then have "m² = (sqrt p)² * n²" by (simp add: power_mult_distrib)
    also have "(sqrt p)² = p"
      by (simp add: assms prime_ge_0_int)
    also have "… * n² = p * n²" by simp
    finally show ?thesis by linarith
  qed
  have "p dvd m ∧ p dvd n"
  proof
    from eq have "p dvd m²" ..
    with ‹prime p› show "p dvd m"
      by (simp add: prime_dvd_power_int_iff)
    then obtain k where "m = p * k" ..
    with eq have "p * n² = p² * k²"
      by (simp add: power_mult_distrib)
    with p have "n² = p * k²" by (simp add: power2_eq_square)
    then have "p dvd n²" ..
    with ‹prime p› show "p dvd n"
      by (metis coprime_dvd_mult_left_iff int_ops(7) power2_eq_square prime_imp_coprime)
  qed
  then have "p dvd gcd m n"
    using ‹coprime m n› coprime_common_divisor coprime_int_iff by blast
  with ‹coprime m n› have "p = 1"
    using p by force
  with p show False by simp
qed

lemma multiplicity_code [code]:
  "multiplicity p x =
     (if p = 0 ∨ is_unit p ∨ x = 0 then 0
      else if p dvd x then 1 + multiplicity p (x div p) else 0)"
proof (cases "p = 0 ∨ is_unit p ∨ x = 0")
  case True
  then show ?thesis by (auto simp: multiplicity_unit_left)
next
  case False
  then have h: "p ≠ 0" "¬ is_unit p" "x ≠ 0" by auto
  show ?thesis
  proof (cases "p dvd x")
    case False
    with h show ?thesis by (simp add: not_dvd_imp_multiplicity_0)
  next
    case True
    with h have eq: "p * (x div p) = x" by simp
    with h have "x div p ≠ 0" by auto
    with h have "multiplicity p (p * (x div p)) = Suc (multiplicity p (x div p))"
      by (intro multiplicity_times_same)
    with eq True h show ?thesis by simp
  qed
qed

simproc_setup sqrt_prime_rat (‹sqrt (numeral n) ∈ ℚ›) =
  ‹K (fn ctxt => fn ct =>
    let
      val ((_ $ (_ $ (_ $ bits))) $ _) = Thm.term_of ct
    in
      @{lemma ‹prime (numeral n :: int) ⟹ (sqrt (numeral n :: real) ∈ ℚ) = False› for n
           by (metis sqrt_prime_irrational[of "numeral n"] of_int_eq_numeral_iff)}
      |> Thm.instantiate' [] [SOME (Thm.cterm_of ctxt bits)]
      |> (fn thm => thm RS @{thm eq_reflection})
      |> SOME
    end
    handle Match => NONE | THM _ => NONE)›
 
lemma "sqrt 23 ∉ ℚ"
  by simp

declare [[ML_debugger]]
ML_file ‹eval_simproc.ML›

simproc_setup eval_ord ("ord m n") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_cong ("[a = b] (mod c)") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_coprime ("coprime a b") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_totient ("totient n") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_multiplicity ("multiplicity p n") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_prime_factorization ("prime_factorization n") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_squarefree ("squarefree n") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_residue_primroot ("residue_primroot n a") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_catalan ("catalan n") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_bernoulli ("bernoulli n") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_Bell ("Bell n") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_Stirling ("Stirling n k") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_sum ("sum f S") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_prod ("prod f S") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_fib ("fib n") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_fact ("fact n") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_choose ("n choose k") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_gcd ("gcd a b") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_lcm ("lcm a b") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_primes_upto ("primes_upto n") =
  ‹K Eval_Simproc.eval_ground›

simproc_setup eval_prime ("prime n") =
  ‹K Eval_Simproc.eval_ground›

― ‹Make HOL-Analysis det executable via Gauss-Jordan on IArrays›
code_datatype set List.coset ― ‹restore coset as code constructor (undoes Gauss_Jordan/Code_Set.thy)›
code_datatype vec_lambda
lemma vec_nth_vec_lambda_code [code]: "vec_nth (vec_lambda f) i = f i" by simp

simproc_setup eval_det ("det m") =
  ‹K Eval_Simproc.eval_ground›

declare Primes.prime_nat_numeral_eq[simp del]

(*
(*test*)
lemma ‹poly [:1, -3, 2::int:] 5 = 36› by simp
lemma ‹degree [:1, -3, 2::int:] = 2› by simp
lemma ‹card {2, 3, 5, 7::nat} = 4› by simp
lemma ‹(∑i<5. i) = (10::nat)› by simp
lemma ‹(∏i=1..4. i) = (24::nat)› by simp
lemma ‹fib 10 = (55::nat)› by simp
lemma ‹fact 5 = (120::nat)› by simp
lemma ‹(10::nat) choose 3 = 120› by simp
lemma ‹gcd (12::nat) 8 = 4› by simp
lemma ‹lcm (12::nat) 8 = 24› by simp
lemma ‹⌊3.7::real⌋ = 3› by simp
lemma ‹⌈3.2::real⌉ = 4› by simp

lemma ‹squarefree (30::nat)›
  by simp

lemma ‹¬ squarefree (12::nat)›
  by  simp
*)

end
