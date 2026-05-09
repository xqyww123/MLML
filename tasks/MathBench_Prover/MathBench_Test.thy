theory MathBench_Test
  imports
    (*"HOL-Algebra.Algebra"*)
    (*Minilang_Agent.Minilang_Agent*)
    HOL.Power
begin

no_notation BNF_Cardinal_Arithmetic.cprod (infixr "*c" 80)
no_notation BNF_Cardinal_Arithmetic.csum (infixr "+c" 65)
no_notation BNF_Cardinal_Arithmetic.cexp (infixr "^c" 90)
no_notation BNF_Wellorder_Constructions.ordIso2 (infix "=o" 50)
no_notation BNF_Wellorder_Constructions.ordLess2 (infix "=o" 50)
no_notation BNF_Wellorder_Constructions.ordLeq2 (infix "<=o" 50)

print_syntax

lemma \<open>multiplicity (int x) (int y) = multiplicity x y\<close>
  unfolding multiplicity_def
  apply (auto simp: )
  oops

hide_type (open) Commutative_Ring.pol Commutative_Ring.polex Commutative_Ring.mon
  Reflective_Field.fexpr Reflective_Field.pexpr Reflective_Field.pexpr1 Reflective_Field.pexpr2

hide_const (open)
  \<comment> \<open>Commutative_Ring datatypes\<close>
  Commutative_Ring.Pc Commutative_Ring.Pinj Commutative_Ring.PX
  Commutative_Ring.Var Commutative_Ring.Const Commutative_Ring.Add
  Commutative_Ring.Sub Commutative_Ring.Mul Commutative_Ring.Pow Commutative_Ring.Neg
  Commutative_Ring.Mc Commutative_Ring.Minj Commutative_Ring.MX
  \<comment> \<open>Commutative_Ring top-level functions\<close>
  Commutative_Ring.mkPinj Commutative_Ring.mkPX
  Commutative_Ring.add Commutative_Ring.mul Commutative_Ring.neg
  Commutative_Ring.sub Commutative_Ring.sqr Commutative_Ring.pow Commutative_Ring.norm
  Commutative_Ring.mkMinj Commutative_Ring.Minj_pred
  Commutative_Ring.mkMX Commutative_Ring.cfactor Commutative_Ring.mfactor
  Commutative_Ring.mon_of_pol Commutative_Ring.mk_monpol_list
  Commutative_Ring.ponesubst Commutative_Ring.pnsubst1 Commutative_Ring.pnsubst
  Commutative_Ring.psubstl1 Commutative_Ring.psubstl Commutative_Ring.pnsubstl
  \<comment> \<open>Reflective_Field datatypes\<close>
  Reflective_Field.FCnst Reflective_Field.FVar Reflective_Field.FAdd
  Reflective_Field.FSub Reflective_Field.FMul Reflective_Field.FNeg
  Reflective_Field.FDiv Reflective_Field.FPow
  Reflective_Field.PExpr1 Reflective_Field.PExpr2
  Reflective_Field.PCnst Reflective_Field.PVar Reflective_Field.PAdd
  Reflective_Field.PSub Reflective_Field.PNeg
  Reflective_Field.PMul Reflective_Field.PPow
  \<comment> \<open>Reflective_Field top-level functions\<close>
  Reflective_Field.npepow Reflective_Field.npemul Reflective_Field.npeadd
  Reflective_Field.npesub Reflective_Field.npeneg
  Reflective_Field.isin Reflective_Field.split_aux Reflective_Field.fnorm

ML_file \<open>ring_field_algebra.ML\<close>

simproc_setup ring_field_eq ("(x::'a::comm_ring_1) = y") =
  \<open>K Ring_Field_Algebra.ring_field_simproc\<close>

setup \<open>
  map_theory_simpset (fn ctxt =>
    let val ctxt = ctxt addSolver
          (Raw_Simplifier.mk_solver "algebra" Ring_Field_Algebra.algebra_solver)
    in Simplifier.addloop (ctxt, ("field", Ring_Field_Algebra.field_looper)) end)
\<close>

(* === Unit tests === *)

ML \<open>
val ctxt = @{context}
fun assert msg b = if b then () else error ("FAIL: " ^ msg)
fun ok msg = writeln (msg ^ " [OK]")

(* ===== 1. Guards: is_ring_expr ===== *)

val _ = assert "ring: Free" (Ring_Field_Algebra.is_ring_expr @{term "x::int"})
val _ = assert "ring: plus" (Ring_Field_Algebra.is_ring_expr @{term "(x::int) + y"})
val _ = assert "ring: times" (Ring_Field_Algebra.is_ring_expr @{term "(x::int) * y"})
val _ = assert "ring: minus" (Ring_Field_Algebra.is_ring_expr @{term "(x::int) - y"})
val _ = assert "ring: uminus" (Ring_Field_Algebra.is_ring_expr @{term "-(x::int)"})
val _ = assert "ring: power" (Ring_Field_Algebra.is_ring_expr @{term "(x::int) ^ 3"})
val _ = assert "ring: zero" (Ring_Field_Algebra.is_ring_expr @{term "0::int"})
val _ = assert "ring: one" (Ring_Field_Algebra.is_ring_expr @{term "1::int"})
val _ = assert "ring: numeral" (Ring_Field_Algebra.is_ring_expr @{term "42::int"})
val _ = assert "ring: nested" (Ring_Field_Algebra.is_ring_expr @{term "((x::int) + y)\<^sup>2 - x*y"})
val _ = assert "ring: reject sin" (not (Ring_Field_Algebra.is_ring_expr @{term "sin (x::real)"}))
val _ = assert "ring: reject divide" (not (Ring_Field_Algebra.is_ring_expr @{term "1/(x::real)"}))
val _ = assert "ring: reject abs" (not (Ring_Field_Algebra.is_ring_expr @{term "\<bar>x::int\<bar>"}))
val _ = assert "ring: reject app" (not (Ring_Field_Algebra.is_ring_expr @{term "f (x::int)"}))
val _ = ok "is_ring_expr"

(* ===== 2. Guards: is_field_expr ===== *)

val _ = assert "field: ring subset" (Ring_Field_Algebra.is_field_expr @{term "(x::real) + y"})
val _ = assert "field: divide" (Ring_Field_Algebra.is_field_expr @{term "1/(x::real)"})
val _ = assert "field: inverse" (Ring_Field_Algebra.is_field_expr @{term "inverse (x::real)"})
val _ = assert "field: nested div in ring" (Ring_Field_Algebra.is_field_expr @{term "(x::real) + 1/y"})
val _ = assert "field: div of div" (Ring_Field_Algebra.is_field_expr @{term "(1/(x::real)) / y"})
val _ = assert "field: complex" (Ring_Field_Algebra.is_field_expr @{term "(1 - 1/(x::real)) * x"})
val _ = assert "field: reject sin" (not (Ring_Field_Algebra.is_field_expr @{term "sin (x::real)"}))
val _ = assert "field: reject exp" (not (Ring_Field_Algebra.is_field_expr @{term "exp (x::real)"}))
val _ = assert "field: reject sqrt" (not (Ring_Field_Algebra.is_field_expr @{term "sqrt (x::real)"}))
val _ = ok "is_field_expr"

(* ===== 3. Guards: has_division ===== *)

val _ = assert "div: present" (Ring_Field_Algebra.has_division @{term "1/(x::real) + y"})
val _ = assert "div: inverse" (Ring_Field_Algebra.has_division @{term "inverse (x::real)"})
val _ = assert "div: deep" (Ring_Field_Algebra.has_division @{term "(a::real) + b * (1/c)"})
val _ = assert "div: absent" (not (Ring_Field_Algebra.has_division @{term "(x::real) + y*z"}))
val _ = ok "has_division"

(* ===== 4. merge_one_conv ===== *)

local
  fun check msg ct expected_rhs_prems =
    let
      val eq = Ring_Field_Algebra.merge_one_conv ctxt ct
      val rhs = Thm.term_of (Thm.rhs_of eq)
      val n = length (Logic.strip_imp_prems rhs)
    in assert (msg ^ ": prem count") (n = expected_rhs_prems);
       ok msg
    end
in
  val _ = check "merge_one: 2 prems"
    @{cprop "x \<noteq> (0::real) \<Longrightarrow> y \<noteq> (0::real) \<Longrightarrow> True"} 1
  val _ = check "merge_one: 2+1 prems (merges first two only)"
    @{cprop "x \<noteq> (0::real) \<Longrightarrow> y \<noteq> (0::real) \<Longrightarrow> z \<noteq> (0::real) \<Longrightarrow> True"} 2
end

(* ===== 5. merge_prems_conv (all prems) ===== *)

local
  fun check msg ct expected_rhs_prems =
    let
      val eq = Ring_Field_Algebra.merge_prems_conv ctxt ct
      val rhs = Thm.term_of (Thm.rhs_of eq)
      val n = length (Logic.strip_imp_prems rhs)
    in assert (msg ^ ": prem count") (n = expected_rhs_prems);
       writeln (msg ^ " [OK]: " ^ Syntax.string_of_term ctxt rhs)
    end
in
  val _ = check "merge_all: 1 prem (identity)"
    @{cprop "x \<noteq> (0::real) \<Longrightarrow> True"} 1
  val _ = check "merge_all: 2 prems -> 1 conj"
    @{cprop "x \<noteq> (0::real) \<Longrightarrow> y \<noteq> (0::real) \<Longrightarrow> True"} 1
  val _ = check "merge_all: 3 prems -> 1 conj (right-assoc)"
    @{cprop "x \<noteq> (0::real) \<Longrightarrow> y \<noteq> (0::real) \<Longrightarrow> z \<noteq> (0::real) \<Longrightarrow> True"} 1
  val _ = check "merge_all: 4 prems -> 1 conj"
    @{cprop "a \<noteq> (0::real) \<Longrightarrow> b \<noteq> (0::real) \<Longrightarrow> c \<noteq> (0::real) \<Longrightarrow> d \<noteq> (0::real) \<Longrightarrow> True"} 1
end

(* ===== 6. merge_n_prems_conv (partial merge) ===== *)

local
  fun check msg ct n expected_rhs_prems =
    let
      val eq = Ring_Field_Algebra.merge_n_prems_conv ctxt n ct
      val rhs = Thm.term_of (Thm.rhs_of eq)
      val actual = length (Logic.strip_imp_prems rhs)
    in assert (msg ^ ": prem count") (actual = expected_rhs_prems);
       writeln (msg ^ " [OK]: " ^ Syntax.string_of_term ctxt rhs)
    end
in
  val _ = check "merge_n: 1 of 3 (identity)"
    @{cprop "x \<noteq> (0::real) \<Longrightarrow> y \<noteq> (0::real) \<Longrightarrow> z \<noteq> (0::real) \<Longrightarrow> True"} 1 3
  val _ = check "merge_n: 2 of 3 (merge first 2, keep last)"
    @{cprop "x \<noteq> (0::real) \<Longrightarrow> y \<noteq> (0::real) \<Longrightarrow> z \<noteq> (0::real) \<Longrightarrow> True"} 2 2
  val _ = check "merge_n: 3 of 3 (merge all)"
    @{cprop "x \<noteq> (0::real) \<Longrightarrow> y \<noteq> (0::real) \<Longrightarrow> z \<noteq> (0::real) \<Longrightarrow> True"} 3 1
  val _ = check "merge_n: 2 of 4"
    @{cprop "a \<noteq> (0::real) \<Longrightarrow> b \<noteq> (0::real) \<Longrightarrow> c \<noteq> (0::real) \<Longrightarrow> d \<noteq> (0::real) \<Longrightarrow> True"} 2 3
  val _ = check "merge_n: 3 of 4"
    @{cprop "a \<noteq> (0::real) \<Longrightarrow> b \<noteq> (0::real) \<Longrightarrow> c \<noteq> (0::real) \<Longrightarrow> d \<noteq> (0::real) \<Longrightarrow> True"} 3 2
end

(* ===== 7. merge_prems (on theorems) ===== *)

local
  fun check msg th expected_prems =
    let
      val merged = Ring_Field_Algebra.merge_prems ctxt th
      val n = Thm.nprems_of merged
    in assert (msg ^ ": prem count") (n = expected_prems);
       writeln (msg ^ " [OK]: " ^ Thm.string_of_thm ctxt merged)
    end
  fun mk_th props concl =
    fold_rev (fn p => fn th => Thm.implies_intr (Thm.cterm_of ctxt p) th)
      props (Thm.assume (Thm.cterm_of ctxt concl))
in
  val _ = check "merge_thm: 0 prems" @{thm TrueI} 0
  val _ = check "merge_thm: 1 prem"
    (mk_th [@{prop "x \<noteq> (0::real)"}] @{prop "True"}) 1
  val _ = check "merge_thm: 2 prems -> 1"
    (mk_th [@{prop "x \<noteq> (0::real)"}, @{prop "y \<noteq> (0::real)"}] @{prop "True"}) 1
  val _ = check "merge_thm: 3 prems -> 1"
    (mk_th [@{prop "x \<noteq> (0::real)"}, @{prop "y \<noteq> (0::real)"}, @{prop "z \<noteq> (0::real)"}]
           @{prop "True"}) 1
end

(* ===== 8. try_ring ===== *)

local
  fun check_some msg ct = assert msg (is_some (Ring_Field_Algebra.try_ring ctxt ct))
  fun check_none msg ct = assert msg (is_none (Ring_Field_Algebra.try_ring ctxt ct))
in
  val _ = check_some "try_ring: binomial" @{cterm "((x::int) + y)\<^sup>2 = x\<^sup>2 + 2*x*y + y\<^sup>2"}
  val _ = check_some "try_ring: diff squares" @{cterm "((a::int) + b) * (a - b) = a\<^sup>2 - b\<^sup>2"}
  val _ = check_some "try_ring: zero" @{cterm "(x::int) - x = 0"}
  val _ = check_none "try_ring: non-identity" @{cterm "(x::int) = y"}
  val _ = check_none "try_ring: has division" @{cterm "1/(x::real) = 1/x"}
  val _ = ok "try_ring"
end

(* ===== 9. try_field ===== *)

local
  fun check msg ct expected_prems =
    case Ring_Field_Algebra.try_field ctxt ct of
      SOME th =>
        (assert (msg ^ ": expected SOME") (expected_prems >= 0);
         assert (msg ^ ": prem count") (Thm.nprems_of th = expected_prems);
         writeln (msg ^ " [OK, " ^ string_of_int (Thm.nprems_of th) ^ " prem]: "
                  ^ Thm.string_of_thm ctxt th))
    | NONE =>
        (assert (msg ^ ": expected NONE") (expected_prems < 0);
         ok msg)
in
  val _ = check "try_field: 1/x+1/x" @{cterm "1/(x::real) + 1/x = 2/x"} 1
  val _ = check "try_field: 1/x+1/y" @{cterm "1/(x::real) + 1/y = (x + y)/(x*y)"} 1
  val _ = check "try_field: 1/x+1/y+1/z"
    @{cterm "1/(x::real) + 1/y + 1/z = (y*z + x*z + x*y)/(x*y*z)"} 1
  val _ = check "try_field: no field (int)" @{cterm "1/(x::int) = 1/x"} ~1
end

(* ===== 10. ring_field_simproc (integration) ===== *)

local
  fun check msg ct expected_prems =
    case Ring_Field_Algebra.ring_field_simproc ctxt ct of
      SOME th =>
        (assert (msg ^ ": expected SOME") (expected_prems >= 0);
         assert (msg ^ ": prem count") (Thm.nprems_of th = expected_prems);
         ok msg)
    | NONE =>
        (assert (msg ^ ": expected NONE") (expected_prems < 0);
         ok msg)
in
  val _ = check "simproc: ring" @{cterm "((x::int) + y)\<^sup>2 = x\<^sup>2 + 2*x*y + y\<^sup>2"} 0
  val _ = check "simproc: field 1 cond" @{cterm "1/(x::real) + 1/x = 2/x"} 1
  val _ = check "simproc: field 2 conds merged" @{cterm "1/(x::real) + 1/y = (x + y)/(x*y)"} 1
  val _ = check "simproc: guard reject (sin)" @{cterm "sin (x::real) = sin x"} ~1
  val _ = check "simproc: guard reject (sqrt)" @{cterm "sqrt (x::real) = sqrt x"} ~1
  val _ = check "simproc: no field sort (int div)" @{cterm "(x::int) + x div y = x + x div y"} ~1
end
\<close>

(* === Ring simproc: unconditional polynomial identities === *)

lemma "((x::int) + y)\<^sup>2 = x\<^sup>2 + 2*x*y + y\<^sup>2"
  by simp

lemma "((a::int) + b) * (a - b) = a\<^sup>2 - b\<^sup>2"
  by simp

lemma "((x::real) + y)\<^sup>2 = x\<^sup>2 + 2*x*y + y\<^sup>2"
  by simp

(* === Field simproc: conditional rewrite with non-zero conditions === *)

lemma "(x::real) \<noteq> 0 \<Longrightarrow> (1 - 1/x) * x - x + 1 = 0"
  by simp

(* === Field looper === *)

lemma "(x::real) \<noteq> 0 \<Longrightarrow> 1/x + 1/x = 2/x"
  by simp

(* === Algebra solver: uses hypotheses === *)

lemma "x + y = (0::int) \<Longrightarrow> x * y = 0 \<Longrightarrow> x\<^sup>2 = 0"
  by simp

(* === Ring: higher degree === *)

lemma "((x::int) + 1) ^ 4 = x ^ 4 + 4*x ^ 3 + 6*x\<^sup>2 + 4*x + 1"
  by simp

lemma "(a::int) ^ 3 + b ^ 3 = (a + b) * (a\<^sup>2 - a*b + b\<^sup>2)"
  by simp

(* === Field: multiple non-zero conditions (tests merge_prems) === *)

lemma "(x::real) \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> 1/(x*y) = 1/x * (1/y)"
  by simp

lemma "(x::real) \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> 1/x - 1/y = (y - x)/(x*y)"
  by simp

(* === Field: nested division === *)

lemma "(x::real) \<noteq> 0 \<Longrightarrow> (x + 1/x)\<^sup>2 = x\<^sup>2 + 2 + 1/x ^ 2"
  by simp

(* === Field: partial fractions === *)

lemma "(x::real) \<noteq> 0 \<Longrightarrow> x - 1 \<noteq> 0 \<Longrightarrow> 1/(x*(x - 1)) = 1/(x - 1) - 1/x"
  by simp

(* === Field over complex === *)

lemma "(z::complex) \<noteq> 0 \<Longrightarrow> (z - 1/z) * (z + 1/z) = z\<^sup>2 - 1/z ^ 2"
  by simp

(* === Algebra: identity from hypothesis === *)

lemma "(x::int) ^ 2 - 1 = 0 \<Longrightarrow> (x + 1) * (x - 1) = 0"
  by simp

(* === Algebra: Newton's identity (3 variables, Groebner) === *)

lemma "x + y + z = (0::int) \<Longrightarrow> x ^ 3 + y ^ 3 + z ^ 3 = 3*x*y*z"
  by simp

(* === Guard rejection: non-polynomial terms === *)

lemma "sin (x::real) + sin x = 2 * sin x"
  by simp

(* ================================================================ *)
(* Stress tests: verify no capability loss vs standalone tactics    *)
(* ================================================================ *)

(* --- poly_eq_simproc coexistence: it partially normalizes first --- *)

lemma "(x::real) \<noteq> 0 \<Longrightarrow> (1/x + 1) * x = x + 1"
  by simp

lemma "(x::real) \<noteq> 0 \<Longrightarrow> (x - 1/x) * x = x\<^sup>2 - 1"
  by simp

(* --- Numeral coefficients (field_combine_numerals active) --- *)

lemma "(x::real) \<noteq> 0 \<Longrightarrow> 3/x + 5/x = 8/x"
  by simp

lemma "(x::real) \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> 2/x - 3/y = (2*y - 3*x)/(x*y)"
  by simp

(* --- left_inverse/right_inverse [simp] coexistence --- *)

lemma "(x::real) \<noteq> 0 \<Longrightarrow> x * inverse x = 1"
  by simp

lemma "(x::real) \<noteq> 0 \<Longrightarrow> inverse x * x + 1 = 2"
  by simp

(* --- Condition discharge: x*y \<noteq> 0 from x \<noteq> 0 and y \<noteq> 0 --- *)

lemma "(x::real) \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x/y + y/x = (x\<^sup>2 + y\<^sup>2)/(x*y)"
  by simp

lemma "(x::real) \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow>
       x/(y*z) + y/(x*z) + z/(x*y) = (x\<^sup>2 + y\<^sup>2 + z\<^sup>2)/(x*y*z)"
  by simp

(* --- Algebra: various hypothesis patterns --- *)

lemma "x\<^sup>2 + y\<^sup>2 = (1::int) \<Longrightarrow> (x + y)\<^sup>2 + (x - y)\<^sup>2 = 2"
  by simp

lemma "a * b = (1::int) \<Longrightarrow> a\<^sup>2 * b\<^sup>2 = 1"
  by simp

lemma "x * y = (0::int) \<Longrightarrow> x ^ 3 * y ^ 3 = 0"
  by simp

(* --- Ring: higher complexity --- *)

lemma "((x::real) + y)\<^sup>2 - (x - y)\<^sup>2 = 4*x*y"
  by simp

lemma "((x::int) + y + z)\<^sup>2 = x\<^sup>2 + y\<^sup>2 + z\<^sup>2 + 2*x*y + 2*x*z + 2*y*z"
  by simp

(* --- Field: complex expressions --- *)

lemma "(x::real) \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> (x/y - y/x) * x * y = x\<^sup>2 - y\<^sup>2"
  by simp

lemma "(x::real) \<noteq> 0 \<Longrightarrow> (x - 1/x) * (x + 1/x) = x\<^sup>2 - 1/x\<^sup>2"
  by simp

(* --- Mixed: ring identity with field subexpression simplified by left/right_inverse --- *)

lemma "(x::real) \<noteq> 0 \<Longrightarrow> (x + 1/x)\<^sup>2 - (x - 1/x)\<^sup>2 = 4"
  by simp

(* --- Regression: existing simprocs still work --- *)

lemma "sin (x::real) + cos x - sin x = cos x"
  by simp

lemma "\<bar>(x::real)\<bar> * \<bar>x\<bar> = x\<^sup>2"
  by (simp add: )

(* --- Regression: multiplicity + auto must not crash (THM 0 bug) --- *)

lemma multiplicity_int_nat: \<open>multiplicity (int x) (int y) = multiplicity x y\<close>
proof -
  have t1: "int x ^ n dvd int y = (x ^ n dvd y)" for n
    using of_nat_dvd_iff by force
  show ?thesis
    unfolding multiplicity_def
    by (auto simp: t1)
qed


(* ================================================================ *)
(* Experimental: sos as a simplifier solver                         *)
(* ================================================================ *)

section \<open>Sum-of-Squares solver for the simplifier\<close>

text \<open>
  We wrap the sos tactic as a simplifier solver. A solver fires once per
  unsolved subgoal after all rewriting is done — unlike a simproc it does
  not fire on intermediate subterms during rewriting.

  The key issue with sos is that its internal @{ML "deepen"} loop has no
  upper bound: on unprovable goals it calls CSDP at depth 0, 1, 2, ...
  forever. We fix this by injecting a bounded CSDP wrapper that raises
  Failure after a fixed number of calls.
\<close>

ML \<open>
structure SOS_Solver = struct

(* Structural guard: is every subexpression a real polynomial/rational atom? *)
fun is_sos_expr t =
  case t of
    Const (@{const_name plus}, _) $ a $ b     => is_sos_expr a andalso is_sos_expr b
  | Const (@{const_name minus}, _) $ a $ b    => is_sos_expr a andalso is_sos_expr b
  | Const (@{const_name times}, _) $ a $ b    => is_sos_expr a andalso is_sos_expr b
  | Const (@{const_name uminus}, _) $ a       => is_sos_expr a
  | Const (@{const_name power}, _) $ a $ _    => is_sos_expr a
  | Const (@{const_name divide}, _) $ a $ b   => is_sos_expr a andalso is_sos_expr b
  | Const (@{const_name inverse}, _) $ a      => is_sos_expr a
  | Const (@{const_name abs}, _) $ a          => is_sos_expr a
  | Const (@{const_name min}, _) $ a $ b      => is_sos_expr a andalso is_sos_expr b
  | Const (@{const_name max}, _) $ a $ b      => is_sos_expr a andalso is_sos_expr b
  | Const (@{const_name zero_class.zero}, _)  => true
  | Const (@{const_name one_class.one}, _)    => true
  | Const (@{const_name numeral}, _) $ _      => true
  | Free (_, \<^Type>\<open>real\<close>)                       => true
  | Var (_, \<^Type>\<open>real\<close>)                        => true
  | _ => false

fun is_sos_comparison t =
  case t of
    Const (@{const_name less_eq}, \<^Type>\<open>fun \<^Type>\<open>real\<close> _\<close>) $ l $ r =>
      is_sos_expr l andalso is_sos_expr r
  | Const (@{const_name less}, \<^Type>\<open>fun \<^Type>\<open>real\<close> _\<close>) $ l $ r =>
      is_sos_expr l andalso is_sos_expr r
  | Const (@{const_name HOL.eq}, \<^Type>\<open>fun \<^Type>\<open>real\<close> _\<close>) $ l $ r =>
      is_sos_expr l andalso is_sos_expr r
  | _ => false

(* CSDP runner — same as SOS_Wrapper.run_solver but standalone *)
fun run_csdp ctxt input =
  Isabelle_System.with_tmp_file "sos_in" "" (fn in_path =>
    Isabelle_System.with_tmp_file "sos_out" "" (fn out_path =>
      let
        val _ = File.write in_path input
        val (output, rc) =
          Isabelle_System.bash_output
            ("\"$ISABELLE_CSDP\" " ^
              File.bash_platform_path in_path ^ " " ^
              File.bash_platform_path out_path)
        val _ = Sum_of_Squares.debug_message ctxt
          (fn () => "Solver output:\n" ^ output)
        val result = if File.exists out_path then File.read out_path else ""
      in
        (case rc of
           0 => result | 3 => result
         | 1 => raise Sum_of_Squares.Failure "SDP is primal infeasible"
         | 2 => raise Sum_of_Squares.Failure "SDP is dual infeasible"
         | _ => raise Sum_of_Squares.Failure ("CSDP rc=" ^ string_of_int rc))
      end))

val max_csdp_calls = 10

(* Re-entrancy guard: sos internals use the simplifier, which would
   re-trigger this solver. A thread-local flag prevents recursion. *)
val sos_running = Thread_Data.var () : bool Thread_Data.var

fun bounded_sos_tac ctxt =
  let
    val calls = Unsynchronized.ref 0
    fun bounded_solver input =
      (Unsynchronized.inc calls;
       if !calls > max_csdp_calls
       then error "SOS: call limit exceeded"
       else run_csdp ctxt input)
  in Sum_of_Squares.sos_tac ignore (Sum_of_Squares.Prover bounded_solver) ctxt end

fun sos_solver_tac ctxt = SUBGOAL (fn (goal, i) =>
  if Thread_Data.get sos_running = SOME true then no_tac
  else
    let val concl = Logic.strip_imp_concl goal |> HOLogic.dest_Trueprop
    in
      if is_sos_comparison concl
      then fn st =>
        let val result =
          Thread_Data.setmp sos_running (SOME true)
            (fn () => SINGLE (bounded_sos_tac ctxt i) st) ()
          handle ERROR _ => NONE
               | Sum_of_Squares.Failure _ => NONE
               | Fail _ => NONE
        in case result of SOME th => Seq.single th | NONE => Seq.empty end
      else no_tac
    end
    handle TERM _ => no_tac)

end
\<close>

setup \<open>
  map_theory_simpset (fn ctxt =>
    ctxt addSolver
      (Raw_Simplifier.mk_solver "sos" SOS_Solver.sos_solver_tac))
\<close>

(* ================================================================ *)
(* Tests                                                            *)
(* ================================================================ *)

text \<open>Trivial: solved by existing simp rules, solver not needed\<close>
lemma sos_test_1: "(x::real) ^ 2 \<ge> 0"
  by simp

text \<open>Nonlinear: simp alone cannot solve, solver kicks in via CSDP\<close>
lemma sos_test_2: "(a::real) ^ 2 + b ^ 2 \<ge> 2 * a * b"
  by simp

lemma sos_test_3: "(a1*b1 + a2*b2)^2 \<le> (a1^2 + a2^2) * (b1^2 + (b2::real)^2)"
  by simp

text \<open>Regression: non-sos goals still work\<close>
lemma "(n::nat) + 0 = n"
  by simp

lemma "sin (x::real) + sin x = 2 * sin x"
  by simp

lemma "((x::int) + y)^2 = x^2 + 2*x*y + y^2"
  by simp

text \<open>Test: structural guard\<close>
ML \<open>
let
  fun assert msg b = if b then () else error ("FAIL: " ^ msg)
  fun ok msg = writeln (msg ^ " [OK]")
  val expr = SOS_Solver.is_sos_expr
  val comp = SOS_Solver.is_sos_comparison
in
  assert "expr: rejects sin" (not (expr @{term "sin (x::real)"}));
  assert "expr: rejects exp" (not (expr @{term "exp (x::real)"}));
  assert "expr: accepts poly" (expr @{term "(x::real)^2 + 2*x + 1"});
  assert "expr: accepts abs" (expr @{term "\<bar>x::real\<bar>"});
  ok "is_sos_expr";
  assert "comp: accepts real le" (comp @{term "(x::real)^2 \<ge> 0"});
  assert "comp: accepts real eq" (comp @{term "(a::real)^2 + b^2 = 2*a*b"});
  assert "comp: rejects nat" (not (comp @{term "(n::nat) + 0 = n"}));
  assert "comp: rejects sin" (not (comp @{term "sin (x::real) \<ge> 0"}));
  ok "is_sos_comparison"
end
\<close>

end
