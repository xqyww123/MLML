theory Scratch_NoNotation_Test
  imports MathBench_ProverBase.MathBench_ProverBase
begin

section \<open>Control: which notations are active in the base session\<close>

term \<open>(F::'a fps) $ n\<close>                                              (* C01 fps_nth *)
term \<open>(D::'a::zero fds) $ n\<close>                                        (* C02 fds_nth *)
term \<open>\<chi> n. f n\<close>                                                     (* C03 binder chi: ambiguous iff fds active *)
term \<open>(v::'b Matrix.vec) $ i\<close>                                       (* C04 JNF vec_index *)
term \<open>(g::('a::real_normed_vector, 'b::real_normed_vector) blinfun) $ x\<close>  (* C05 blinfun_apply *)
term \<open>(v::'a::semiring_0 Matrix.vec) \<bullet> w\<close>                           (* C06 JNF scalar_prod *)
term \<open>a *c b\<close>                                                       (* C07 cprod *)
term \<open>a +c b\<close>                                                       (* C08 csum *)
term \<open>a ^c b\<close>                                                       (* C09 cexp *)
term \<open>(r::'a rel) =o (s::'b rel)\<close>                                   (* C10 ordIso2 *)
term \<open>r <o s\<close>                                                       (* C11 ordLess2 *)
term \<open>r <=o s\<close>                                                      (* C12 ordLeq2 *)
term \<open>k *k (A::'a::ab_semigroup_mult^'n^'m)\<close>                        (* C13 matrix_scalar_mult *)
term \<open>(c::'a::times) *\<^sub>S (M::'a^^'n)\<close>                                (* C14 NEW Cayley smult *)
term \<open>A *iv x\<close>                                                      (* C15 *)
term \<open>x v*i A\<close>                                                      (* C16 *)
term \<open>v v* (m::'a::semiring_1^'n^'m)\<close>                               (* C17 *)
term \<open>(<s)\<close>                                                         (* C18 word_sless prefix *)
term \<open>a <s b\<close>                                                       (* C19 word_sless infix *)
term \<open>(<=s)\<close>                                                        (* C20 OLD word_sle prefix *)
term \<open>a <=s b\<close>                                                      (* C21 word_sle ASCII input *)
term \<open>(\<le>s)\<close>                                                         (* C22 NEW word_sle prefix *)
term \<open>a \<le>s b\<close>                                                       (* C23 NEW word_sle infix *)
term \<open>a *o B\<close>                                                       (* C24 elt_set_times *)
term \<open>a +o B\<close>                                                       (* C25 elt_set_plus *)
term \<open>(x::'a) =o (A::'a set)\<close>                                       (* C26 elt_set_eq *)
term \<open>SUM x. f x\<close>                                                   (* C27 Sum_any ASCII *)
term \<open>\<Sum>x. f x\<close>                                                      (* C28 Sum_any *)

section \<open>Replicated removal block (verbatim from MathBench_Prover.thy lines 5-36)\<close>

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
  "_Sum_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add" (‹(‹indent=3 notation=‹binder SUM››SUM _. _)› [0, 10] 10)
no_syntax
  "_Sum_any" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a::comm_monoid_add" (‹(‹indent=2 notation=‹binder ∑››∑_. _)› [0, 10] 10)
no_translations
  "\<Sum>a. b" \<rightleftharpoons> "CONST Sum_any (\<lambda>a. b)"

section \<open>After: same probes again\<close>

term \<open>(F::'a fps) $ n\<close>                                              (* A01 *)
term \<open>(D::'a::zero fds) $ n\<close>                                        (* A02 *)
term \<open>\<chi> n. f n\<close>                                                     (* A03 *)
term \<open>(v::'b Matrix.vec) $ i\<close>                                       (* A04 *)
term \<open>(g::('a::real_normed_vector, 'b::real_normed_vector) blinfun) $ x\<close>  (* A05 *)
term \<open>(v::'a::semiring_0 Matrix.vec) \<bullet> w\<close>                           (* A06 *)
term \<open>a *c b\<close>                                                       (* A07 *)
term \<open>a +c b\<close>                                                       (* A08 *)
term \<open>a ^c b\<close>                                                       (* A09 *)
term \<open>(r::'a rel) =o (s::'b rel)\<close>                                   (* A10 *)
term \<open>r <o s\<close>                                                       (* A11 *)
term \<open>r <=o s\<close>                                                      (* A12 *)
term \<open>k *k (A::'a::ab_semigroup_mult^'n^'m)\<close>                        (* A13 *)
term \<open>(c::'a::times) *\<^sub>S (M::'a^^'n)\<close>                                (* A14 *)
term \<open>A *iv x\<close>                                                      (* A15 *)
term \<open>x v*i A\<close>                                                      (* A16 *)
term \<open>v v* (m::'a::semiring_1^'n^'m)\<close>                               (* A17 *)
term \<open>(<s)\<close>                                                         (* A18 *)
term \<open>a <s b\<close>                                                       (* A19 *)
term \<open>(<=s)\<close>                                                        (* A20 *)
term \<open>a <=s b\<close>                                                      (* A21 *)
term \<open>(\<le>s)\<close>                                                         (* A22 *)
term \<open>a \<le>s b\<close>                                                       (* A23 *)
term \<open>a *o B\<close>                                                       (* A24 *)
term \<open>a +o B\<close>                                                       (* A25 *)
term \<open>(x::'a) =o (A::'a set)\<close>                                       (* A26 *)
term \<open>SUM x. f x\<close>                                                   (* A27 *)
term \<open>\<Sum>x. f x\<close>                                                      (* A28 *)

term \<open>word_sless a b\<close>                                               (* P1 print check *)
term \<open>word_sle a b\<close>                                                 (* P2 print check *)

section \<open>Proposed corrected removals (2025-2 mixfixes)\<close>

no_notation word_sless (‹(‹notation=‹infix <s››_/ <s _)›  [51, 51] 50)
no_notation word_sle (‹'(\<le>s')›)
no_notation word_sle (‹(‹notation=‹infix \<le>s››_/ \<le>s _)›  [51, 51] 50)
no_notation (input) word_sle (‹(‹notation=‹infix <=s››_/ <=s _)›  [51, 51] 50)

term \<open>a <s b\<close>                                                       (* F1: expect NOT word_sless *)
term \<open>a \<le>s b\<close>                                                       (* F2: expect NOT word_sle *)
term \<open>a <=s b\<close>                                                      (* F3: expect NOT word_sle *)
term \<open>(\<le>s)\<close>                                                         (* F4: expect error *)
term \<open>word_sless a b\<close>                                               (* F5: expect prints word_sless *)
term \<open>word_sle a b\<close>                                                 (* F6: expect prints word_sle *)

end
