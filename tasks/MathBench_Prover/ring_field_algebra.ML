structure Ring_Field_Algebra : sig
  val ring_field_simproc : Proof.context -> cterm -> thm option
  val algebra_solver     : Proof.context -> int -> tactic
  val field_looper       : Proof.context -> int -> tactic
  val is_ring_expr  : term -> bool
  val is_field_expr : term -> bool
  val has_division      : term -> bool
  val has_algebra_eq    : term -> bool
  val trigger_consts_of : Proof.context -> unit Symtab.table
  val merge_one_conv     : Proof.context -> conv
  val merge_prems_conv   : Proof.context -> conv
  val merge_n_prems_conv : Proof.context -> int -> conv
  val merge_prems        : Proof.context -> thm -> thm
  val try_ring  : Proof.context -> cterm -> thm option
  val try_field : Proof.context -> cterm -> thm option
end = struct

(* --- Guards --- *)

fun is_poly_expr recurse t =
  case t of
    Const (@{const_name plus}, _) $ a $ b     => recurse a andalso recurse b
  | Const (@{const_name minus}, _) $ a $ b    => recurse a andalso recurse b
  | Const (@{const_name times}, _) $ a $ b    => recurse a andalso recurse b
  | Const (@{const_name uminus}, _) $ a       => recurse a
  | Const (@{const_name power}, _) $ a $ _    => recurse a
  | Const (@{const_name zero_class.zero}, _)  => true
  | Const (@{const_name one_class.one}, _)    => true
  | Const (@{const_name numeral}, _) $ _      => true
  | Free _  => true
  | Var _   => true
  | Bound _ => true
  | _       => false

fun is_ring_expr t = is_poly_expr is_ring_expr t

fun is_field_expr t =
  case t of
    Const (@{const_name divide}, _) $ a $ b => is_field_expr a andalso is_field_expr b
  | Const (@{const_name inverse}, _) $ a    => is_field_expr a
  | _ => is_poly_expr is_field_expr t

fun has_division t =
  Term.exists_subterm (fn
    Const (@{const_name divide}, _) $ _ $ _ => true
  | Const (@{const_name inverse}, _) $ _    => true
  | _ => false) t

(* --- Premise merging via conversions --- *)

(* (Trueprop P ==> Trueprop Q ==> R) == (Trueprop (P & Q) ==> R) *)
fun merge_one_conv ctxt ct =
  let
    val (prem1_ct, inner_ct) = Thm.dest_implies ct
    val (prem2_ct, rest_ct) = Thm.dest_implies inner_ct
    val P = HOLogic.dest_Trueprop (Thm.term_of prem1_ct)
    val Q = HOLogic.dest_Trueprop (Thm.term_of prem2_ct)
    val conj_prem = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_conj (P, Q)))
    val rhs_ct = Thm.cterm_of ctxt
      (Logic.mk_implies (Thm.term_of conj_prem, Thm.term_of rest_ct))

    val conj_assumed = Thm.assume conj_prem
    val fwd = Thm.assume ct
      |> (fn th => Thm.implies_elim th (conj_assumed RS @{thm conjunct1}))
      |> (fn th => Thm.implies_elim th (conj_assumed RS @{thm conjunct2}))
      |> Thm.implies_intr conj_prem
      |> Thm.implies_intr ct

    val bwd = Thm.implies_elim (Thm.assume rhs_ct)
        (@{thm conjI} OF [Thm.assume prem1_ct, Thm.assume prem2_ct])
      |> Thm.implies_intr prem2_ct
      |> Thm.implies_intr prem1_ct
      |> Thm.implies_intr rhs_ct
  in Thm.equal_intr fwd bwd end

(* Bottom-up: produces right-associative conjunction *)
fun merge_prems_conv ctxt ct =
  (case Thm.term_of ct of
    Const ("Pure.imp", _) $ _ $ (Const ("Pure.imp", _) $ _ $ _) =>
      (Conv.implies_concl_conv (merge_prems_conv ctxt)
       then_conv merge_one_conv ctxt) ct
  | _ => Conv.all_conv ct)

fun merge_n_prems_conv _ 1 ct = Conv.all_conv ct
  | merge_n_prems_conv ctxt n ct =
      (Conv.implies_concl_conv (merge_n_prems_conv ctxt (n - 1))
       then_conv merge_one_conv ctxt) ct

fun merge_prems ctxt th =
  if Thm.nprems_of th <= 1 then th
  else Conv.fconv_rule (merge_prems_conv ctxt) th

fun merge_new_subgoals ctxt i n_before st =
  let
    val n_after = Thm.nprems_of st
    val n_new = n_after - n_before + 1
  in
    if n_new <= 1 then st
    else
      let
        val rotated = Drule.rotate_prems (i - 1) st
        val merged = Conv.fconv_rule (merge_n_prems_conv ctxt n_new) rotated
      in Drule.rotate_prems (Thm.nprems_of merged - (i - 1)) merged end
  end

(* --- Simproc --- *)

fun try_ring ctxt ct =
  Option.join (try (fn () =>
    let val goal = Goal.init (Thm.apply \<^cterm>\<open>Trueprop\<close> ct)
    in case SINGLE (Ring_Tac.ring_tac false [] ctxt 1) goal of
         SOME th => SOME (Goal.finish ctxt th RS @{thm Eq_TrueI})
       | NONE => NONE
    end) ())

fun try_field ctxt ct =
  Option.join (try (fn () =>
    let val goal = Goal.init (Thm.apply \<^cterm>\<open>Trueprop\<close> ct)
    in case SINGLE (Field_Tac.field_tac false ctxt 1
                     THEN Ring_Tac.ring_tac false [] ctxt 1) goal of
         SOME th =>
           let val merged = merge_prems ctxt (Goal.conclude th)
           in SOME (merged RS @{thm Eq_TrueI}) end
       | NONE => NONE
    end) ())

fun ring_field_simproc ctxt ct =
  Option.join (try (fn () =>
    let val tm = Thm.term_of ct
    in case tm of
         Const (@{const_name HOL.eq}, _) $ lhs $ rhs =>
           if not (is_field_expr lhs andalso is_field_expr rhs) then NONE
           else
             (Timeout.apply (Time.fromSeconds 10) (fn () =>
               case try_ring ctxt ct of
                 SOME th => SOME th
               | NONE =>
                   if Sign.of_sort (Proof_Context.theory_of ctxt)
                        (fastype_of lhs, @{sort field})
                      andalso has_division tm
                   then try_field ctxt ct
                   else NONE) ()
              handle Timeout.TIMEOUT _ => NONE)
       | _ => NONE
    end) ())

(* --- Solver --- *)

fun has_algebra_eq t =
  Term.exists_subterm (fn
    Const (@{const_name HOL.eq}, T) $ lhs $ rhs =>
      domain_type T <> HOLogic.boolT
      andalso is_field_expr lhs andalso is_field_expr rhs
  | _ => false) t

val ring_vocab = Symtab.make (map (fn n => (n, ()))
  [@{const_name HOL.eq}, @{const_name Trueprop},
   @{const_name HOL.conj}, @{const_name HOL.disj}, @{const_name HOL.implies},
   @{const_name Not}, @{const_name All}, @{const_name Ex},
   @{const_name plus}, @{const_name minus}, @{const_name times},
   @{const_name uminus}, @{const_name power},
   @{const_name zero_class.zero}, @{const_name one_class.one},
   @{const_name numeral}, @{const_name divide}, @{const_name inverse},
   "Pure.imp", "Pure.eq", "Pure.all",
   "Num.num.One", "Num.num.Bit0", "Num.num.Bit1"])

fun trigger_consts_of ctxt =
  let
    val ths = Named_Theorems.get ctxt @{named_theorems algebra}
    val all = fold (fn th =>
      Term.fold_aterms (fn Const (n, _) => Symtab.update (n, ()) | _ => I)
        (Thm.prop_of th)) ths Symtab.empty
  in
    Symtab.fold (fn (n, ()) =>
      if Symtab.defined ring_vocab n then I
      else Symtab.update (n, ())) all Symtab.empty
  end

fun run_algebra ctxt i st =
  the_default Seq.empty (try (fn () =>
    Timeout.apply (Time.fromSeconds 5) (fn () =>
      case Seq.pull (Groebner.algebra_tac [] [] ctxt i st) of
        SOME (th, _) => Seq.single th
      | NONE => Seq.empty) ()) ())

fun algebra_solver ctxt =
  let
    val triggers = trigger_consts_of ctxt
    fun has_trigger t =
      Term.exists_subterm (fn Const (n, _) => Symtab.defined triggers n | _ => false) t
    val presimp = asm_full_simp_tac (put_simpset HOL_basic_ss ctxt
      addsimps (Named_Theorems.get ctxt @{named_theorems algebra}))
  in SUBGOAL (fn (subgoal, i) =>
    if has_algebra_eq subgoal then run_algebra ctxt i
    else if has_trigger subgoal then
      (presimp THEN' SUBGOAL (fn (subgoal', i') =>
        if has_algebra_eq subgoal' then run_algebra ctxt i'
        else no_tac)) i
    else no_tac)
  end

(* --- Looper --- *)

fun field_looper ctxt = SUBGOAL (fn (subgoal, i) =>
  let
    val concl = Logic.strip_assums_concl subgoal
    val dominated = case try HOLogic.dest_Trueprop concl of
        SOME (Const (@{const_name HOL.eq}, T) $ lhs $ rhs) =>
          is_field_expr lhs andalso is_field_expr rhs
          andalso Sign.of_sort (Proof_Context.theory_of ctxt) (domain_type T, @{sort field})
          andalso has_division (HOLogic.mk_eq (lhs, rhs))
      | _ => false
  in
    if not dominated then no_tac
    else fn st =>
      the_default Seq.empty (try (fn () =>
        let val n_before = Thm.nprems_of st
        in case Seq.pull ((Field_Tac.field_tac false ctxt i THEN Ring_Tac.ring_tac false [] ctxt i) st) of
             SOME (th, _) => Seq.single (merge_new_subgoals ctxt i n_before th)
           | NONE => Seq.empty
        end) ())
  end)

end
