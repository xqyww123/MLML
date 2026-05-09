(* Simproc core: evaluate ground executable terms.
   - bool-typed: Code_Runtime via Trueprop wrapping (handles [code_unfold] fully)
   - other types: NBE (computes and reads back the result term) *)
structure Eval_Simproc : sig
  val eval_ground : Proof.context -> cterm -> thm option
end = struct

fun has_typ_vars_or_frees t =
  Term.exists_type (Term.exists_subtype (fn TFree _ => true | TVar _ => true | _ => false)) t

fun is_ground t =
  not (Term.exists_subterm Term.is_Free t) andalso not (Term.is_schematic t)
  andalso not (has_typ_vars_or_frees t)

fun is_executable_const ctxt thy c =
  Code.is_constr thy c
  orelse Code.is_abstr thy c
  orelse is_some (Axclass.class_of_param thy c)
  orelse (let val cert = Code.get_cert ctxt [] c
              val (_, eqns) = Code.equations_of_cert thy cert
          in is_some eqns end
          handle ERROR _ => true)

fun all_consts_executable ctxt t =
  let val thy = Proof_Context.theory_of ctxt
      val consts = Term.add_const_names t []
  in forall (is_executable_const ctxt thy) consts end

(* For bool: wrap in Trueprop, run Code_Runtime, strip back to bool equation.
   Tries P=True first, then ¬P=True (giving P=False). *)
fun eval_bool ctxt ct =
  let val prop_ct = Thm.apply \<^cterm>\<open>Trueprop\<close> ct
  in (* Try P = True *)
    (let val eq = Code_Runtime.dynamic_holds_conv ctxt prop_ct
     in if Thm.is_reflexive eq
        then (* Try ¬P = True, giving P = False *)
             let val neg_ct = Thm.apply \<^cterm>\<open>Not\<close> ct
                 val neg_prop_ct = Thm.apply \<^cterm>\<open>Trueprop\<close> neg_ct
                 val eq = Code_Runtime.dynamic_holds_conv ctxt neg_prop_ct
              in if Thm.is_reflexive eq then NONE
                 else SOME (eq RS @{lemma \<open>(Trueprop (\<not>P) \<equiv> Trueprop True) \<Longrightarrow> P \<equiv> False\<close>
                                       by (simp add: atomize_eq)})
              end
        else SOME (eq RS @{thm strip_Trueprop_eq})
     end)
    
  end

fun eval_ground ctxt ct =
  let val tm = Thm.term_of ct
      val is_bool = (Thm.typ_of (Thm.ctyp_of_cterm ct) = \<^typ>\<open>bool\<close>)
  in if is_ground tm andalso all_consts_executable ctxt tm then
       Timeout.apply (Time.fromSeconds 10) (fn () =>
         if is_bool then eval_bool ctxt ct
         else let val eq = Nbe.dynamic_conv ctxt ct
              in if Thm.is_reflexive eq then NONE else SOME eq end
       ) ()
       handle Match => NONE | ERROR _ => NONE | Timeout.TIMEOUT _ => NONE
     else NONE
  end

end
