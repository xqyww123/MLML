structure Sturm_Simproc : sig
  val sturm_simproc : Proof.context -> cterm -> thm option
end = struct

val poison_names =
  [@{const_name sin}, @{const_name cos}, @{const_name tan},
   @{const_name exp}, @{const_name ln}, @{const_name sqrt},
   @{const_name abs}, @{const_name sgn},
   @{const_name arctan}, @{const_name powr}]

fun has_poison body =
  Term.exists_subterm (fn
    Const (@{const_name divide}, _) $ _ $ denom =>
      loose_bvar (denom, 0)
  | Const (c, _) => member (op =) poison_names c
  | _ => false) body

fun body_has_frees body =
  Term.exists_subterm Term.is_Free body

fun is_sturm_candidate t =
  (case t of
    Const (@{const_name All}, _) $ Abs (_, @{typ real}, body) =>
      not (has_poison body) andalso not (body_has_frees body)
  | Const (@{const_name HOL.eq}, _) $
      (Const (@{const_name Finite_Set.card}, _) $
        (Const (@{const_name Collect}, _) $ Abs (_, @{typ real}, body))) $ rhs =>
      not (has_poison body) andalso not (body_has_frees body)
      andalso not (Term.exists_subterm Term.is_Free rhs)
  | _ => false)

fun run_sturm ctxt ct =
  let
    val goal = Goal.init (Thm.apply \<^cterm>\<open>Trueprop\<close> ct)
  in
    (case SINGLE (Sturm.sturm_tac ctxt false 1) goal of
       SOME th =>
         (case try (Goal.finish ctxt) th of
            SOME finished => SOME (finished RS @{thm Eq_TrueI})
          | NONE => NONE)
     | NONE => NONE)
  end

fun sturm_simproc ctxt ct =
  if not (is_sturm_candidate (Thm.term_of ct)) then NONE
  else
    Option.join (try (fn () =>
      Timeout.apply (Time.fromSeconds 10) (run_sturm ctxt) ct
      handle Timeout.TIMEOUT _ => NONE) ())

end
