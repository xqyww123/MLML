signature THEOREM_EXTRACTION = sig
include THEOREM_EXTRACTION

type theory_name = string
(* type theorem_name = theory_name * string * int option *)

val premise_selection : (string list -> unit) -> bool -> thm list
                     -> Sledgehammer.fact_override
                     -> Toplevel.state
                     -> (term * thm list) list

end

structure Theorem_Extraction : THEOREM_EXTRACTION = struct
open Theorem_Extraction

type theory_name = string
(* type theorem_name = theory_name * string * int option *)
                                                  
(*
fun fact_ref_to_name ctxt facts (Facts.Named ((name, _), iv)) : (theorem_name * thm) list =
  \<^try>\<open>
      let val iname = Facts.intern facts name
          val thy = Proof_Context.theory_of ctxt
          val shortname = Context.theory_name {long = false} thy
          val longname  = Context.theory_name {long = true } thy
          val thms = Proof_Context.get_thms ctxt name
          fun mk_name k =
                case first_field "." iname
                  of SOME (thy_name, _) =>
                       ( if thy_name = "local"
                         then ("<local>", )
                         else if shortname = thy_name
                         then longname
                         else Context.get_theory {long=false} thy thy_name
                           |> Context.theory_name {long = true}
                       , iname, k )
                   | NONE => ("", iname, k)
          fun mk_lst (Facts.FromTo (i,j)) =
                  List.tabulate (j-i+1, fn k => (mk_name (SOME (i+k)), nth thms k))
            | mk_lst (Facts.From i) = mk_lst (Facts.FromTo (i, length thms))
            | mk_lst (Facts.Single i) = mk_lst (Facts.FromTo (i, i))
       in case thms
       of [thm] => [(mk_name NONE, thm)]
        | _ => (case iv
       of SOME ivs => maps mk_lst ivs
        | NONE => mk_lst (Facts.FromTo (1, length thms)))
      end
   catch E => raise E
   \<close>
  | fact_ref_to_name _ _ _ = [] *)

val full_keywords = Thy_Header.get_keywords \<^theory>

fun dirty_hack debug ctxt relevant_facts_store s =
  let val _ = debug ["SH", s]
      fun find c s = CharVector.foldri (fn (i, c', ret) => if c' = c then i :: ret else ret) [] s
      val inds = find #"\^E" s
   in if length inds < 4
      then () (* tracing s *)
      else let
        val _ = debug ["Enter dirty hack"]
        val i2 = List.nth (inds, 1)
        val i3 = List.nth (inds, 2)
     (* val i4 = List.nth (inds, 3) *)
        val s_prf = String.substring (s, i2+1, i3 - 1 -i2)
        val ast  = Symbol_Pos.explode (s_prf, Position.none)
                |> Token.tokenize full_keywords {strict = false}
                |> Outer_Syntax.parse_spans
                |> map ( Command_Span.content
                      #> filter Token.is_proper )
                |> try MinLang_Translator.parse_isar_no_state
                |> (fn SOME x => x
                     | NONE => [])
        val (w, _) = MinLang_Translator.collect_facts ast
        val thy = Proof_Context.theory_of ctxt
        val relevant_facts = Attrib.eval_thms ctxt w
         in debug ["Before Synchronized.change"]
          ; Synchronized.change relevant_facts_store (union (Thm.equiv_thm thy) relevant_facts)
          ; debug ["After Synchronized.change"]
       end
  end

val silence_state =
      Proof.map_contexts (Try0.silence_methods false #> Config.put SMT_Config.verbose false)

fun raw_premise_selection debug override stat =
  let val ctxt = Proof.context_of stat
      val goals = #goal (Proof.raw_goal stat) |> Thm.prems_of
      (* val ret : string list Synchronized.var = Synchronized.var "raw_sledgehammer" [] *)
      val sledgehammer_params =
              ("try0", "false") :: ("preplay_timeout", "0") ::
              Phi_Sledgehammer_Solver.get_sledgehammer_params (Proof.context_of stat)
      val params = Sledgehammer_Commands.default_params (Proof.theory_of stat) sledgehammer_params
      val stat' = (silence_state stat)
      fun collect (i, goal) =
        let val relevant_facts_store = Synchronized.var "relevant_facts" []
            val _ = debug ["before run_sledgehammer"]
            val tmp = Sledgehammer.run_sledgehammer params
                Sledgehammer_Prover.Normal
                  (SOME (dirty_hack debug ctxt relevant_facts_store)) (i+1) override
                stat'
            val _ = debug ["after run_sledgehammer"]
         in (goal, Synchronized.value relevant_facts_store)
        end
   in map_index collect goals
  end

val timeout = Time.fromSeconds 3
fun premise_selection debug first_or_all wthms override toplevel =
  let val stat = Toplevel.proof_of toplevel
   in if Proof.goal_finished stat
     then []
     else let
      val stat = stat
              |> Proof.refine_insert []
              |> first_or_all ? Proof.refine_primitive (fn _ => Goal.protect 1)
      fun timeout_pull seq =
            Timeout.apply timeout Seq.pull seq
            handle Timeout.TIMEOUT _ => NONE
      fun timeout_tac tac = (fn th => Seq.make (fn () =>
            Timeout.apply timeout Seq.pull (tac th)
            handle Timeout.TIMEOUT _ => NONE))
      val _ = debug ["AAAA1"]
      val stat's = Seq.append
         (Proof.refine (Method.Basic (fn ctxt =>
                Method.METHOD (K (timeout_tac (Clasimp.auto_tac ctxt))))) stat)
         (Proof.refine (Method.Basic (fn ctxt =>
                Method.METHOD (K (ALLGOALS (timeout_tac o Clasimp.clarsimp_tac ctxt))))) stat)
         |> Seq.filter_results
      val thy = Toplevel.theory_of toplevel
   in(case (let val _ = debug ["Before pulling auto"]
                val ret = timeout_pull stat's
                val _ = debug ["After pulling auto"]
             in ret
            end )
        of SOME (stat', _) =>
            let val goal = #goal (Proof.goal stat)
                val goal'= #goal (Proof.goal stat')
             in if Thm.prop_of goal aconv Thm.prop_of goal'
              then let
                  val _ = debug ["Before raw_premise_selection 11"]
                  val ret = raw_premise_selection debug override stat
                  val _ = debug ["After raw_premise_selection 11"]
                   in ret
                   |> map (apsnd (union (Thm.equiv_thm thy) wthms))
                  end
              else let
                val _ = debug ["Before raw_premise_selection XX1"]
                val premises  = raw_premise_selection debug override stat
                             |> map (apsnd (union (Thm.equiv_thm thy) wthms))
                val _ = debug ["Before raw_premise_selection XX2"]
                val premises' = raw_premise_selection debug override stat'
                val _ = debug ["After raw_premise_selection XX3"]
                 in AList.join (op aconv) (fn _ => merge (Thm.equiv_thm thy)) (premises', premises)
                end
            end
         | NONE => let
                 val _ = debug ["Before raw_premise_selection OO"]
                 val ret = raw_premise_selection debug override stat
                 val _ = debug ["After raw_premise_selection OO"]
                  in ret
                  |> map (apsnd (union (Thm.equiv_thm thy) wthms))
                 end
    ) |> filter_out (null o snd)
  end end

end