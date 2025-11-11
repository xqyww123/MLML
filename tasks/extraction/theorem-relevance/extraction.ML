signature THEOREM_EXTRACTION = sig
include THEOREM_EXTRACTION

type reporter

val interactive_reporter : reporter
val init_translator : reporter -> unit
val extraction_file : string -> unit

end

structure Theorem_Extraction : THEOREM_EXTRACTION = struct
open Theorem_Extraction

val ac_shuffle_num = 40

type goal = string
type thm_expr = string
type reporter = {
        start: Position.T -> bool,
        premise_group: Position.T
                    -> (goal * (thm_expr list * goal list (*ac-shuffle*))) list
                    -> unit,
        notify_theorems: Proof.context -> (thm_expr * thm) list -> unit,
        report_errors : string list -> unit
     }


fun is_goal_command (Command_Span.Command_Span (name, _)) =
      member (op =) ["lemma", "theorem", "schematic_goal", "proposition", "corollary",
                     "interpretation", "global_interpretation", "sublocale"] name
  | is_goal_command _ = false
fun is_goal_command' (Command_Span.Span (k, _)) = is_goal_command k

fun print_term_ ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types true
              |> Config.put Printer.show_sorts true
     in Syntax.string_of_term ctxt'
     #> REPL.trim_makrup
    end

fun pos_packer pos =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      val {line, offset, end_offset, props} = Position.dest pos
      val {label, file, id} = props
   in packTuple4 (packInt, packInt, packInt, packTuple3 (packString, packString, packString))
      (line, offset, end_offset, (label, file, id))
  end

fun socket_reporter pos_tr (cin,cout) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
   (* val packError  = packString o Minilang_Aux.trim_markup o String.concat o Runtime.exn_message_list
      val packErrors = packList packError *)
      val pos_packer = pos_packer o pos_tr
      val known_premises = Synchronized.var "Theorem_Extraction.known_premises" Symtab.empty
      fun read packer = let val (ret, cin') = doUnpack packer (!cin)
                         in cin := cin'
                          ; ret
                        end
   in { start = (fn pos =>
          let val _ = doPack (packPair (packInt, pos_packer)) (0, pos) cout 
              val _ = BinIO.StreamIO.flushOut cout
           in read unpackBool
          end),
        premise_group = (fn pos => fn data => (
          doPack (packTuple3 (packInt, pos_packer,
                    packPairList (packString,
                        packPair (packList packString, packList packString))))
                 (1, pos, data)
                 cout
        ; BinIO.StreamIO.flushOut cout
        )),
        notify_theorems = (fn ctxt => fn premises =>
          Synchronized.change known_premises (fn tabs =>
          let val premises' = filter_out (Symtab.defined tabs o fst) premises
              val _ = doPack (packPair (packInt, packList packString))
                             (2, map fst premises') cout
              val _ = BinIO.StreamIO.flushOut cout
              val seen = read (unpackList unpackString)
              val print = print_term_ ctxt
              val get_ac = ac_shuffle ac_shuffle_num (Context.Proof ctxt)
              fun pass thm = map print (get_ac (Thm.prop_of thm))
              val premises'1 = filter_out (member (op =) seen o fst) premises'
                            |> map (apsnd pass)
           in doPack (packPair (packInt,
                    packPairList (packString, packList packString))
                ) (3, premises'1) cout
            ; BinIO.StreamIO.flushOut cout
            ; fold (Symtab.update o rpair ()) seen tabs
          end )),
        report_errors = (fn errs => (
              doPack (packPair (packInt, packList packString)) (4, errs) cout
            ; BinIO.StreamIO.flushOut cout ))
    } : reporter
  end

val interactive_reporter = let open Pretty
  in {
    start = (fn pos => (
      tracing (string_of (block [str "Start ", position pos])) ;
      true
    )),
    premise_group = (fn pos => fn data =>
      tracing (string_of (chunks (
            block [str "Position:", brk 1, position pos]
         :: map (fn (goal, (thms, acs)) =>
              item [chunks [
                  para goal
                , str "Dependent theorems"
                , chunks (map (item o text) thms) 
                , str "AC shuffle"
                , chunks (map (item o text) acs)
                  ]]) data
         )))),
    notify_theorems = (fn ctxt => fn thms =>
      tracing (string_of (chunks (
          para "New theorem(s):"
       :: map (fn (name, th) =>
            item [Syntax.pretty_term ctxt (Thm.prop_of th)]
          ) thms )))),
    report_errors = (fn errs =>
      warning (string_of (chunks (map para errs))) )
    }
  end

fun collect stat commands =
  let open Minilang_Aux
      fun extraction _ ret [] = ret
        | extraction stat ret (all_commands as (tr, _) :: commands) =
            let fun fallback () =
                     case Toplevel.command_errors true tr stat
                       of ([], SOME stat') => extraction stat' ret commands
                        | _ => error "BUG extraction_thor - Isar evaluation fails"
                fun collect_premises ret commands =
                  let (* val ctxt = Toplevel.context_of stat
                     val sequent = #goal (Proof.goal (Toplevel.proof_of stat)) *)

                     val tactics = extract_proof all_commands
                     val origin_prf = tactics
                                   |> map ( filter Token.is_proper
                                          o Command_Span.content o snd)
                     val origin_ast = try MinLang_Translator.parse_isar (stat, origin_prf)
                                   |> the_default []
                     val (w,wo) = MinLang_Translator.collect_facts origin_ast
                     val override = { add = w, del = wo, only = false }
                     fun pass stat ret [] = (stat, ret)
                       | pass stat ret ((tr,_) :: cmds) =
                          let val premises = premise_selection override stat
                              val ctxt = Toplevel.context_of stat
                              val print = print_term_ ctxt
                              val get_acs = ac_shuffle ac_shuffle_num (Context.Proof ctxt)
                              val assms = Assumption.all_assms_of (Toplevel.context_of stat)
                                       |> map Thm.term_of
                              val premises = premises
                                    |> map (fn (raw_goal, prems) =>
                                        let val goal = Logic.list_implies (assms, raw_goal)
                                         in (print goal,
                                              ( map (`(print o Thm.prop_of)) prems,
                                                map print (get_acs goal)))
                                        end )
                              fun join (pa,ga) (pb,gb) = (pa @ pb, ga @ gb)
                              val ret' = fold (fn (k,v) => Symtab.map_default (k, ([],[])) (join v))
                                              premises ret
                              val (stat', _) = Toplevel.transition false tr stat
                           in pass stat' ret' cmds
                          end
                   in pass stat ret commands
                  end
             in (*
            if unsuported span
            then raise Unsupported "oops or sorry"
            else *) if Toplevel.is_proof stat andalso
                       begin_with_tactic all_commands
            then let val tactics = extract_tactic all_commands
                     val (stat', ret') = collect_premises ret tactics
                  (* val pos = case Command_Span.kind (snd (hd tactics))
                                 of Command_Span.Command_Span (_, pos) => pos
                                  | _ => error "BUG" *)
                  in extraction stat' ret' (remove_tactic all_commands)
                 end
            else fallback ()
            end
   in extraction stat Symtab.empty commands
   |> Symtab.dest
  end


fun REPL_plugin (reporter : reporter) : REPL.collector =
      fn _ => fn {current_command, state, remaining} =>
  let val pos = case current_command of Command_Span.Span (Command_Span.Command_Span (_, pos), _) => pos
                   | _ => Position.none
   in if is_goal_command' current_command andalso
        Toplevel.is_proof state andalso
         let val st = #goal (Proof.raw_goal (Toplevel.proof_of state))
          in not (Thm.is_dummy st) andalso not (Thm.no_prems st)
         end
    then if #start reporter pos
      then let
          val proof = Minilang_Aux.extract_proof remaining
          val data = collect state proof
          val premise_group = map (apsnd (apfst (map fst))) data
          val theorems = maps (fst o snd) data
          val ctxt = Toplevel.context_of state
       in #premise_group reporter pos premise_group
        ; #notify_theorems reporter ctxt theorems
        ; (NONE, NONE)
      end
      else (NONE, NONE)
    else (NONE, NONE)
  end

fun init_translator reporter = (
      REPL.init_repler NONE
    ; REPL.set_register_thy false
    ; REPL.register_plugin ("Theorem_Extraction", REPL_plugin reporter) )

exception Bad_Source of string list

fun extraction_src cfg src =
  let val errs = REPL.collect_erros (REPL.RE cfg src)
   in if null errs
    then ()
    else raise Bad_Source errs
  end

fun extraction_file path =
  let val path' = Path.explode path
      val thy_qualifier = the_default "HOL" (REPL_Aux.parse_session_name path')
      val src = File.read path'
      val dir = Path.dir path'
   in extraction_src { thy_qualifier = thy_qualifier,
                      file = SOME path,
                      position_label = NONE,
                      additional_libs = [] (*["Minilang.Minilang_Base"]*),
                      import_dir = NONE,
                      single_cmd_timeout = NONE,
                      attributes = [],
                      base_dir = dir,
                      write_thy = false }
                    src
  end

fun REPL_App (cin, cout, toplevel) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      fun read packer = let val (ret, cin') = doUnpack packer (!cin)
                         in cin := cin'
                          ; ret
                        end
      val path = read unpackString

      val path' = Path.explode path
      val src = File.read path'
      val (_, tr) = REPL_Aux.column_of_pos src
      val reporter = socket_reporter tr (cin,cout)

   in init_translator reporter
    ; \<^try>\<open>extraction_file path
        catch Bad_Source errs => #report_errors reporter errs \<close>
    ; doPack packInt 5 cout
    ; BinIO.StreamIO.flushOut cout
    ; toplevel
  end

val _ = REPL_Server.register_app "Premise_Extraction" REPL_App

end