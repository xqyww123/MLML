structure Goal_state_Extraction = struct

type goal_pos = Position.T
type pp_name = REPL_Serialize.pp_name
datatype location = Inline  (*add a space, then insert the annotation*)
                  | Newline of int (*insert a new line, and then the annotation*)
type target_cmd = string
type annotations = ((target_cmd * Position.T * location) * (pp_name * string) list) list
type reporter = {
        start: goal_pos -> bool,
        report: goal_pos -> annotations * (string * annotations) option -> unit,
        debug: string list -> unit,
        error: string list -> unit
     }

fun pos_packer pos =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      val {line, offset, end_offset, props} = Position.dest pos
      val {label, file, id} = props
   in packTuple4 (packInt, packInt, packInt, packTuple3 (packString, packString, packString))
      (line, offset, end_offset, (label, file, id))
  end

local open MessagePackBinIO.Unpack MessagePackBinIO.Pack
in
fun read cin packer =
      let val (ret, cin') = doUnpack packer (!cin)
       in cin := cin'
        ; ret
      end
fun send cout packer data = (
      doPack packer data cout
    ; BinIO.StreamIO.flushOut cout)
end

fun socket_reporter pos_tr (cin,cout) : reporter =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      val tr_pos_packer = pos_packer o pos_tr
      val location = packTuple3 (packString, tr_pos_packer,
                        packOption packInt o (fn Inline => NONE | Newline i => SOME i))
      val pack_annotation = packList (packPair (location, packPairList (packString, packString)))
   in { start = (fn pos => (
            send cout (packPair (packInt, tr_pos_packer)) (0, pos)
          ; read cin unpackBool))
      , report = (fn pos => fn annotations =>
            send cout
                 (packTuple3 (packInt, tr_pos_packer,
                    packPair (pack_annotation, packOption (packPair (packString, pack_annotation)))))
                 (1, pos, annotations))
      , debug = (fn msgs => send cout (packPair (packInt, packList packString)) (2, msgs) )
      , error = (fn msgs => send cout (packPair (packInt, packList packString)) (3, msgs) )
      }
  end


val single_cmd_timeout = Time.fromSeconds 150

exception Partial_Ret of annotations

fun end_pos_of shift pos =
  Position.make {
    line = the_default 0 (Position.line_of pos),
    offset = the_default 1 (Position.end_offset_of pos) - 1 + shift,
    end_offset = the_default 1 (Position.end_offset_of pos) + shift,
    props= { label = the_default "" (Position.label_of pos),
             file = the_default "" (Position.file_of pos),
             id = the_default "" (Position.id_of pos) }
  }

fun last [] = error "no last"
  | last [x] = x
  | last (_ :: L) = last L

fun parse_end_pos parser toks =
  let val (ret, toks') = parser toks
      val used = Token.pos_of (last (take (length toks') toks))
   in ((ret, end_pos_of 0 used), toks')
  end

fun show_all_goals pos stat pp_names =
  if Toplevel.is_proof stat
  then let val state = Toplevel.proof_of stat
   in [(pos, pp_names ~~ MinLang_Translator.print_all_goals pp_names state)]
  end else []

fun show_this pos stat pp_names =
  if Toplevel.is_proof stat
  then let val state = Toplevel.proof_of stat
    in [(pos, pp_names ~~ MinLang_Translator.print_this_fact pp_names state)]
   end else []

fun is_dummy (Const(\<^const_name>\<open>Pure.term\<close>, _) $ _) = true
  | is_dummy tm = Term.is_dummy_pattern tm

fun annotate_facts_in_cmd stat cmd raw_tokens pp_names =
  let val tokens = filter Token.is_proper raw_tokens @ [Token.eof]
      val (facts, _) = Scan.repeat (parse_end_pos Parse.thm) tokens
      val ctxt = Toplevel.context_of stat
      fun SOT pp_name = REPL_Serialize.string_of_term pp_name (Context.Proof ctxt)
   in map_filter (fn (fact, pos) =>
      let val props = map Thm.prop_of (Attrib.eval_thms ctxt [fact])
                   |> filter_out is_dummy
          val key = (cmd, pos, Inline)
       in case props
       of [] => NONE
        | [prop] => SOME (key, map (fn pp => (pp, String.concat ["(*\<open>", SOT pp prop, "\<close>*)"])) pp_names)
        | _ => SOME (key, map (fn pp =>
                (pp, String.concat ("(*" ::
                  Minilang_Aux.implode_with " " (map (fn prop => ["\<open>", SOT pp prop, "\<close>"]) props) @ ["*)"]))
              ) pp_names)
      end) facts
  end

fun show_calculation pos stat pp_names =
  if Toplevel.is_proof stat
  then let val state = Toplevel.proof_of stat
    in [(pos, pp_names ~~ MinLang_Translator.print_calculation pp_names state)]
  end else []

fun has_macro tokens =
  let fun check s =
        String.isSubstring "?case" s orelse String.isSubstring "?thesis" s
   in exists (fn tok =>
        member (op =) [Token.Var, Token.String, Token.Alt_String, Token.Cartouche]
                      (Token.kind_of tok)
        andalso check (Token.unparse tok)) tokens
  end


fun raw_collect _ elaborated_version show_first pp_names stat commands =
  let open Minilang_Aux

      val is_first = Unsynchronized.ref (not show_first)
      fun pass _ ret [] = ret
        | pass stat ret ((tr, Command_Span.Span (Command_Span.Command_Span (this_cmd, pos), tokens)) :: cmds) =
            let val stat' =
                      case try (Timeout.apply single_cmd_timeout (Toplevel.transition false tr)) stat
                        of SOME (x, NONE) => x
                         | SOME (_, SOME _) => raise Partial_Ret ret
                         | NONE => raise Partial_Ret ret

                val end_pos = end_pos_of 0 (Token.pos_of (last tokens))
                fun pos_next ((_, Command_Span.Span (Command_Span.Command_Span (_, pos), _)) :: _) = pos
                  | pos_next (_ :: cmds) = pos_next cmds
                  | pos_next [] = raise Partial_Ret ret

                fun show_all_goals' i () = show_all_goals (this_cmd, end_pos, Newline i) stat pp_names
                fun show_this' loc () = show_this (this_cmd, end_pos, loc) stat pp_names
                fun annotate_facts_in_cmd' () = annotate_facts_in_cmd stat this_cmd tokens pp_names
                fun show_calculation' () = show_calculation (this_cmd, end_pos, Newline 0) stat pp_names

                val gen_ret =
                    case this_cmd
                      of "proof" => show_all_goals' 1
                       | "next"  => show_all_goals' 1
                       | "obtain" => show_all_goals' 1
                       | "consider" => show_all_goals' 1
                       | "unfolding" => show_all_goals' 0
                       | "apply" => if elaborated_version
                                    then K []
                                    else show_all_goals' 0
                       | "}" => show_this' (Newline 0)
                       | "case" => show_this' (Newline 0)
                       | "assume" => (fn _ => show_this (this_cmd, end_pos, Newline 0) stat (map (K "type_sort") pp_names))
                       | "using" => annotate_facts_in_cmd'
                       | "from"  => annotate_facts_in_cmd'
                       | "with"  => annotate_facts_in_cmd'
                       | "note"  => annotate_facts_in_cmd'
                       | "also"  => show_calculation'
                       | "finally" => show_calculation'
                       | "show" => if has_macro tokens
                                   then show_all_goals' 1
                                   else K []
                       | "thus" => if has_macro tokens
                                   then show_all_goals' 1
                                   else K []
                       | _ => K []

                val ret' = gen_ret () @ ret
(*
                val stat' =
                      case try (Timeout.apply single_cmd_timeout (Toplevel.transition false tr)) stat
                        of SOME (x, NONE) => x
                         | SOME (_, SOME _) => raise Partial_Ret ret
                         | NONE => raise Partial_Ret ret
                fun pos_next ((_, Command_Span.Span (Command_Span.Command_Span (_, pos), _)) :: _) = pos
                  | pos_next (_ :: cmds) = pos_next cmds
                  | pos_next [] = raise Partial_Ret ret

                

                val ret' =
                    if not (!is_first) andalso
                       not (member (op =) ["have", "hence", "consider", "obtain"] cmd) andalso
                       Toplevel.is_proof stat' andalso
                       can Proof.assert_backward (Toplevel.proof_of stat')
                    then let val state = Toplevel.proof_of stat'
                             val ctxt = Proof.context_of state
                             val goals = Thm.prems_of (#goal (Proof.goal state))
                             val pos = pos_next cmds
                      in if null goals then ret else 
                        (pos, map (fn (pp_name, string_of_term) =>
                        let val s =
                           (* if first_goal_only
                              then String.concat ["(*goal: \"", string_of_term ctxt (hd goals), "\" *)"]
                              else *) String.concat (
                              case goals
                                of [goal] => ["(*goal: \"", string_of_term ctxt goal, "\" *)"]
                                 | _ => "(*goals:\n" ::
                                    flat (map_index (fn (i, goal) =>
                                      [string_of_int (i+1), ". \"", string_of_term ctxt goal, "\"\n"]) goals)
                                    @ ["*)"])
                         in (pp_name, s)
                        end ) pp_names
                      ) :: ret
                      end
                    else ret *)
             in pass stat' ret' cmds
            end
        | pass stat ret (_ :: cmds) = pass stat ret cmds
   in pass stat [] commands
   |> rev
  end

(*
fun raw_collect _ first_goal_only show_first pp_names stat commands =
  let open Minilang_Aux
      val is_first = Unsynchronized.ref (not show_first)
      fun pass _ ret [] = ret
        | pass stat ret ((tr, Command_Span.Span (Command_Span.Command_Span (cmd, _), _)) :: cmds) =
            let val stat' =
                      case try (Timeout.apply single_cmd_timeout (Toplevel.transition false tr)) stat
                        of SOME (x, NONE) => x
                         | SOME (_, SOME _) => raise Partial_Ret ret
                         | NONE => raise Partial_Ret ret
                fun pos_next ((_, Command_Span.Span (Command_Span.Command_Span (_, pos), _)) :: _) = pos
                  | pos_next (_ :: cmds) = pos_next cmds
                  | pos_next [] = raise Partial_Ret ret

                

                val ret' =
                    if not (!is_first) andalso
                       not (member (op =) ["have", "hence", "consider", "obtain"] cmd) andalso
                       Toplevel.is_proof stat' andalso
                       can Proof.assert_backward (Toplevel.proof_of stat')
                    then let val state = Toplevel.proof_of stat'
                             val ctxt = Proof.context_of state
                             val goals = Thm.prems_of (#goal (Proof.goal state))
                             val pos = pos_next cmds
                      in if null goals then ret else 
                        (pos, map (fn (pp_name, string_of_term) =>
                        let val s =
                           (* if first_goal_only
                              then String.concat ["(*goal: \"", string_of_term ctxt (hd goals), "\" *)"]
                              else *) String.concat (
                              case goals
                                of [goal] => ["(*goal: \"", string_of_term ctxt goal, "\" *)"]
                                 | _ => "(*goals:\n" ::
                                    flat (map_index (fn (i, goal) =>
                                      [string_of_int (i+1), ". \"", string_of_term ctxt goal, "\"\n"]) goals)
                                    @ ["*)"])
                         in (pp_name, s)
                        end ) pp_names
                      ) :: ret
                      end
                    else ret
             in is_first := false
              ; pass stat' ret' cmds
            end
        | pass stat ret (_ :: cmds) = pass stat ret cmds
   in pass stat [] commands
   |> rev
  end
*)

fun parse_cmds thy src =
  let val pos = Position.make {
                  line=1, offset=1, end_offset=0,
                  props= { label = "", file = "#Extraction", id="" }
                }
      val symbs = Symbol_Pos.explode (src, pos)
      val keywords = Thy_Header.get_keywords thy
                  |> Keyword.add_major_keywords ["mqed", "mproof"]
      fun fix_cmds (_, cmd as Command_Span.Span (Command_Span.Command_Span ("mproof", pos), _))
            = ( MinLang_Translator.mproof_transition Toplevel.empty
                  |> Toplevel.position pos
                  |> Toplevel.name "mproof"
              , cmd)
        | fix_cmds (_, cmd as Command_Span.Span (Command_Span.Command_Span ("mqed", pos), _))
            = ( MinLang_Translator.mqed_transition Toplevel.empty
                  |> Toplevel.position pos
                  |> Toplevel.name "mqed"
              , cmd)
        | fix_cmds x = x
      val cmds = Token.tokenize keywords {strict = false} symbs
              |> Outer_Syntax.parse_spans
              |> map (` (Command_Span.content #> Outer_Syntax.parse_span thy (K thy)))
              |> filter_out (Toplevel.is_ignored o fst)
              |> map fix_cmds
   in cmds
  end

val translation_timeout = Time.fromSeconds 300

fun collect (reporter:reporter) show_first pp_names stat commands =
  let (* val stat' = stat *)
      fun try_raw_collect flag stat commands =
          \<^try>\<open>raw_collect (#debug reporter) flag show_first pp_names stat commands
            catch Partial_Ret ret => ret
                | E => ( #error reporter (Runtime.exn_message_list E); [] )\<close>
      val ret1 = try_raw_collect false stat commands
      val ret2 = case try (Timeout.apply translation_timeout (fn () =>
                    let val _ = #debug reporter ["start elaboration"]
                        val tokens = map (filter Token.is_proper o Command_Span.content o snd) commands
                        val ast' = MinLang_Translator.elaborate (Unsynchronized.ref []) (stat, tokens)
                        val elaborated = MinLang_Translator.print_ast false ast'
                        val thy = Toplevel.theory_of stat
                        val cmds' = parse_cmds thy elaborated
                        val _ = Timeout.apply (Time.fromSeconds (60 + 20 * length cmds'))
                                              (fold (Toplevel.command_exception false o fst) cmds') stat
                     in #debug reporter ["Elaboration succeeds", elaborated]
                      ; (elaborated, cmds')
                    end)) ()
                of SOME (src, cmds') => SOME (src, try_raw_collect true stat cmds')
                 | NONE => NONE
   in (ret1, ret2)
(* case try (Timeout.apply translation_timeout (fn () =>
        let val _ = #debug reporter ["start elaboration"]
            val tokens = map (filter Token.is_proper o Command_Span.content o snd) commands
            val ast' = MinLang_Translator.elaborate (Unsynchronized.ref []) (stat, tokens)
            val elaborated = MinLang_Translator.print_ast ast'
            val thy = Toplevel.theory_of stat'
            val cmds' = parse_cmds thy elaborated
            val _ = Timeout.apply (Time.fromSeconds (60 + 20 * length cmds'))
                                  (fold (Toplevel.command_exception false o fst) cmds') stat'
         in #debug reporter ["Elaboration succeeds", elaborated]
          ; cmds'
        end)) ()
    of SOME cmds' =>
          \<^try>\<open>raw_collect (#debug reporter) pp_names stat' cmds'
            catch Partial_Ret ret => ret
             | E => (#error reporter (Runtime.exn_message_list E); []) \<close>
     | NONE => try_raw_collect stat commands *)
  end

fun is_goal_command (Command_Span.Command_Span (name, _)) =
      member (op =) ["lemma", "theorem", "schematic_goal", "proposition", "corollary",
                     "interpretation", "global_interpretation", "sublocale"] name
  | is_goal_command _ = false
fun is_goal_command' (Command_Span.Span (k, _)) = is_goal_command k

fun REPL_plugin (reporter : reporter) pp_names : REPL.collector =
  let val pp_names' = map (fn name =>
              (name, REPL_Serialize.string_of_term name o Context.Proof)) pp_names
   in fn _ => fn {current_command, state, remaining} =>
  let val pos = case current_command of Command_Span.Span (Command_Span.Command_Span (_, pos), _) => pos
                   | _ => Position.none
      val show_first =
            case current_command
              of Command_Span.Span (Command_Span.Command_Span ("show", _), _) => true
               | _ => false
   in \<^try>\<open>
    if is_goal_command' current_command andalso
        Toplevel.is_proof state andalso
         let val st = #goal (Proof.raw_goal (Toplevel.proof_of state))
          in not (Thm.is_dummy st) andalso not (Thm.no_prems st)
         end
    then if #start reporter pos
      then let
          val proof = Minilang_Aux.extract_proof remaining
          val data = collect reporter show_first pp_names' state proof
       in #report reporter pos data
        ; (NONE, NONE)
      end
      else (NONE, NONE)
    else (NONE, NONE)
    catch E => (#error reporter (Runtime.exn_message_list E); (NONE, NONE))\<close>
  end
  end

fun init_translator pp_names reporter = (
      REPL.init_repler NONE
    ; REPL.set_register_thy false
    ; REPL.register_plugin ("Pretrian_Extraction", REPL_plugin reporter pp_names) )

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
      val (path, pp_names) = read cin (unpackPair (unpackString, unpackList unpackString))

      val path' = Path.explode path
      val src = File.read path'
      val (_, tr) = REPL_Aux.column_of_pos src
      val reporter = socket_reporter tr (cin,cout)

   in init_translator pp_names reporter
    ; \<^try>\<open>extraction_file path
        catch Bad_Source errs => #error reporter errs \<close>
    ; doPack packInt 5 cout
    ; BinIO.StreamIO.flushOut cout
    ; toplevel
  end

val _ = REPL_Server.register_app "Pretrain_Extraction" REPL_App


end