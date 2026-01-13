structure Goal_state_Extraction = struct

type goal_pos = Position.T
type pp_name = REPL_Serialize.pp_name
datatype location = Inline  (*add a space, then insert the annotation*)
                  | Newline of int (*insert a new line, and then the annotation*)
type target_cmd = string
type annotation = Position.T (*proof begin*) * Position.T (*proof end*) * (pp_name * string (*code*)) list
type reporter = {
        start: goal_pos -> bool,
        report: goal_pos -> annotation -> unit,
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

fun socket_reporter (pos_tr, tr_offset) (cin,cout) : reporter =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      val tr_pos_packer = pos_packer o pos_tr
      fun offset_packer pos = packInt (
            case Position.offset_of pos of SOME p => tr_offset p
                                         | NONE => ~1)
      val pack_annotation = packTuple3 (offset_packer, offset_packer, packPairList (packString, packString))
   in { start = (fn pos => (
            send cout (packPair (packInt, tr_pos_packer)) (0, pos)
          ; read cin unpackBool))
      , report = (fn pos => fn annotations =>
            send cout
                 (packTuple3 (packInt, tr_pos_packer, pack_annotation))
                 (1, pos, annotations))
      , debug = (fn msgs => send cout (packPair (packInt, packList packString)) (2, map REPL.trim_makrup msgs) )
      , error = (fn msgs => send cout (packPair (packInt, packList packString)) (3, map REPL.trim_makrup msgs) )
      }
  end

fun parse_cmds thy src =
  let val pos = Position.make {
                  line=1, offset=1, end_offset=0,
                  props= { label = "", file = "#Extraction", id="" }
                }
      val symbs = Symbol_Pos.explode (src, pos)
      val keywords = Thy_Header.get_keywords thy
      val cmds = Token.tokenize keywords {strict = false} symbs
              |> Outer_Syntax.parse_spans
              |> map (` (Command_Span.content #> Outer_Syntax.parse_span thy (K thy)))
              |> filter_out (Toplevel.is_ignored o fst)
   in cmds
  end

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

val translation_timeout = Time.fromSeconds 300

exception Known_Error of string

fun collect (reporter:reporter) pp_names stat commands =
  let (* val stat' = stat *)
      val _ = #debug reporter ["start elaboration"]
      val tokens = map (filter Token.is_proper o Command_Span.content o snd) commands
      val ast' = MinLang_Translator.elaborate_tactic (stat, tokens)
      val _ = #debug reporter ["end elaboration"]
      val kws = Thy_Header.get_keywords (Toplevel.theory_of stat)
      val codes = map (fn pp => (pp, MinLang_Translator.print_ast (SOME pp) (SOME kws) ast')) pp_names

(*
      val thy = Toplevel.theory_of stat
      val cmds' = parse_cmds thy (snd (hd codes))
      val _ = Timeout.apply (Time.fromSeconds (60 + 20 * length cmds'))
                                              (fold (Toplevel.command_exception false o fst) cmds') stat
              handle Timeout.TIMEOUT _ => raise Known_Error "Timeout in Evaluating Annotated Code"
*)
      val all_toks = maps (fn (_, Command_Span.Span (_, toks)) => toks) commands
      val begin_pos = Token.pos_of (hd all_toks)
      val end_pos   = Token.pos_of (last all_toks) |> end_pos_of 0
   in (begin_pos, end_pos, codes)
  end

fun is_goal_command (Command_Span.Command_Span (name, _)) =
      member (op =) ["lemma", "theorem", "schematic_goal", "proposition", "corollary",
                     "interpretation", "global_interpretation", "sublocale"] name
  | is_goal_command _ = false
fun is_goal_command' (Command_Span.Span (k, _)) = is_goal_command k

fun REPL_plugin (reporter : reporter) pp_names : REPL.collector = fn _ =>
  fn {current_command, state, remaining} =>
  let val pos = case current_command of Command_Span.Span (Command_Span.Command_Span (_, pos), _) => pos
                   | _ => Position.none
   in \<^try>\<open>
    if is_goal_command' current_command andalso
        Toplevel.is_proof state andalso
         let val st = #goal (Proof.raw_goal (Toplevel.proof_of state))
          in not (Thm.is_dummy st) andalso not (Thm.no_prems st)
         end
    then if #start reporter pos
      then let
          val proof = Minilang_Aux.extract_proof remaining
          val data = collect reporter pp_names state proof
       in #report reporter pos data
        ; (NONE, NONE)
      end
      else (NONE, NONE)
    else (NONE, NONE)
    catch E => (#error reporter (Runtime.exn_message_list E); (NONE, NONE))\<close>
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
      val tr_offset = REPL_Aux.ascii_offset_of_pos src
      val reporter = socket_reporter (tr, tr_offset) (cin,cout)

   in init_translator pp_names reporter
    ; \<^try>\<open>extraction_file path
        catch Bad_Source errs => #error reporter errs \<close>
    ; doPack packInt 5 cout
    ; BinIO.StreamIO.flushOut cout
    ; toplevel
  end

val _ = REPL_Server.register_app "Pretrain_Extraction2" REPL_App


end