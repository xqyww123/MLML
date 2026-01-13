theory Pretrain_Extraction
  imports Minilang_Translator.MS_Translator
begin

(* ML_file \<open>extraction.ML\<close> *)
ML_file \<open>extraction2.ML\<close>

(*
ML \<open>val kwds = Thy_Header.get_keywords @{theory}\<close>
ML \<open>
Token.tokenize kwds {strict=false} (Input.source_explode (Input.string "show \" ?thesis \""))
\<close>

ML \<open>
val contain_macro = exists (fn tok =>
      let val s = Token.unparse tok
       in String.isSubstring "?thesis" s orelse
          String.isSubstring "?case" s
      end )
\<close>

ML \<open>String.isSubstring "aa" "aaaa"\<close>

ML \<open>val pos = Position.make {
                  line=1, offset=1, end_offset=1,
                  props= { label = "",
                           file = "#REPL",
                           id="" }
                }\<close>
ML \<open>fun end_pos_of shift pos =
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
      val used = Token.pos_of (nth toks (length toks - length toks' - 1))
   in ((ret, end_pos_of 0 used), toks')
  end
\<close>
ML \<open>fun range scan = (Scan.ahead Parse.not_eof >> (Token.range_of o single)) -- scan >> Library.swap;\<close>

lemma True
proof auto
qed
  ML_val \<open> 
Token.tokenize (Thy_Header.get_keywords @{theory}) {strict=false} (Symbol_Pos.explode (
  "text \<open>sad\<close>", pos))
|> Outer_Syntax.parse_span @{theory} (fn _ => error "aa")
|> (fn tr =>
  let val state = Toplevel.make_state (SOME @{theory})
      val tr' = Toplevel.theory_to_proof (K (Toplevel.proof_of @{Isar.state})) Toplevel.empty
   in Toplevel.command_exception false tr' state
   |> Toplevel.command_exception false tr
   |> Toplevel.proof_of
   |> Proof.goal
  end )
\<close>

ML \<open> 

Token.tokenize (Thy_Header.get_keywords @{theory}) {strict=false} (Symbol_Pos.explode (
  "show ?cases", pos))
|> Outer_Syntax.parse_spans
|> (fn Command_Span.Span (_, x)  :: _ => x)
|> filter Token.is_proper
|> tl
|> map Token.kind_of
\<close>


lemma " x = (2::nat)"
proof (cases x)
  ML_val \<open>Toplevel.proof_of @{Isar.state} |> Proof.goal |> #goal\<close>
  case 0
  fix a :: int
  { assume "x = 1" and "x = 2" hence "x + x = 2" by auto }
  also
  thm calculation
  ML_val \<open>Proof_Context.get_thms (Toplevel.context_of @{Isar.state}) "calculation"\<close>
  ML_val \<open>Toplevel.proof_of @{Isar.state} |> Proof.the_fact\<close>
  then show ?thesis sorry
next
  
  then show ?thesis sorry
qed

ML \<open>@{thm [[]]} |> Thm.prop_of\<close>

(*
Show all goals:
  proof, next,
  obtain, consider (*good or not?*)
  unfolding,
  tactics (turned off for elaborated proofs)

  TODO!
  interpretation, global_interpretation, subgoal

Special:
  assume - show full typed sorted expression
Show facts:
  using from with note a b c
  using from with note a (*\<open>...\<close>*) b (*\<open>...\<close>*) c (*\<open>...\<close>*)

Show this:
  }
  case
  (*facts:
    \<open>...\<close>
    \<open>...\<close>*)
Show calculation:
  also finally
  (*calculation: \<open>...\<close>*)
Show goal (if contains ?thesis or ?)
  show thus
*)

*)

end