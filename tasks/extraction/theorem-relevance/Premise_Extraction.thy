theory Premise_Extraction
  imports Minilang_Translator.MS_Translator Isa_REPL.Isa_REPL
begin

(* declare [[ML_debugger, ML_print_depth = 1000, ML_exception_trace, ML_exception_debugger]] *)

ML_file "ac_shuffle.ML"

setup \<open>Context.theory_map (
     Theorem_Extraction.install_AC (Context.Proof \<^context>)
  #> Theorem_Extraction.remove_AC [@{const_name HOL.eq}]
)\<close>

ML_file "context_info.ML"
ML_file "sledgehammer.ML"
ML_file "extraction.ML"


(*
ML \<open>fun f () = (\<^try>\<open>Syntax.read_term \<^context> "asdqq s!" catch e => error "OK"\<close>)\<close>

term \<open>Par_Exn\<close>

term 12
ML \<open>f ()\<close>
*)

(*

locale L0 =
  fixes N :: \<open>'a :: times\<close>
  assumes AX0: "N * N = N"

locale L1 = L0 +
  fixes P :: \<open>'a :: plus\<close> ("AA")
    assumes A: "P = P"

locale L2 = L1 0 1 +
  fixes Q :: bool
  assumes B: "Q"
begin
thm AX0

definition "kkk = Q"

thm L2_def
thm L1_def
thm L1_axioms_def

end

ML \<open>
let val ctxt0 = Proof_Context.init_global \<^theory>
    val ctxt = Target_Context.context_begin_named_cmd [] ("Premise_Extraction.L2", Position.none) \<^theory>
 in Assumption.local_prems_of ctxt ctxt0
  |> map (Simplifier.rewrite_rule ctxt @{thms L2_def L2_axioms_def } )
    (* Variable.constraints_of ctxt *)
end
\<close>


ML \<open>
let val ctxt = Proof_Context.init_global \<^theory>
    
    val ctxt'= Locale.activate_declarations ("Premise_Extraction.L2", Morphism.identity) ctxt
 in Assumption.local_assms_of ctxt' ctxt
end
\<close>



fun fact where
  "fact (0::nat) = 1" |
  "fact (Suc N) = N * fact N"

thm fact.simps 

ML \<open>Thy_Info.get_names () |> List.app writeln\<close>



term store
ML \<open>Record.the_info \<^theory> "A_Aodv.state" |> #args\<close>
thm state.simps
thm store_def
thm \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton_simps(1)
term PAodv
ML \<open>Record.the_info \<^theory> \<close>

thm non_trivial_neg

thm non_trivial_neg
  
typ \<open>'a :: monoid_add\<close>
ML \<open>Locale.axioms_of \<^theory> "DBM.class.time"\<close>
typ \<open>'a :: DBM.time\<close>
thm DBM.class.time_def
thm class.time_axioms_def
ML \<open>Locale.specification_of   \<^theory> "DBM.time"\<close>
 
  
ML \<open>      
let val buf = Context_Info.mk_buffer ()
    val info = Context_Info.defctxt_of \<^context> (Thm.prop_of @{thm non_trivial_neg})
 in List.app (Context_Info.put_defctxt \<^context> buf) info
  ; Context_Info.content_of buf |> tracing
end \<close>

term less_eq
term\<open>\<infinity>\<close>
thm dbm_lt.simps
thm dbm_lt.intros
 
ML \<open> 
let val buf = Context_Info.mk_buffer ()
    val info = Context_Info.defctxt_of \<^context> (Thm.prop_of @{thm dbm_not_lt_impl(1)})
 in List.app (Context_Info.put_defctxt \<^context> buf) info
  ; Context_Info.content_of buf |> tracing
end \<close>

term CHOICE

typ AWN.seqp
typ state
record 'a xx =
  aaa :: 'a
  bbb :: \<open>'a \<times> 'a\<close>
record yy = \<open>nat xx\<close> + zzz :: int
term zzz
term "Premise_Extraction.yy_ext"

datatype ('a,'b) test = is_Test: Test (tA1: nat) 'b | Test2 (tB1: \<open>'a \<times> 'b\<close>) | is_Test3: Test3


ML \<open>Record.the_info \<^theory> "Premise_Extraction.xx" |> #args\<close>
ML \<open>Record.the_info \<^theory> "Premise_Extraction.yy" |> #parent\<close>

consts AAA :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> ("_ CC _")
    
term LABEL   

ML \<open> 
let val buf = Context_Info.mk_buffer ()
 in Context_Info.put_ADT \<^context> buf
      (the (Ctr_Sugar.ctr_sugar_of \<^context> "Premise_Extraction.test"),
       BNF_Def.bnf_of \<^context> "Premise_Extraction.test")
  ; Context_Info.content_of buf |> tracing
end \<close>


ML \<open> 
let val buf = Context_Info.mk_buffer ()
 in Context_Info.put_record \<^context> buf "Premise_Extraction.xx"
  ; Context_Info.content_of buf
end \<close>

term Nil

ML \<open>
BNF_Def.bnf_of \<^context> "Premise_Extraction.test" |> the
|> BNF_Def.map_of_bnf
\<close>

term aaa
term rreqs


term plus

class semigroup_add = plus +
  assumes add_assoc: "(a + b) + c = a + (b + c)"
begin

sublocale add: semigroup plus
  by standard (fact add_assoc)

declare add.assoc [algebra_simps, algebra_split_simps, field_simps, field_split_simps]

end





context L2 begin

end

term L2.kkk
thm L2_def

ML \<open>Locale.params_of \<^theory> "Premise_Extraction.L2"\<close>
ML \<open>Locale.axioms_of \<^theory> "Premise_Extraction.L2"\<close>
ML \<open>(oo)\<close>
thm L2_def

term plus
ML \<open>Axclass.get_info \<^theory> "Groups.semigroup_add"\<close>
ML \<open>Sign.super_classes \<^theory> "Groups.semigroup_add"\<close>
ML \<open>Axclass.get_info \<^theory> "Groups.plus"\<close>

ML \<open>
fun show_const_syntax ctxt const_name =
    let
      val syn = Proof_Context.syntax_of ctxt
      val prtabs = Syntax.prtabs syn
      val tab = the_default Symtab.empty (AList.lookup (op =) prtabs "")
      val entries = Symtab.lookup_list tab const_name
    in
      if null entries then
        "No syntax for " ^ quote const_name
      else
        const_name ^ ": " ^ @{make_string} (entries)
    end
\<close>
ML \<open>show_const_syntax \<^context> \<^const_syntax>\<open>LABEL\<close> |> tracing\<close>
ML \<open>
let val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern \<^context>
    val term = (Const (\<^const_name>\<open>LABEL\<close>, dummyT) $ Term.dummy $ Term.dummy)
 in Syntax.string_of_term ctxt term
 |> tracing
end
\<close>

ML \<open>fun get_local_mixfixes (Local_Syntax.Syntax {mixfixes, ...}) = mixfixes\<close>
ML \<open>Locale .params_of \<^theory> "Groups.semigroup_add"\<close>
ML \<open>Locale.axioms_of \<^theory> "Groups.plus"\<close>
ML \<open>Locale.pretty_locale \<^theory> false "Groups.monoid_add"\<close>
ML \<open>Locale.pretty_locale \<^theory> false "Premise_Extraction.L2"\<close>
thm class.monoid_add_def

ML \<open>Locale.hyp_spec_of \<^theory> "Premise_Extraction.L1"\<close>
ML \<open>
let val dep = Locale.dest_dependencies [] \<^theory>
    val m = filter (fn {target,...} => target = "Premise_Extraction.L2") dep
  |> hd
  |> #morphism
    val m2 = filter (fn {target,...} => target = "Premise_Extraction.L1") dep
              |> hd |> #morphism
    val eles = Locale.hyp_spec_of \<^theory> "Premise_Extraction.L1"
            |> map (Element.transform_ctxt m)
    val mm = Morphism.compose m m2
 in (* Locale.params_of \<^theory> "Premise_Extraction.L0"
  |> map (Free o #1)
  |> map (Morphism.term mm) *)
  filter (fn {target,...} => target = "Premise_Extraction.L0")  dep
(*Locale.hyp_spec_of \<^theory> "Premise_Extraction.L0"
            |> map (Element.transform_ctxt mm)*)
end
\<close>

ML \<open>Locale.axioms_of \<^theory> "Premise_Extraction.L2"
      |> map (Simplifier.rewrite_rule \<^context> (Locale.get_unfolds \<^context>))\<close>
thm L2_def
thm L1_def
ML \<open>Locale.get_unfolds \<^context>\<close>
ML \<open>Locale.hyp_spec_of \<^theory> "Groups.monoid_add"\<close>
ML \<open>Locale.params_of \<^theory> "Premise_Extraction.L2"\<close>
ML \<open>Locale.params_of \<^theory> "Groups.semigroup_add"\<close>
ML \<open>Locale.specification_of \<^theory> "Groups.plus"\<close>
ML \<open>Name_Space.markup_table\<close>
ML \<open>
 local
  val code =
    "let \n\
    \  fun symb_to_string (Printer.Arg p) = \"_[\" ^ Int.toString p ^ \"]\"\n\
    \    | symb_to_string (Printer.TypArg p) = \"T[\" ^ Int.toString p ^ \"]\"\n\
    \    | symb_to_string (Printer.String (_, s)) = quote s\n\
    \    | symb_to_string (Printer.Break n) = \"break(\" ^ Int.toString n ^ \")\"\n\
    \    | symb_to_string (Printer.Block (_, symbs)) = \n\
    \        \"{\" ^ String.concatWith \" \" (map symb_to_string symbs) ^ \"}\"\n\
    \in symb_to_string end"
in
  (* 尝试动态编译 *)
  val symb_to_string_compiled =
    ML_Context.eval_source (ML_Compiler.verbose false ML_Compiler.flags)
      (Input.source false code (Position.none, Position.none))
      
end;

\<close>

ML \<open>
fun get_mixfixes (Local_Syntax.Syntax {mixfixes, ...}) = mixfixes
\<close>

ML \<open>
Locale.dest_dependencies [] \<^theory>
  |> map (fn {source, target, ...} => (source, target))
\<close>

ML \<open>
Named_Target.init
\<close>

ML \<open>

fun activate_all name thy activ_elem (marked, input) =
  let
    val {parameters = (_, params), spec = (asm, defs), ...} = the_locale thy name;
    val input' = input |>
      (not (null params) ?
        activ_elem (Element.Fixes (map (fn ((x, T), mx) => (Binding.name x, SOME T, mx)) params))) |>
      (* FIXME type parameters *)
      (case asm of SOME A => activ_elem (Assumes [(Binding.empty_atts, [(A, [])])]) | _ => I) |>
      (not (null defs) ?
        activ_elem (Element.Defines (map (fn def => (Binding.empty_atts, (def, []))) defs)));
    val activate = activate_notes activ_elem (Context.Theory thy) NONE;
  in
    roundup thy activate Morphism.identity (name, Morphism.identity) (marked, input')
  end

fun pretty_locale thy show_facts name =
  let
    val locale_ctxt = Locale.init name thy;
    fun cons_elem (elem as Element.Notes _) = show_facts ? cons elem
      | cons_elem (elem as Element.Lazy_Notes _) = show_facts ? cons elem
      | cons_elem elem = cons elem;
    val elems =
      Locale.activate_all name thy cons_elem (Symtab.empty, [])
      |> snd |> rev
      |> tap consolidate_notes
      |> map force_notes;
  in
    Pretty.block (Pretty.keyword1 "locale" :: Pretty.brk 1 :: pretty_name locale_ctxt name ::
      maps (fn elem => [Pretty.fbrk, Pretty.chunks (Element.pretty_ctxt locale_ctxt elem)]) elems)
  end;
\<close>

term plus

ML \<open>
fun show_const_syntax_raw ctxt const_name =
    let
      val syn = Proof_Context.syntax_of ctxt
      val prtabs = Syntax.prtabs syn
      val tab = the_default Symtab.empty (AList.lookup (op =) prtabs "")
      val entries = Symtab.lookup_list tab const_name
    in
       entries
    end
\<close>

ML \<open>Syntax.print_syntax\<close>

ML \<open>show_const_syntax_raw \<^context> \<^const_syntax>\<open>plus\<close> \<close>

ML \<open>
let val syn = Proof_Context.syntax_of @{context}
    val prtabs = Syntax.prtabs syn
    
 in Printer.get_infix prtabs \<^const_syntax>\<open>Groups.plus_class.plus\<close>
end \<close>

ML \<open>Syntax.string_of_term \<^context> (Const(\<^const_name>\<open>Groups.plus_class.plus\<close>, dummyT)) |> tracing\<close>
ML \<open>Name_Space.names_short\<close>
ML \<open>Name_Space.extern\<close>
ML \<open>Name_Space.extern \<^context> (Consts.space_of (Proof_Context.consts_of \<^context>)) "Groups.plus_class.plus"\<close>

ML "\<^const_syntax>\<open>Groups.plus_class.plus\<close> |> String.explode"

notation



term Test
term "is_Test"
term "tA1"

ML \<open>Ctr_Sugar.ctr_sugar_of \<^context> "Premise_Extraction.test" |> the |> #discs |> map (Thm.cterm_of \<^context>)\<close>
ML \<open>Ctr_Sugar.ctr_sugar_of \<^context> "Premise_Extraction.test" |> the |> #selss\<close>
ML \<open>Ctr_Sugar.ctr_sugar_of \<^context> "A_Aodv.state.state_ext" |> the |> #selss\<close>
ML \<open>Ctr_Sugar.ctr_sugar_of \<^context> "Premise_Extraction.xx.xx_ext" |> the |> #ctrs\<close>
ML \<open>String.substring ("0123456789", 3, 2)\<close>

term "Inter"

(*
ML \<open>fun mapx F (L,x) = (map F L, F x)\<close>
ML \<open>Theorem_Extraction.ac_shuffle_goal 30 (Context.Proof \<^context>)
    ([@{term \<open>(ys::'a::type list) @ [y::'a::type] = (xs::'a::type list) @
    (zs::'a::type list)\<close>},
    @{term \<open>prefix (xs::'a::type list) ((ys::'a::type list) @ [y::'a::type])\<close>}],
  @{term \<open>(xs::'a::type list) = (ys::'a::type list) @ [y::'a::type] \<or> prefix xs ys\<close>})
  |> map (mapx (Thm.cterm_of \<^context>)) \<close>


ML \<open>Theorem_Extraction.ac_shuffle_goal 100 (Context.Proof \<^context>)
    ([@{term \<open>(xs::'a::type list) = [] \<and> B\<close>},
      @{term \<open>AAA \<or> CCC\<close>}  ],
  @{term \<open>prefix xs ((y::'a::type) # (ys::'a::type list)) = (xs = [] \<or> (\<exists>zs::'a::type list. xs = y # zs \<and> prefix zs ys))\<close>})
  |> map (mapx (Thm.cterm_of \<^context>))
  |> length  \<close>

(*
declare [[ML_print_depth = 100]]
  
ML \<open>
  Theorem_Extraction.ac_shuffle 30 (Context.Proof \<^context>)
    @{term \<open>(A \<Longrightarrow> B \<Longrightarrow> \<forall>x y z. x + (1::nat) = y + z) \<Longrightarrow> C\<close>}
  |> map (Thm.cterm_of \<^context>)
\<close>

ML \<open>
fun print_term_ ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types true
              |> Config.put Printer.show_sorts true
     in Syntax.string_of_term ctxt'
     #> REPL.trim_makrup
    end\<close>
*)
*)
*)

end