theory Premise_Extraction
  imports Minilang_Translator.MS_Translator Isa_REPL.Isa_REPL
begin


ML_file "ac_shuffle.ML"

setup \<open>Context.theory_map (
     Theorem_Extraction.install_AC (Context.Proof \<^context>)
  #> Theorem_Extraction.remove_AC [@{const_name HOL.eq}]
)\<close>

ML_file "sledgehammer.ML"
ML_file "extraction.ML"

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

end