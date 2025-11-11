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

declare [[ML_print_depth = 100]]


end