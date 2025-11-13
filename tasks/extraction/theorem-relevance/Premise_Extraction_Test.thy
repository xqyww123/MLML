theory Premise_Extraction_Test
  imports Premise_Extraction
begin 
    
             
ML \<open>Theorem_Extraction.init_translator Theorem_Extraction.interactive_reporter\<close>
      
(* ML \<open>Theorem_Extraction.extraction_file "/home/qiyuan/Current/MLML/contrib/Isabelle2024/src/HOL/Library/Sublist.thy"\<close> *)
ML \<open>Theorem_Extraction.extraction_file "/home/qiyuan/Current/MLML/contrib/afp-2025-02-12/thys/MHComputation/MHComputation.thy"\<close>
  
thm append.simps(1)

ML \<open>Theorem_Extraction.ac_shuffle 30 (Context.Proof \<^context>)
    @{term \<open>(xs::'a::type list) = [] \<Longrightarrow> prefix xs ((y::'a::type) # (ys::'a::type list)) = (xs = [] \<or> (\<exists>zs::'a::type list. xs = y # zs \<and> prefix
  zs ys))\<close>}
  |> map (Thm.cterm_of \<^context>)\<close>

end