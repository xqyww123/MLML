theory Premise_Extraction_Test
  imports Premise_Extraction
begin
 
   
ML \<open>Theorem_Extraction.init_translator Theorem_Extraction.interactive_reporter\<close>
   
ML \<open>Theorem_Extraction.extraction_file "/home/qiyuan/Current/MLML/contrib/Isabelle2024/src/HOL/Library/Sublist.thy"\<close>

thm append.simps(1)

end