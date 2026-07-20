theory AoA_Learning_Toy
  imports Complex_Main
begin

(* Tiny target theory for smoke-testing the AoA-learning harness end-to-end on a
   Minilang_AoA-based heap (no MathBench corpus needed). Each lemma below is
   replayed from source; at each goal the harness runs the AoA agent with a
   LearningTask (the goal + this original Isar proof), then lets the original
   proof close the goal. *)

lemma toy_add_comm: "(a::nat) + b = b + a"
  by simp

lemma toy_sq_nonneg: "(0::int) \<le> x * x"
  by simp

end
