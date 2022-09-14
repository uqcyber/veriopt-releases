theory SignedRemPhase
  imports
    Common
begin

section \<open>Optimizations for SignedRem Nodes\<close>

phase SignedRemNode
  terminating size
begin


lemma val_remainder_one:
  assumes "intval_mod x (IntVal 32 1) \<noteq> UndefVal"
  shows "intval_mod x (IntVal 32 1) = IntVal 32 0"
  using assms apply (cases x; auto) sorry
  
value "word_of_int (sint (x2::32 word) smod 1)"

end (* End of SignedRedPhase *)

end (* End of file *)