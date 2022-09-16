theory NotPhase
  imports
    Common
begin

section \<open>Optimizations for Not Nodes\<close>

phase NotNode
  terminating size
begin

(* Word level proofs *)
lemma bin_not_cancel:
 "bin[\<not>(\<not>(e))] = bin[e]"
  by auto

(* Value level proofs *)
lemma val_not_cancel:
  assumes "val[~(new_int b v)] \<noteq> UndefVal"
  shows "val[~(~(new_int b v))] = (new_int b v)"
   using bin_not_cancel
  by (simp add: take_bit_not_take_bit)

(* Exp level proofs *)
lemma exp_not_cancel:
  shows "exp[~(~a)] \<ge> exp[a]" 
   using val_not_cancel apply auto 
  by (metis eval_unused_bits_zero intval_logic_negation.cases intval_not.simps(1) 
      intval_not.simps(2) intval_not.simps(3) intval_not.simps(4) new_int.simps)


text \<open>Optimisations\<close>
optimization NotCancel: "exp[~(~a)] \<longmapsto> a"
  by (metis exp_not_cancel)

end (* End of NotPhase *)

end (* End of file *)
