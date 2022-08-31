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

(* Expr level proofs *)
lemma exp_not_cancel:
  shows "exp[~(~a)] \<ge> exp[a]"
   apply simp using val_not_cancel sorry (*
  by (metis UnaryExprE unary_eval.simps(3))*)

(* Optimisations *)
optimization not_cancel: "exp[~(~a)] \<longmapsto> a"
  by (metis exp_not_cancel)

end (* End of NotPhase *)

end (* End of file *)
