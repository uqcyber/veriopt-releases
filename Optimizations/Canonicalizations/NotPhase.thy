theory NotPhase
  imports
    Common
begin

section \<open>Optimizations for Not Nodes\<close>

phase NotPhase
  terminating size
begin

(* Word level proofs *)
lemma bin_not_cancel:
 "bin[\<not>(\<not>(e))] = bin[e]"
  by auto

(* Value level proofs *)
lemma val_not_cancel:
  assumes "val[~e] \<noteq> UndefVal"
  shows "val[~(~e)] = e"
   using bin_not_cancel 
  by (metis (no_types, lifting) assms intval_not.elims intval_not.simps(1) intval_not.simps(2))

(* Expr level proofs *)
lemma exp_not_cancel:
  shows "exp[~(~a)] \<ge> exp[a]"
   apply simp using val_not_cancel
  by (metis UnaryExprE unary_eval.simps(3))

(* Optimisations *)
optimization not_cancel: "exp[~(~a)] \<longmapsto> a"
  by (metis exp_not_cancel)

end (* End of NotPhase *)

end (* End of file *)
