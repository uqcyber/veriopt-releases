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
  assumes "e \<noteq> UndefVal \<and> (intval_not e) \<noteq> UndefVal \<and> intval_not (intval_not e) \<noteq> UndefVal"
  shows "intval_not (intval_not e) = e"
  using bin_not_cancel
  by (metis (no_types, lifting) assms intval_not.elims intval_not.simps(1) intval_not.simps(2))

(* Expr level proofs *)
lemma exp_not_cancel:
  shows "UnaryExpr UnaryNot (UnaryExpr UnaryNot a) \<ge> exp[a]"
   apply simp using val_not_cancel
  by (metis UnaryExprE intval_not.simps(3) unary_eval.simps(3))

(* Optimisations *)
optimization not_cancel: "UnaryExpr UnaryNot (UnaryExpr UnaryNot a) \<longmapsto> a"
   apply simp_all
   apply auto
 by (metis intval_not.simps(3) val_not_cancel)

end (* End of NotPhase *)

end (* End of file *)
