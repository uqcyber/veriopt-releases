theory XorPhase
  imports
    Common
begin

section \<open>Optimizations for Xor Nodes\<close>

phase XorNode
  terminating size
begin

(* Word level proofs *)
lemma bin_xor_self_is_false:
 "bin[x \<oplus> x] = 0"
  by simp

lemma bin_xor_commute:
 "bin[x \<oplus> y] = bin[y \<oplus> x]"
  by (simp add: xor.commute)

lemma bin_eliminate_redundant_false:
 "bin[x \<oplus> 0] = bin[x]"
  by simp


(* Value level proofs *)
lemma val_xor_self_is_false:
  assumes "val[x \<oplus> x] \<noteq> UndefVal"
  shows "val_to_bool (val[x \<oplus> x]) = False"
  using assms by (cases x; auto)

lemma val_xor_self_is_false_2:
  assumes "(val[x \<oplus> x]) \<noteq> UndefVal \<and> x = IntVal 32 v" 
  shows "val[x \<oplus> x] = bool_to_val False"
  using assms by (cases x; auto)

(* Not sure if I need this; Optimization uses ConstantExpr False which is IntVal32 0 *)
lemma val_xor_self_is_false_3:
  assumes "val[x \<oplus> x] \<noteq> UndefVal \<and> x = IntVal 64 v" 
  shows "val[x \<oplus> x] = IntVal 64 0"
  using assms by (cases x; auto)

lemma val_xor_commute:
   "val[x \<oplus> y] = val[y \<oplus> x]"
   apply (cases x; cases y; auto)
  by (simp add: xor.commute)+

lemma val_eliminate_redundant_false:
  assumes "x = new_int b v"
  assumes "val[x \<oplus> (bool_to_val False)] \<noteq> UndefVal"
  shows "val[x \<oplus> (bool_to_val False)] = x"
  using assms apply (cases x; auto)
  by meson


(* Borrowed from ConditionalPhase *)
definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"


(* Expression level proofs *)

(* Unsure about this one *)
lemma exp_xor_self_is_false:
 assumes "wf_stamp x \<and> stamp_expr x = default_stamp" 
 shows "exp[x \<oplus> x] \<ge> exp[false]" 
  using assms apply auto unfolding wf_stamp_def
  using IntVal0 Value.inject(1) bool_to_val.simps(2) constantAsStamp.simps(1) evalDet int_signed_value_bounds new_int.simps unfold_const val_xor_self_is_false_2 valid_int valid_stamp.simps(1) valid_value.simps(1)
  by (smt (z3) validDefIntConst)

(* Optimisations *)
(* Not sure about the conditions on this one. *)
optimization xor_self_is_false: "(x \<oplus> x) \<longmapsto> false when 
                      (wf_stamp x \<and> stamp_expr x = default_stamp)"
   apply auto[1] 
   apply (simp add: Suc_lessI one_is_add) using exp_xor_self_is_false
  by auto 

optimization XorShiftConstantRight: "((const x) \<oplus> y) \<longmapsto> y \<oplus> (const x) when \<not>(is_ConstantExpr y)"
   unfolding le_expr_def using val_xor_commute size_non_const 
   apply simp apply auto 
  sorry

optimization EliminateRedundantFalse: "(x \<oplus> false) \<longmapsto> x"
    using val_eliminate_redundant_false apply auto sorry (*
   by (metis)*)


optimization opt_mask_out_rhs: "(x \<oplus> const y) \<longmapsto> UnaryExpr UnaryNot x
                                 when ((stamp_expr (x) = IntegerStamp bits l h))  
"
    unfolding le_expr_def apply auto 
  sorry

end (* End of XorPhase *)

end (* End of file *)
