theory XorPhase
  imports
    Common
begin

section \<open>Optimizations for Xor Nodes\<close>

phase XorPhase
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
  assumes "(val[x \<oplus> x]) \<noteq> UndefVal \<and> is_IntVal32 x" 
  shows "val[x \<oplus> x] = bool_to_val False"
  using assms by (cases x; auto)

(* Not sure if I need this; Optimization uses ConstantExpr False which is IntVal32 0 *)
lemma val_xor_self_is_false_3:
  assumes "val[x \<oplus> x] \<noteq> UndefVal \<and> is_IntVal64 x" 
  shows "val[x \<oplus> x] = IntVal64 0"
  using assms by (cases x; auto)

lemma val_xor_commute:
   "val[x \<oplus> y] = val[y \<oplus> x]"
   apply (cases x; cases y; auto)
  by (simp add: xor.commute)+

lemma val_eliminate_redundant_false:
  assumes "val[x \<oplus> (bool_to_val False)] \<noteq> UndefVal"
  shows "val[x \<oplus> (bool_to_val False)] = x"
  using assms by (cases x; auto)


(* Borrowed from ConditionalPhase *)
definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"


(* Expression level proofs *)

(* Unsure about this one *)
lemma exp_xor_self_is_false:
 assumes "wf_stamp x \<and> stamp_expr x = default_stamp" 
 shows "exp[x \<oplus> x] \<ge> exp[false]" 
  using assms val_xor_self_is_false_2 wf_stamp_def apply (cases x; auto) 
  using bin_xor_self_is_false
  apply (smt (verit, ccfv_threshold) evalDet intval_xor.simps(1) unfold_const32 unfold_unary 
         valid_int32)
  apply (smt (verit, best) BinaryExpr evalDet is_IntVal32_def unfold_const32 valid_int32)
  apply (smt (verit, best) ConditionalExpr evalDet is_IntVal32_def unfold_const32 valid_int32)
  apply (metis Value.disc(2) unfold_const32 valid_int32)
 by (metis  is_IntVal32_def unfold_const32 valid_int32)+


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
    using val_eliminate_redundant_false apply auto 
   by (metis)


optimization opt_mask_out_rhs: "(x \<oplus> const y) \<longmapsto> UnaryExpr UnaryNot x
                                 when ((stamp_expr (x) = IntegerStamp bits l h))  
"
    unfolding le_expr_def apply auto 
  sorry

end (* End of XorPhase *)

end (* End of file *)
