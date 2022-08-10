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
  assumes "x \<noteq> UndefVal \<and> (intval_xor x x) \<noteq> UndefVal"
  shows "val_to_bool (intval_xor x x) = False"
  using assms apply (cases x; auto)
  done

lemma val_xor_self_is_false_2:
  assumes "x \<noteq> UndefVal \<and> (intval_xor x x) \<noteq> UndefVal \<and> is_IntVal32 x" 
  shows "intval_xor x x = bool_to_val False"
  using assms apply (cases x; auto)
  done

(* Not sure if I need this; Optimization uses ConstantExpr False which is IntVal32 0 *)
lemma val_xor_self_is_false_3:
  assumes "x \<noteq> UndefVal \<and> (intval_xor x x) \<noteq> UndefVal \<and> is_IntVal64 x" 
  shows "intval_xor x x = IntVal64 0"
  using assms apply (cases x; auto)
  done

lemma val_xor_commute:
   "val[x \<oplus> y] = val[y \<oplus> x]"
  apply (cases x; cases y; auto)
   apply (simp add: xor.commute)+
  done

lemma val_eliminate_redundant_false:
  assumes "x \<noteq> UndefVal \<and> (intval_xor x (bool_to_val False)) \<noteq> UndefVal"
  shows "val[intval_xor x (bool_to_val False)] = val[x]"
  apply (cases x; auto)
  using assms apply force+
  done


(* Borrowed from ConditionalPhase *)
definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"


(* Expression level proofs *)

(* Unsure about this one *)
lemma exp_xor_self_is_false:
 assumes "wf_stamp x \<and> stamp_expr x = default_stamp" 
 shows "exp[x \<oplus> x] \<ge> exp[false]" 
  using assms val_xor_self_is_false_2 wf_stamp_def 
   apply (cases x; auto) 
  using bin_xor_self_is_false
   apply (smt (verit, ccfv_threshold) evalDet intval_xor.simps(1) unfold_const32 unfold_unary 
               valid_int32)
   apply (smt (verit, best) BinaryExpr evalDet is_IntVal32_def unfold_const32 valid_int32)
   apply (smt (verit, best) ConditionalExpr evalDet is_IntVal32_def unfold_const32 valid_int32)
   apply (metis Value.disc(2) Value.distinct(1) unfold_const32 valid_int32)
   apply (metis intval_xor.simps(10) is_IntVal32_def unfold_const32 valid_int32)+
  done


(* Optimisations *)
(* Not sure about the conditions on this one. *)
optimization xor_self_is_false: "(x \<oplus> x) \<longmapsto> false when 
                      (wf_stamp x \<and> stamp_expr x = default_stamp)"
   apply unfold_optimization unfolding le_expr_def using val_xor_self_is_false 
   apply auto[1] defer using size_non_const 
   apply simp
   apply (metis less_1_mult less_one linorder_neqE_nat mult.commute mult_1 numeral_1_eq_Suc_0 
                one_eq_numeral_iff one_less_numeral_iff semiring_norm(77) size_pos 
                zero_less_iff_neq_zero) using val_xor_self_is_false_2 wf_stamp_def
   apply (metis Value.disc(2) Value.distinct(1) bool_to_val.simps(2) evalDet unfold_const32 
                valid_int32)
  done

optimization XorShiftConstantRight: "((const x) \<oplus> y) \<longmapsto> y \<oplus> (const x) when \<not>(is_ConstantExpr y)"
   apply unfold_optimization unfolding le_expr_def using val_xor_commute 
   apply auto[1] using size_non_const 
   apply simp
  done

optimization EliminateRedundantFalse: "(x \<oplus> false) \<longmapsto> x"
   apply unfold_optimization unfolding le_expr_def using val_eliminate_redundant_false 
   apply auto[1] 
   apply (metis evaltree_not_undef) using size_non_const 
   apply simp
  done


optimization opt_mask_out_rhs: "(x \<oplus> (UnaryExpr UnaryNot (ConstantExpr (IntVal32 0)))) \<longmapsto> 
                                       UnaryExpr UnaryNot x"
   apply unfold_optimization unfolding le_expr_def 
   apply simp_all apply auto 
  sorry

end (* End of XorPhase *)

end (* End of file *)
