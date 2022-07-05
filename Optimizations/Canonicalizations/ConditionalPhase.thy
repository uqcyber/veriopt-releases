subsection \<open>Conditional Expression\<close>

theory ConditionalPhase
  imports
    Common
begin

phase Conditional
  terminating size
begin

lemma negates: "is_IntVal32 e \<or> is_IntVal64 e \<Longrightarrow> val_to_bool (val[e]) \<equiv> \<not>(val_to_bool (val[!e]))"
  using intval_logic_negation.simps unfolding logic_negate_def
  by (smt (verit, best) Value.collapse(1) is_IntVal64_def val_to_bool.simps(1) val_to_bool.simps(2) zero_neq_one)

lemma negation_condition_intval: 
  assumes "e \<noteq> UndefVal \<and> \<not>(is_ObjRef e) \<and> \<not>(is_ObjStr e)"
  shows "val[(!e) ? x : y] = val[e ? y : x]"
  using assms by (cases e; auto simp: negates logic_negate_def)

optimization negate_condition: "((!e) ? x : y) \<longmapsto> (e ? y : x)"
    apply simp using negation_condition_intval
  by (smt (verit, ccfv_SIG) ConditionalExpr ConditionalExprE Value.collapse(3) Value.collapse(4) Value.exhaust_disc evaltree_not_undef intval_logic_negation.simps(4) intval_logic_negation.simps(5) negates unary_eval.simps(4) unfold_unary)

optimization const_true: "(true ? x : y) \<longmapsto> x" .

optimization const_false: "(false ? x : y) \<longmapsto> y" .

optimization equal_branches: "(e ? x : x) \<longmapsto> x" .

(* this will be removable after some work *)
definition wff_stamps :: bool where
  "wff_stamps = (\<forall>m p expr val . ([m,p] \<turnstile> expr \<mapsto> val) \<longrightarrow> valid_value val (stamp_expr expr))"

definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

(*
optimization condition_bounds_x: "((u < v) ? x : y) \<longmapsto> x 
    when (stamp_under (stamp_expr u) (stamp_expr v) \<and> wf_stamp u \<and> wf_stamp v)"
   apply unfold_optimization
  using stamp_under_semantics
  using wf_stamp_def
  apply (smt (verit, best) ConditionalExprE le_expr_def stamp_under.simps)
  unfolding size.simps by simp

optimization condition_bounds_y: "((x < y) ? x : y) \<longmapsto> y 
    when (stamp_under (stamp_expr y) (stamp_expr x) \<and> wf_stamp x \<and> wf_stamp y)"
   apply unfold_optimization
  using stamp_under_semantics_inversed
  using wf_stamp_def
  apply (smt (verit, best) ConditionalExprE le_expr_def stamp_under.simps)
  unfolding size.simps by simp

(*extra one*)
optimization b[intval]: "((x eq y) ? x : y) \<longmapsto> y"
   apply unfold_optimization
    apply (smt (z3) bool_to_val.simps(2) intval_equals.elims val_to_bool.simps(1) val_to_bool.simps(3))
    unfolding intval.simps
    apply (smt (z3) BinaryExprE ConditionalExprE Value.inject(1) Value.inject(2) bin_eval.simps(10) bool_to_val.simps(2) evalDet intval_equals.simps(1) intval_equals.simps(10) intval_equals.simps(12) intval_equals.simps(15) intval_equals.simps(16) intval_equals.simps(2) intval_equals.simps(5) intval_equals.simps(8) intval_equals.simps(9) le_expr_def val_to_bool.cases val_to_bool.elims(2))
  unfolding size.simps by auto
*)

end

end
