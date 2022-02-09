subsection \<open>Conditional Expression\<close>

theory ConditionalPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase Conditional
  terminating size
begin

lemma negates: "is_IntVal32 e \<or> is_IntVal64 e \<Longrightarrow> val_to_bool (val[e]) \<equiv> \<not>(val_to_bool (val[\<not>e]))"
  by (smt (verit, best) Value.disc(1) Value.disc(10) Value.disc(4) Value.disc(5) Value.disc(6) Value.disc(9) intval_logic_negation.elims val_to_bool.simps(1) val_to_bool.simps(2) zero_neq_one)

optimization negate_condition: "((\<not>e) ? x : y) \<longmapsto> (e ? y : x)"
    apply unfold_optimization apply simp using negates
    using ConditionalExprE UnaryExprE intval_logic_negation.elims unary_eval.simps(4) val_to_bool.simps(1) val_to_bool.simps(2) zero_neq_one
    apply (smt (verit) ConditionalExpr)
    unfolding size.simps by simp

optimization const_true: "(true ? x : y) \<longmapsto> x"
   apply unfold_optimization
   apply force
  unfolding size.simps by simp

optimization const_false: "(false ? x : y) \<longmapsto> y"
   apply unfold_optimization
   apply force
  unfolding size.simps by simp

optimization equal_branches: "(e ? x : x) \<longmapsto> x"
   apply unfold_optimization
   apply force
  unfolding size.simps by auto

(* this will be removable after some work *)
definition wff_stamps :: bool where
  "wff_stamps = (\<forall>m p expr val . ([m,p] \<turnstile> expr \<mapsto> val) \<longrightarrow> valid_value val (stamp_expr expr))"

definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

optimization condition_bounds_x: "((x < y) ? x : y) \<longmapsto> x 
    when (stamp_under (stamp_expr x) (stamp_expr y) \<and> wf_stamp x \<and> wf_stamp y)"
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

end

end
