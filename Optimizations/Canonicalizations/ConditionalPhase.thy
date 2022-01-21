theory ConditionalPhase
  imports
    Common
    Semantics.IRTreeEvalThms
    Proofs.StampEvalThms
begin

phase Conditional
  trm size
begin

lemma negates: "is_IntVal32 e \<or> is_IntVal64 e \<Longrightarrow> val_to_bool (val[e]) \<equiv> \<not>(val_to_bool (val[\<not>e]))"
  by (smt (verit, best) Value.disc(1) Value.disc(10) Value.disc(4) Value.disc(5) Value.disc(6) Value.disc(9) intval_logic_negation.elims val_to_bool.simps(1) val_to_bool.simps(2) zero_neq_one)

optimization negate_condition: "((\<not>e) ? x : y) \<mapsto> (e ? y : x)"
    apply unfold_optimization
  using negates evaltree.ConditionalExpr
  apply (smt (verit, best) ConditionalExprE UnaryExprE is_IntVal32_def is_IntVal64_def le_expr_def stamp_implies_valid_value unary_eval.simps(4) valid_value.elims(2))
  unfolding size.simps by simp

optimization const_true: "((const(IntVal32 1)) ? x : y) \<mapsto> x"
   apply unfold_optimization
   apply force
  unfolding size.simps by simp

optimization const_false: "((const(IntVal32 0)) ? x : y) \<mapsto> y"
   apply unfold_optimization
   apply force
  unfolding size.simps by simp

optimization equal_branches: "(e ? x : x) \<mapsto> x"
   apply unfold_optimization
   apply force
  unfolding size.simps by auto

optimization condition_bounds_x: "((x < y) ? x : y) \<mapsto> x when stamp_under (stamp_expr x) (stamp_expr y)"
   apply unfold_optimization
  using stamp_under_semantics
   apply fastforce
  unfolding size.simps by simp

optimization condition_bounds_y: "((x < y) ? x : y) \<mapsto> y when stamp_under (stamp_expr y) (stamp_expr x)"
   apply unfold_optimization
  using stamp_under_semantics_inversed
   apply fastforce
  unfolding size.simps by simp

(*extra one*)
optimization b[intval]: "((x eq y) ? x : y) \<mapsto> y"
   apply unfold_optimization
    apply (smt (z3) bool_to_val.simps(2) intval_equals.elims val_to_bool.simps(1) val_to_bool.simps(3))
    unfolding intval.simps
    apply (smt (z3) BinaryExprE ConditionalExprE Value.inject(1) Value.inject(2) bin_eval.simps(10) bool_to_val.simps(2) evalDet intval_equals.simps(1) intval_equals.simps(10) intval_equals.simps(12) intval_equals.simps(15) intval_equals.simps(16) intval_equals.simps(2) intval_equals.simps(5) intval_equals.simps(8) intval_equals.simps(9) le_expr_def val_to_bool.cases val_to_bool.elims(2))
  unfolding size.simps by auto

end

end
