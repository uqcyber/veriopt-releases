theory ConditionalPhase
  imports 
    OptimizationDSL.Canonicalization
    "HOL-Eisbach.Eisbach"
    Semantics.IRTreeEvalThms
begin

fun size :: "IRExpr \<Rightarrow> nat" where
  "size (UnaryExpr op e) = (size e) + 1" |
  "size (BinaryExpr BinAdd x y) = (size x) + ((size y) * 2)" |
  "size (BinaryExpr op x y) = (size x) + (size y)" |
  "size (ConditionalExpr cond t f) = (size cond) + (size t) + (size f) + 2" |
  "size (ConstantExpr c) = 1" |
  "size (ParameterExpr ind s) = 2" |
  "size (LeafExpr nid s) = 2" |
  "size (ConstantVar c) = 2" |
  "size (VariableExpr x s) = 2"

method unfold_optimization =
  (unfold rewrite_preservation.simps, unfold rewrite_termination.simps,
    unfold intval.simps,
    rule conjE, simp, simp del: le_expr_def)
  | (unfold rewrite_preservation.simps, unfold rewrite_termination.simps,
    rule conjE, simp, simp del: le_expr_def)

phase Conditional
  trm size
begin

optimization a: "(e ? x : x) \<mapsto> x"
   apply unfold_optimization
   apply force
  unfolding size.simps by auto

optimization b[intval]: "((x eq y) ? x : y) \<mapsto> y"
   apply unfold_optimization
    apply (smt (z3) bool_to_val.simps(2) intval_equals.elims val_to_bool.simps(1) val_to_bool.simps(3))
    unfolding intval.simps
    apply (smt (z3) BinaryExprE ConditionalExprE Value.inject(1) Value.inject(2) bin_eval.simps(10) bool_to_val.simps(2) evalDet intval_equals.simps(1) intval_equals.simps(10) intval_equals.simps(12) intval_equals.simps(15) intval_equals.simps(16) intval_equals.simps(2) intval_equals.simps(5) intval_equals.simps(8) intval_equals.simps(9) le_expr_def val_to_bool.cases val_to_bool.elims(2))
  unfolding size.simps by auto

(*
lemma unary_eval_outcome: 
  "is_IntVal32 (unary_eval op e) \<or> is_IntVal64 (unary_eval op e) \<or> (unary_eval op e) = UndefVal"
  apply (cases op; auto)
     apply (metis Value.exhaust_sel intval_abs.simps(1) intval_abs.simps(2) intval_abs.simps(3) intval_abs.simps(4) intval_abs.simps(5) is_IntVal32_def is_IntVal64_def)
    apply (metis intval_negate.elims is_IntVal32_def is_IntVal64_def)
   apply (metis intval_not.elims is_IntVal32_def is_IntVal64_def)
  by (metis Value.exhaust_sel intval_logic_negation.simps(1) intval_logic_negation.simps(2) intval_logic_negation.simps(3) intval_logic_negation.simps(4) intval_logic_negation.simps(5) is_IntVal32_def is_IntVal64_def)

lemma valid_under: "[m, p] \<turnstile> e \<mapsto> v \<Longrightarrow> valid_value (stamp_expr e) v"
  sorry

lemma "stamp_under x y 
      \<Longrightarrow> [m, p] \<turnstile> x \<mapsto> e1 \<and> [m, p] \<turnstile> y \<mapsto> e2 
      \<Longrightarrow> val_to_bool (intval_less_than e1 e2)"
  using valid_under sorry
*)

fun stamp_under :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "stamp_under x y = (stpi_upper (stamp_expr x) < stpi_lower (stamp_expr y))"

(* The problem:
   Stamps aren't required to be correct in the evaluation semantics yet.
*)
optimization c: "((x < y) ? x : y) \<mapsto> x when stamp_under x y"
   apply unfold_optimization
  sorry


lemma negates: "is_IntVal32 e \<or> is_IntVal64 e \<Longrightarrow> val_to_bool (val[e]) \<equiv> \<not>(val_to_bool (val[\<not>e]))"
  by (smt (verit, best) Value.disc(1) Value.disc(10) Value.disc(4) Value.disc(5) Value.disc(6) Value.disc(9) intval_logic_negation.elims val_to_bool.simps(1) val_to_bool.simps(2) zero_neq_one)

(* The problem:
   Evaluation of e and \<not>e needs to be of IntVal32 or IntVal64 to allow the above lemma
   to be used. I haven't yet found a way to show this.
*)
optimization d[intval]: "((\<not>e) ? x : y) \<mapsto> (e ? y : x)"
    apply unfold_optimization
  using negates sorry 

optimization e: "((const(IntVal32 1)) ? x : y) \<mapsto> x"
   apply unfold_optimization
   apply force
  unfolding size.simps by simp

optimization f: "((const(IntVal32 0)) ? x : y) \<mapsto> y"
   apply unfold_optimization
   apply force
  unfolding size.simps by simp

end

end
