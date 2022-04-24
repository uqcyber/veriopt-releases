section \<open>Canonicalization Phase\<close>

theory Common
  imports 
    OptimizationDSL.Canonicalization
    Semantics.IRTreeEvalThms
    "HOL-Eisbach.Eisbach"
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

lemma size_pos[simp]: "0 < size y"
  apply (induction y; auto?)
  subgoal premises prems for op a b
    using prems by (induction op; auto)
  done

lemma size_non_add: "op \<noteq> BinAdd \<Longrightarrow> size (BinaryExpr op a b) = size a + size b"
  by (induction op; auto)

lemma size_non_const:
  "\<not> is_ConstantExpr y \<Longrightarrow> 1 < size y"
  using size_pos apply (induction y; auto)
  subgoal premises prems for op a b
    apply (cases "op = BinAdd")
    using size_non_add size_pos apply auto
    by (simp add: Suc_lessI one_is_add)+
  done

method unfold_optimization =
  (unfold rewrite_preservation.simps, unfold rewrite_termination.simps,
    unfold intval.simps,
    rule conjE, simp, simp del: le_expr_def)
  | (unfold rewrite_preservation.simps, unfold rewrite_termination.simps,
    rule conjE, simp, simp del: le_expr_def)

end