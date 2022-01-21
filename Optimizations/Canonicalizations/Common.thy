theory Common
  imports 
    OptimizationDSL.Canonicalization
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

method unfold_optimization =
  (unfold rewrite_preservation.simps, unfold rewrite_termination.simps,
    unfold intval.simps,
    rule conjE, simp, simp del: le_expr_def)
  | (unfold rewrite_preservation.simps, unfold rewrite_termination.simps,
    rule conjE, simp, simp del: le_expr_def)

end