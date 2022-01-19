theory AddPhase
  imports
    OptimizationDSL.Canonicalization
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

phase SnipPhase 
  trm size
begin

optimization BinaryFoldConstant: "BinaryExpr op c1 c2 \<mapsto> ConstantExpr (bin_eval op val_c1 val_c2)"
  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  sorry

thm BinaryFoldConstant(1)
thm BinaryFoldConstant(2)
thm BinaryFoldConstant

optimization AddShiftConstantRight: "(c1 + y) \<mapsto> y + c1 when \<not>(is_ConstantExpr y)"
  unfolding rewrite_preservation.simps rewrite_termination.simps
  apply (rule conjE, simp, simp del: le_expr_def, rule impI)
  sorry

optimization AddNeutral: "(e + (const (IntVal32 0))) \<mapsto> e"
  unfolding rewrite_preservation.simps
  sorry

optimization NeutralLeftSub: "(e\<^sub>1 - e\<^sub>2) + e\<^sub>2 \<mapsto> e\<^sub>1"
  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  sorry

optimization NeutralRightSub: " e\<^sub>2 + (e\<^sub>1 - e\<^sub>2) \<mapsto> e\<^sub>1"
  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  sorry

optimization AddToSub: "-e + y \<mapsto> y - e"
  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  sorry

print_context
end

print_phases

end