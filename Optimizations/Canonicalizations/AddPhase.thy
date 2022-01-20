theory AddPhase
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
    rule conjE, simp, simp del: le_expr_def)

phase SnipPhase 
  trm size
begin

optimization BinaryFoldConstant: "BinaryExpr op c1 c2 \<mapsto> ConstantExpr (bin_eval op val_c1 val_c2)"
   apply unfold_optimization
  sorry

thm BinaryFoldConstant(1)
thm BinaryFoldConstant(2)
thm BinaryFoldConstant
value "BinaryFoldConstant_code (ConstantExpr (IntVal32 0))"

optimization AddShiftConstantRight: "(c1 + y) \<mapsto> y + c1 when \<not>(is_ConstantExpr y)"
  apply unfold_optimization
  sorry

optimization AddNeutral: "(e + (const (IntVal32 0))) \<mapsto> e"
  apply unfold_optimization
  sorry

ML_val \<open>@{term \<open>x = y\<close>}\<close>

optimization NeutralLeftSub[intval]: "((e\<^sub>1 - e\<^sub>2) + e\<^sub>2) \<mapsto> e\<^sub>1"
  apply unfold_optimization unfolding intval.simps
  using intval_add.simps intval_sub.simps
    apply (metis (no_types, lifting) diff_add_cancel val_to_bool.cases)
  sorry

optimization NeutralRightSub[intval]: " e\<^sub>2 + (e\<^sub>1 - e\<^sub>2) \<mapsto> e\<^sub>1"
  apply unfold_optimization
  using NeutralLeftSub(1) intval_add_sym apply auto[1]
  sorry

optimization AddToSub: "-e + y \<mapsto> y - e"
  apply unfold_optimization
  sorry

print_context
end

print_phases

end