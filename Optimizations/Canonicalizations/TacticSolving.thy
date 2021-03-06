theory TacticSolving
  imports Common
begin

fun size :: "IRExpr \<Rightarrow> nat" where
  "size (UnaryExpr op e) = (size e) * 2" |
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

phase TacticSolving
  terminating size
begin

subsection \<open>AddNode\<close>
(*lemma val_add_left_negate_to_sub:
  "val[-x + y] \<approx> val[y - x]"
  apply simp by (cases x; cases y; auto)

lemma exp_add_left_negate_to_sub:
  "exp[-x + y] \<ge> exp[y - x]"
  using val_add_left_negate_to_sub by auto*)

lemma value_approx_implies_refinement:
  assumes "lhs \<approx> rhs"
  assumes "\<forall>m p v. ([m, p] \<turnstile> elhs \<mapsto> v) \<longrightarrow> v = lhs"
  assumes "\<forall>m p v. ([m, p] \<turnstile> erhs \<mapsto> v) \<longrightarrow> v = rhs"
  assumes "\<forall>m p v1 v2. ([m, p] \<turnstile> elhs \<mapsto> v1) \<longrightarrow> ([m, p] \<turnstile> erhs \<mapsto> v2)"
  shows "elhs \<ge> erhs"
  using assms unfolding le_expr_def well_formed_equal_def
  using evalDet evaltree_not_undef
  by metis

method explore_cases for x y :: Value =
  (cases x; cases y; auto)

method explore_cases_bin for x :: IRExpr =
  (cases x; auto)

method obtain_approx_eq for lhs rhs x y :: Value =
  (rule meta_mp[where P="lhs \<approx> rhs"], defer_tac, explore_cases x y)

method obtain_eval for exp::IRExpr and val::Value =
  (rule meta_mp[where P="\<And>m p v. ([m, p] \<turnstile> exp \<mapsto> v) \<Longrightarrow> v = val"], defer_tac)

method solve for lhs rhs x y :: Value =
  (match conclusion in "size _ < size _" \<Rightarrow> \<open>simp\<close>)?,
  (match conclusion in "(elhs::IRExpr) \<ge> (erhs::IRExpr)" for elhs erhs \<Rightarrow> \<open>
    (obtain_approx_eq lhs rhs x y)?\<close>)


print_methods
(*
    (simp del: well_formed_equal_def le_expr_def)?;
    ((rule allI)+)?\<close>)*)
thm BinaryExprE
optimization opt_add_left_negate_to_sub:
  "-x + y \<longmapsto> y - x"
  (*defer apply simp apply (rule allI)+ apply (rule impI)
   apply (subgoal_tac "\<forall>x1. [m, p] \<turnstile> exp[-x + y] \<mapsto> x1") defer
  *)
   apply (solve "val[-x1 + y1]" "val[y1 - x1]" x1 y1)
  apply simp apply auto using evaltree_not_undef sorry
(*
  apply (obtain_eval "exp[-x + y]" "val[-x1 + y1]")
  

  apply (rule BinaryExprE)
  apply (rule allI)+ sorry
  apply (auto simp: unfold_evaltree) sorry*)
  (*
   defer apply (test "val[-x1 + y1]" "val[y1 - x1]" x1 y1)
   apply (rule meta_mp[where P="val[-x1 + y1] \<approx> val[y1 - x1]"])
    prefer 2 apply (cases x1; cases y1; auto)
   apply (subgoal_tac "val[-x1 + y1] \<approx> val[y1 - x1]")
    apply (cases x1; cases y1; auto)
  using exp_add_left_negate_to_sub apply simp
  unfolding size.simps by simp*)

subsection \<open>NegateNode\<close>

lemma val_distribute_sub: 
 "val[-(x-y)] \<approx> val[y-x]" 
  by (cases x; cases y; auto) 

optimization distribute_sub: "-(x-y) \<longmapsto> (y-x)" 
  apply simp
  using val_distribute_sub apply simp
  using unfold_binary unfold_unary by auto

lemma val_xor_self_is_false:
  assumes "is_IntVal32 x"
  shows "val[x \<oplus> x] \<approx> val[false]"
  apply simp using assms by (cases x; auto)

definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"


lemma exp_xor_self_is_false: 
  assumes "stamp_expr x = IntegerStamp 32 l h"
  assumes "wf_stamp x"
  shows "exp[x \<oplus> x] >= exp[false]"
  unfolding le_expr_def using assms unfolding wf_stamp_def
  using val_xor_self_is_false evaltree_not_undef
  by (metis BinaryExprE Value.disc(2) bin_eval.simps(6) evalDet unfold_const32 valid_int32 well_formed_equal_defn)

end

end