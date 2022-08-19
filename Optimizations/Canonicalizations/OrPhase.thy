theory OrPhase
  imports
    Common
    NewAnd (* Allows access to mask operations *)
begin

section \<open>Optimizations for Or Nodes\<close>

phase OrPhase
  terminating size
begin

(* Word level proofs *)
lemma bin_or_equal:
  "bin[x | x] = bin[x]"
  by simp

lemma bin_shift_const_right_helper:
 "x | y = y | x"
  by simp

lemma bin_or_not_operands:
 "(~x | ~y) = (~(x & y))"
  by simp

(* Value level proofs *)
lemma val_or_equal:
  assumes "x \<noteq> UndefVal \<and> ((intval_or x x) \<noteq> UndefVal)"
  shows "val[x | x] = val[x]"
   apply (cases x; auto) using bin_or_equal assms 
  by auto+ 

lemma val_elim_redundant_false:
  assumes "x \<noteq> UndefVal \<and> (intval_or x (bool_to_val False)) \<noteq> UndefVal"
  shows "val[x | false] = val[x]"
   using assms apply (cases x) 
  by simp+

lemma val_shift_const_right_helper:
   "val[x | y] = val[y | x]"
   apply (cases x; cases y; auto)
  by (simp add: or.commute)+

lemma val_or_not_operands:
 "val[~x | ~y] = val[~(x & y)]"
  by (cases x; cases y; auto)

(* Expr level proofs *)
lemma exp_or_equal:
  "exp[x | x] \<ge> exp[x]"
   apply simp using val_or_equal
  by (metis bin_eval.simps(5) evalDet evaltree_not_undef unfold_binary)

lemma exp_elim_redundant_false:
 "exp[x | false] \<ge> exp[x]"
   apply simp using val_elim_redundant_false 
   apply (cases x)
  by (metis BinaryExprE bin_eval.simps(5) bool_to_val.simps(2) evaltree_not_undef unfold_const32)+
  
(* Optimizations *)
optimization or_equal: "x | x \<longmapsto> x"
  by (meson exp_or_equal le_expr_def)


optimization OrShiftConstantRight: "((const x) | y) \<longmapsto> y | (const x) when \<not>(is_ConstantExpr y)"
   unfolding le_expr_def using val_shift_const_right_helper size_non_const
   apply simp apply auto 
  sorry

optimization elim_redundant_false: "x | false \<longmapsto> x"
  by (meson exp_elim_redundant_false le_expr_def)


optimization or_not_operands: "(~x | ~y) \<longmapsto> ~ (x & y)"
   apply auto using val_or_not_operands
  by (metis bin_eval.simps(4) intval_not.simps(3) unary_eval.simps(3) unfold_binary 
          unfold_unary) 

optimization or_left_fall_through: "(x | y) \<longmapsto> x
                                when (((and (not (IRExpr_down x)) (IRExpr_up y)) = 0))"
  by (simp add: IRExpr_down_def IRExpr_up_def) 

optimization or_right_fall_through: "(x | y) \<longmapsto> y
                                when (((and (not (IRExpr_down y)) (IRExpr_up x)) = 0))"
  by (meson exp_or_commute or_left_fall_through(1) order.trans rewrite_preservation.simps(2))

end (* End of OrPhase *)

end (* End of file *)
