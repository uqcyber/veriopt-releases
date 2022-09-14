theory OrPhase
  imports
    Common
begin

section \<open>Optimizations for Or Nodes\<close>

phase OrNode
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
  assumes "x = new_int b v"
  assumes "x \<noteq> UndefVal \<and> ((intval_or x x) \<noteq> UndefVal)"
  shows "val[x | x] = val[x]"
   apply (cases x; auto) using bin_or_equal assms 
  by auto+ 

lemma val_elim_redundant_false:
  assumes "x = new_int b v"
  assumes "val[x | false] \<noteq> UndefVal"
  shows "val[x | false] = val[x]"
   using assms apply (cases x; auto) by presburger

lemma val_shift_const_right_helper:
   "val[x | y] = val[y | x]"
   apply (cases x; cases y; auto)
  by (simp add: or.commute)+

lemma val_or_not_operands:
 "val[~x | ~y] = val[~(x & y)]"
  apply (cases x; cases y; auto)
  by (simp add: take_bit_not_take_bit)

(* Expr level proofs *)
lemma exp_or_equal:
  "exp[x | x] \<ge> exp[x]"
   using val_or_equal apply auto
   by (smt (verit, ccfv_SIG) evalDet eval_unused_bits_zero intval_negate.elims intval_or.simps(2) intval_or.simps(6) intval_or.simps(7) new_int.simps val_or_equal)

lemma exp_elim_redundant_false:
 "exp[x | false] \<ge> exp[x]"
   using val_elim_redundant_false apply auto
   by (smt (verit) Value.sel(1) eval_unused_bits_zero intval_or.elims new_int.simps new_int_bin.simps val_elim_redundant_false)


(* Optimizations *)
optimization OrEqual: "x | x \<longmapsto> x"
  by (meson exp_or_equal le_expr_def)


optimization OrShiftConstantRight: "((const x) | y) \<longmapsto> y | (const x) when \<not>(is_ConstantExpr y)"
  using size_non_const apply force
  apply auto
  by (simp add: BinaryExpr unfold_const val_shift_const_right_helper)

optimization EliminateRedundantFalse: "x | false \<longmapsto> x"
  by (meson exp_elim_redundant_false le_expr_def)


optimization OrNotOperands: "(~x | ~y) \<longmapsto> ~(x & y)"
  defer
   apply auto using val_or_not_operands
  apply (metis BinaryExpr UnaryExpr bin_eval.simps(4) intval_not.simps(2) unary_eval.simps(3))
  sorry (* termination *)

end (* End of OrPhase *)


context stamp_mask
begin

lemma OrLeftFallthrough:
  assumes "(and (not (\<down>x)) (\<up>y)) = 0"
  shows "exp[x | y] \<ge> exp[x]"
  using assms sorry

lemma OrRightFallthrough: 
  assumes "(and (not (\<down>y)) (\<up>x)) = 0"
  shows "exp[x | y] \<ge> exp[y]"
  using assms sorry

end (* End of file *)
