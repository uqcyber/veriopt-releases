theory OrPhase
  imports
    Common
    NewAnd (* Allows access to mask operations *)
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
  assumes "x \<noteq> UndefVal \<and> (intval_or x (bool_to_val False)) \<noteq> UndefVal"
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

(* Exp level proofs *)
lemma exp_or_equal:
  "exp[x | x] \<ge> exp[x]"
  apply simp using val_or_equal apply auto 
  subgoal premises p for m p xa y
    proof -
      obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
        using p(2) by auto
      obtain y where y: "[m,p] \<turnstile> x \<mapsto> y"
        using p(2) by auto
      then have "val[xa | y] \<noteq> UndefVal"
        by (metis evalDet p(1) p(2) p(3) xa)
      then have "val[xa | xa] = xa"
        apply (cases xa; auto) using eval_unused_bits_zero xa by auto
      then show ?thesis
        by (metis evalDet p(1) p(2) xa)
    qed 
  done

lemma exp_elim_redundant_false:
 "exp[x | false] \<ge> exp[x]"
   apply simp using val_elim_redundant_false apply auto
   subgoal premises p for m p xa
    proof - 
      obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
        using p(2) by auto
      then have "val[xa | (IntVal 32 0)] \<noteq> UndefVal"
        using evalDet p(2) p(3) by blast
      then have "[m,p] \<turnstile> x \<mapsto> val[xa | (IntVal 32 0)]"
        apply (cases xa; auto) using eval_unused_bits_zero xa by fastforce
      then show ?thesis
        using evalDet p(2) xa by blast
    qed
  done

text \<open>Optimisations\<close>
optimization OrEqual: "x | x \<longmapsto> x"
  by (meson exp_or_equal le_expr_def)


optimization OrShiftConstantRight: "((const x) | y) \<longmapsto> y | (const x) when \<not>(is_ConstantExpr y)"
   unfolding le_expr_def using val_shift_const_right_helper size_non_const
   apply simp apply auto 
  sorry

optimization EliminateRedundantFalse: "x | false \<longmapsto> x"
  by (meson exp_elim_redundant_false le_expr_def)


optimization OrNotOperands: "(~x | ~y) \<longmapsto> ~ (x & y)"
   apply auto using val_or_not_operands
  by (metis BinaryExpr UnaryExpr bin_eval.simps(4) intval_not.simps(2) unary_eval.simps(3))

optimization OrLeftFallthrough: "(x | y) \<longmapsto> x
                                when (((and (not (IRExpr_down x)) (IRExpr_up y)) = 0))"
  by (simp add: IRExpr_down_def IRExpr_up_def) 

optimization OrRightFallthrough: "(x | y) \<longmapsto> y
                                when (((and (not (IRExpr_down y)) (IRExpr_up x)) = 0))"
  by (meson exp_or_commute OrLeftFallthrough(1) order.trans rewrite_preservation.simps(2))

end (* End of OrPhase *)

end (* End of file *)
