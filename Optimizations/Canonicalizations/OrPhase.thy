subsection \<open>OrNode Phase\<close>

theory OrPhase
  imports
    Common
begin

context stamp_mask
begin

text \<open>
Taking advantage of the truth table of or operations.

\begin{center}
\begin{tabular}{ c c c c }
\# & x & y & $x | y$ \\
1 & 0 & 0 & 0 \\ 
2 & 0 & 1 & 1 \\  
3 & 1 & 0 & 1 \\
4 & 1 & 1 & 1   
\end{tabular}
\end{center}

If row 2 never applies, that is, canBeZero x \& canBeOne y = 0,
then $(x | y) = x$.

Likewise, if row 3 never applies, canBeZero y \& canBeOne x = 0,
then $(x | y) = y$.
\<close>

lemma OrLeftFallthrough:
  assumes "(and (not (\<down>x)) (\<up>y)) = 0"
  shows "exp[x | y] \<ge> exp[x]"
  using assms
  apply simp apply ((rule allI)+; rule impI)
  subgoal premises eval for m p v
  proof -
    obtain b vv where e: "[m, p] \<turnstile> exp[x | y] \<mapsto> IntVal b vv"
      using eval
      by (metis BinaryExprE bin_eval_new_int new_int.simps)
    from e obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      apply (subst (asm) unfold_binary_width)
      by force+
    from e obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      apply (subst (asm) unfold_binary_width)
      by force+
    have vdef: "v = intval_or (IntVal b xv) (IntVal b yv)"
      using e xv yv
      by (metis bin_eval.simps(5) eval(2) evalDet unfold_binary)
    have "\<forall> i. (bit xv i) | (bit yv i) = (bit xv i)"
      by (metis assms bit_and_iff not_down_up_mask_and_zero_implies_zero xv yv)
    then have "IntVal b xv = intval_or (IntVal b xv) (IntVal b yv)"
      by (smt (verit, ccfv_threshold) and.idem assms bit.conj_disj_distrib eval_unused_bits_zero intval_or.simps(1) new_int.simps new_int_bin.simps not_down_up_mask_and_zero_implies_zero word_ao_absorbs(3) xv yv)
    then show ?thesis
      using vdef
      using xv by presburger
  qed
  done

lemma OrRightFallthrough: 
  assumes "(and (not (\<down>y)) (\<up>x)) = 0"
  shows "exp[x | y] \<ge> exp[y]"
  using assms
  apply simp apply ((rule allI)+; rule impI)
  subgoal premises eval for m p v
  proof -
    obtain b vv where e: "[m, p] \<turnstile> exp[x | y] \<mapsto> IntVal b vv"
      using eval
      by (metis BinaryExprE bin_eval_new_int new_int.simps)
    from e obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      apply (subst (asm) unfold_binary_width)
      by force+
    from e obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      apply (subst (asm) unfold_binary_width)
      by force+
    have vdef: "v = intval_or (IntVal b xv) (IntVal b yv)"
      using e xv yv
      by (metis bin_eval.simps(5) eval(2) evalDet unfold_binary)
    have "\<forall> i. (bit xv i) | (bit yv i) = (bit yv i)"
      by (metis assms bit_and_iff not_down_up_mask_and_zero_implies_zero xv yv)
    then have "IntVal b yv = intval_or (IntVal b xv) (IntVal b yv)"
      by (metis (no_types, lifting) assms eval_unused_bits_zero intval_or.simps(1) new_int.elims new_int_bin.elims stamp_mask.not_down_up_mask_and_zero_implies_zero stamp_mask_axioms word_ao_absorbs(8) xv yv)
    then show ?thesis
      using vdef
      using yv by presburger
  qed
  done

end

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
  and    "(val[x | x] \<noteq> UndefVal)"
  shows   "val[x | x] = val[x]"
   apply (cases x; auto) using bin_or_equal assms 
  by auto+ 

lemma val_elim_redundant_false:
  assumes "x = new_int b v"
  and     "val[x | false] \<noteq> UndefVal"
  shows   "val[x | false] = val[x]"
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
   using val_or_equal apply auto
   by (smt (verit, ccfv_SIG) evalDet eval_unused_bits_zero intval_negate.elims intval_or.simps(2) 
       intval_or.simps(6) intval_or.simps(7) new_int.simps val_or_equal)

lemma exp_elim_redundant_false:
 "exp[x | false] \<ge> exp[x]"
   using val_elim_redundant_false apply auto
   by (smt (verit) Value.sel(1) eval_unused_bits_zero intval_or.elims new_int.simps 
       new_int_bin.simps val_elim_redundant_false)

text \<open>Optimisations\<close>

optimization OrEqual: "x | x \<longmapsto> x"
  by (meson exp_or_equal le_expr_def)

optimization OrShiftConstantRight: "((const x) | y) \<longmapsto> y | (const x) when \<not>(is_ConstantExpr y)"
  using size_flip_binary apply force
  apply auto
  by (simp add: BinaryExpr unfold_const val_shift_const_right_helper)

optimization EliminateRedundantFalse: "x | false \<longmapsto> x"
  by (meson exp_elim_redundant_false le_expr_def)

optimization OrNotOperands: "(~x | ~y) \<longmapsto> ~(x & y)"
  apply (metis add_2_eq_Suc' less_SucI not_add_less1 not_less_eq size_binary_const size_non_add)
   apply auto using val_or_not_operands
  by (metis BinaryExpr UnaryExpr bin_eval.simps(4) intval_not.simps(2) unary_eval.simps(3))

definition IRExpr_up :: "IRExpr \<Rightarrow> int64" where
  "IRExpr_up e = not 0"

definition IRExpr_down :: "IRExpr \<Rightarrow> int64" where
  "IRExpr_down e = 0"

lemma ucast_zero: "(ucast (0::int64)::int32) = 0"
  by simp

lemma ucast_minus_one: "(ucast (-1::int64)::int32) = -1"
  apply transfer by auto

interpretation simple_mask: stamp_mask
  "IRExpr_up :: IRExpr \<Rightarrow> int64"
  "IRExpr_down :: IRExpr \<Rightarrow> int64"
  unfolding IRExpr_up_def IRExpr_down_def
  apply unfold_locales
  by (simp add: ucast_minus_one)+

optimization OrLeftFallthrough:
  "x | y \<longmapsto> x when ((and (not (IRExpr_down x)) (IRExpr_up y)) = 0)"
  using simple_mask.OrLeftFallthrough by blast

optimization OrRightFallthrough:
  "x | y \<longmapsto> y when ((and (not (IRExpr_down y)) (IRExpr_up x)) = 0)"
  using simple_mask.OrRightFallthrough by blast

end (* End of OrPhase *)


end (* End of file *)
