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
      by (metis BinaryExprE bin_eval_new_int new_int.simps eval(2))
    from e obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      apply (subst (asm) unfold_binary_width) by force+
    from e obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      apply (subst (asm) unfold_binary_width) by force+
    have vdef: "v = val[(IntVal b xv) | (IntVal b yv)]"
      by (metis bin_eval.simps(7) eval(2) evalDet unfold_binary xv yv)
    have "\<forall> i. (bit xv i) | (bit yv i) = (bit xv i)"
      by (metis assms bit_and_iff not_down_up_mask_and_zero_implies_zero xv yv)
    then have "IntVal b xv = val[(IntVal b xv) | (IntVal b yv)]"
      by (metis (no_types, lifting) and.idem assms bit.conj_disj_distrib eval_unused_bits_zero yv xv
          intval_or.simps(1) new_int.simps new_int_bin.simps not_down_up_mask_and_zero_implies_zero 
          word_ao_absorbs(3))
    then show ?thesis
      using xv vdef by presburger
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
      by (metis BinaryExprE bin_eval_new_int new_int.simps eval(2))
    from e obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      apply (subst (asm) unfold_binary_width) by force+
    from e obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      apply (subst (asm) unfold_binary_width) by force+
    have vdef: "v = val[(IntVal b xv) | (IntVal b yv)]"
      by (metis bin_eval.simps(7) eval(2) evalDet unfold_binary xv yv)
    have "\<forall> i. (bit xv i) | (bit yv i) = (bit yv i)"
      by (metis assms bit_and_iff not_down_up_mask_and_zero_implies_zero xv yv)
    then have "IntVal b yv = val[(IntVal b xv) | (IntVal b yv)]"
      by (metis (no_types, lifting) assms eval_unused_bits_zero intval_or.simps(1) new_int.elims yv 
          new_int_bin.elims stamp_mask.not_down_up_mask_and_zero_implies_zero stamp_mask_axioms xv
          word_ao_absorbs(8))
    then show ?thesis
      using vdef yv by presburger
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
  and     "val[x | x] \<noteq> UndefVal"
  shows   "val[x | x] = val[x]"
  by (auto simp: assms)

lemma val_elim_redundant_false:
  assumes "x = new_int b v"
  and     "val[x | false] \<noteq> UndefVal"
  shows   "val[x | false] = val[x]"
  using assms by (cases x; auto; presburger)

lemma val_or_not_operands:
  "val[~x | ~y] = val[~(x & y)]"
  by (cases x; cases y; auto simp: take_bit_not_take_bit)

lemma val_or_inverse:
  assumes "n = IntVal 32 v"
  shows "val[n | ~n] \<approx> new_int 32 (-1)"
  apply (auto simp: assms) by (metis bit.disj_cancel_right mask_eq_take_bit_minus_one take_bit_or)

(* Exp level proofs *)
lemma exp_or_equal:
  "exp[x | x] \<ge> exp[x]"
  apply auto
  subgoal premises p for m p xa ya
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis evalDet evaltree_not_undef intval_is_null.cases intval_or.simps(3,4,5) p(1,3) xv)
    have "xv = new_int xb (xvv)"
      using eval_unused_bits_zero xv xvv by auto
    then show ?thesis
      by (metis evalDet p(1,2,3) val_or_equal xv)
  qed
  done

lemma exp_elim_redundant_false:
  "exp[x | false] \<ge> exp[x]"
  apply auto
  subgoal premises p for m p xa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis evalDet evaltree_not_undef intval_is_null.cases intval_or.simps(3,4,5) p(1,2) xv)
    have "xv = new_int xb (xvv)"
      using eval_unused_bits_zero xv xvv by auto
    then show ?thesis
      by (metis evalDet p(1,2) val_elim_redundant_false xv)
  qed
  done

text \<open>Optimisations\<close>

optimization OrEqual: "x | x \<longmapsto> x"
  by (meson exp_or_equal)

optimization OrShiftConstantRight: "((const x) | y) \<longmapsto> y | (const x) when \<not>(is_ConstantExpr y)"
  using exp_or_commutative by blast

optimization EliminateRedundantFalse: "x | false \<longmapsto> x"
  by (meson exp_elim_redundant_false)

optimization OrNotOperands: "(~x | ~y) \<longmapsto> ~(x & y)"
  apply (simp add: less_SucI size_bin_cycle1_lt_succ_sum) apply auto
  by (metis BinaryExpr bin_eval.simps(6) intval_not.simps(2) unary_eval.simps(3) unfold_unary
      val_or_not_operands)

optimization OrLeftFallthrough:
  "x | y \<longmapsto> x when ((and (not (IRExpr_down x)) (IRExpr_up y)) = 0)"
  using simple_mask.OrLeftFallthrough by blast

optimization OrRightFallthrough:
  "x | y \<longmapsto> y when ((and (not (IRExpr_down y)) (IRExpr_up x)) = 0)"
  using simple_mask.OrRightFallthrough by blast

optimization OrInverse: "exp[n | ~n] \<longmapsto> (const (new_int 32 (not 0)))
                         when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
  apply auto
  subgoal premises p for m p xa xaa
  proof -
    obtain nv where nv: "[m,p] \<turnstile> n \<mapsto> nv"
      using p(3) by auto
    obtain nbits nvv where nvv: "nv = IntVal nbits nvv"
      by (metis evalDet evaltree_not_undef intval_logic_negation.cases intval_not.simps(3,4,5) nv
          p(5,6))
    then have width: "nbits = 32"
      by (metis Value.inject(1) nv p(1,2) valid_int wf_stamp_def)
    then have stamp: "constantAsStamp (IntVal 32 (mask 32)) =
                  (IntegerStamp 32 (int_signed_value 32 (mask 32)) (int_signed_value 32 (mask 32)))"
      by auto
    have wf: "wf_value (IntVal 32 (mask 32))"
      unfolding wf_value_def stamp apply auto by eval+
    then have "val[nv | ~nv] = (new_int 32 (or (not nvv) nvv))"
      using intval_or.simps val_or_inverse nvv width by auto
    then show ?thesis
      by (metis bit.compl_zero evalDet local.wf neg_one.elims nv p(3,5) bit.disj_cancel_left
          neg_one_value new_int_mask unfold_const)
  qed
  done

optimization OrInverseCommute: "exp[~n | n] \<longmapsto> (const (new_int 32 (not 0)))
                                when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
  using IRExpr.disc(42) One_nat_def size_non_const apply presburger
  using OrInverse exp_or_commutative by auto

end (* End of OrPhase *)

end (* End of file *)