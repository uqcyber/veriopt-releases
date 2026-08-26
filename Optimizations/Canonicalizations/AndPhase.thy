subsection \<open>AndNode Phase\<close>

theory AndPhase
  imports
    Common
    Proofs.StampEvalThms
begin

context stamp_mask
begin

lemma AndRightFallthrough: "((and (not (\<down> x)) (\<up> y)) = 0) \<longrightarrow> exp[x & y] \<ge> exp[y]"
  apply simp apply (rule impI; (rule allI)+; rule impI)
  subgoal premises p for m p v
    proof -
      obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
        using p(2) by blast
      obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> yv"
        using p(2) by blast
      obtain xb xvv where xvv: "xv = IntVal xb xvv"
        by (metis bin_eval_inputs_are_ints bin_eval_int evalDet is_IntVal_def p(2) unfold_binary xv)
      obtain yb yvv where yvv: "yv = IntVal yb yvv"
        by (metis bin_eval_inputs_are_ints bin_eval_int evalDet is_IntVal_def p(2) unfold_binary yv)
      have equalAnd: "v = val[xv & yv]"
        by (metis BinaryExprE bin_eval.simps(6) evalDet p(2) xv yv)
      then have andUnfold: "val[xv & yv] = (if xb = yb then new_int xb (and xvv yvv) else UndefVal)"
        by (simp add: xvv yvv)
      have "v = yv"
        apply (cases v; cases yv; auto)
        using p(2) yvv apply auto prefer 2
        apply (metis Value.inject(1) andUnfold eval_int_implies_truncated new_int_truncated_eq p(1)
               equalAnd not_down_up_mask_and_zero_implies_zero xv xvv yv)
        by (metis Value.distinct(9,11,13) andUnfold equalAnd new_int.simps intval_bits.simps)+
      then show ?thesis
        by (simp add: yv)
    qed
  done

lemma AndLeftFallthrough: "((and (not (\<down> y)) (\<up> x)) = 0) \<longrightarrow> exp[x & y] \<ge> exp[x]"
  using AndRightFallthrough exp_and_commutative by simp

end

phase AndNode
  terminating size
begin

(* Word level proofs *)
lemma bin_and_equal_not:
 "(x & ~x) = False"
  by simp

lemma bin_and_nots:
 "(~x & ~y) = (~(x | y))"
  by simp

lemma bin_and_neutral:
 "(x & ~False) = x"
  by simp

(* Value level proofs *)
lemma val_and_equal:
  assumes "x = new_int b v"
  and     "val[x & x] \<noteq> UndefVal"
  shows   "val[x & x] = x"
  by (auto simp: assms)

lemma val_and_nots:
  "val[~x & ~y] = val[~(x | y)]"
  by (cases x; cases y; auto simp: take_bit_not_take_bit)

lemma val_and_equal_not:
  assumes "x = new_int b v"
  and "val[x & ~x] \<noteq> UndefVal"
shows "val[x & ~x] = new_int b 0"
  using assms apply auto
  by (metis assms(1) new_int_unused_bits_zero take_bit_and take_bit_of_0 word_and_not)

lemma val_and_neutral:
  assumes "x = new_int b v"
  and     "val[x & ~(new_int b' 0)] \<noteq> UndefVal"
  shows   "val[x & ~(new_int b' 0)] = x"
  using assms apply (simp add: take_bit_eq_mask) by presburger

lemma val_and_zero:
  assumes "x = new_int b v"
  shows   "val[x & (IntVal b 0)] = IntVal b 0"
  by (auto simp: assms)

lemma val_and_self:
  assumes "n = IntVal 32 v"
  shows "val[~n & n] = new_int 32 0"
  apply (auto simp: assms) by (metis bit.conj_cancel_left take_bit_and take_bit_of_0)

(* TODO double check encoding *)
lemma val_and_sign_extend:
  assumes "e = (1 << In)-1"
  shows "val[(intval_sign_extend In Out x) & (IntVal b e)] = intval_zero_extend In Out x"
  using assms apply (cases x; auto)
  sorry

lemma val_and_sign_extend_2:
  assumes "e = (1 << In)-1 \<and> intval_and (intval_sign_extend In Out x) (IntVal 32 e) \<noteq> UndefVal"
  shows "val[(intval_sign_extend In Out x) &  (IntVal 32 e)] = intval_zero_extend In Out x"
  using assms apply (cases x;  auto) 
  sorry

(* Exp level proofs *)
lemma exp_and_equal:
  "exp[x & x] \<ge> exp[x]"
  apply auto
  subgoal premises p for m p xv yv
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain yv where yv: "[m,p] \<turnstile> x \<mapsto> yv"
      using p(1) by auto
    then have evalSame: "xv = yv"
      using evalDet xv by auto
    then have notUndef: "xv \<noteq> UndefVal \<and> yv \<noteq> UndefVal"
      using evaltree_not_undef xv by blast
    then have andNotUndef: "val[xv & yv] \<noteq> UndefVal"
      by (metis evalDet evalSame p(1,2,3) xv)
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis Value.exhaust_sel andNotUndef evalSame intval_and.simps(3,4,9) notUndef)
    obtain yb yvv where yvv: "yv = IntVal yb yvv"
      using evalSame xvv by auto
    then have widthSame: "xb = yb"
      using evalSame xvv by auto
    then have valSame: "yvv = xvv"
      using evalSame xvv yvv by blast
    then have "val[xv & yv] = new_int xb xvv"
      using evalSame xvv by auto
    then show ?thesis
      by (metis eval_unused_bits_zero new_int.simps evalDet p(1,2) valSame widthSame xv xvv yvv)
  qed
  done

lemma exp_and_nots:
  "exp[~x & ~y] \<ge> exp[~(x | y)]"
  using val_and_nots by force

lemma exp_and_equal_not:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp b lo hi"
  shows "exp[~x & x] \<ge> exp[const (new_int b 0)]"
  using val_and_equal_not apply auto
  subgoal premises p for m p y xa
  proof -
    obtain y where y: "[m,p] \<turnstile> x \<mapsto> y"
      using p by auto
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p by auto
    then have eqa: "xa = y"
      using evalDet xa y by blast
    obtain xb xvv where xy: "y = IntVal xb xvv"
      by (metis evalDet intval_not.elims p(4,5) y)
    obtain xc xva where xa: "xa = IntVal xc xva"
      by (simp add: eqa xy)
    then have unfoldEq: "val[(~xa) & y] = new_int xb (and (not xva) xvv)"
      by (metis (no_types, lifting) Value.inject(1) bit.conj_cancel_left eqa evalDet new_int.elims y
          eval_unused_bits_zero p(2,3,4) val_and_commutative xa xy val_and_equal_not)
    then have "new_int xb (and (not xva) xvv) = new_int xb 0"
      using eqa xa xy by fastforce
    then have evalSame: "val[(~xa) & y] = new_int xb 0"
      by (simp add: unfoldEq)
    then have "b = xb"
      by (metis assms valid_int_same_bits wf_stamp_def xy y)
    then have "[m,p] \<turnstile> exp[const (IntVal b 0)] \<mapsto> val[new_int xb 0]"
      by (metis assms new_int_zero p(2) stamp_eval_int wf_integerstamp_eval_is_new_int)
    then show ?thesis
      by (metis eqa evalDet evalSame p(2,4) y)
  qed
  done

lemma exp_sign_extend:
  assumes "e = (1 << In) - 1"
  shows   "BinaryExpr BinAnd (UnaryExpr (UnarySignExtend In Out) x) 
                             (ConstantExpr (new_int b e))
                           \<ge> (UnaryExpr (UnaryZeroExtend In Out) x)"
  apply auto
  subgoal premises p for m p va
    proof - 
      obtain va where va: "[m,p] \<turnstile> x \<mapsto> va"
        using p(2) by auto
      then have notUndef: "va \<noteq> UndefVal"
        by (simp add: evaltree_not_undef)
      then have 1: "intval_and (intval_sign_extend In Out va) (IntVal b (take_bit b e)) \<noteq> UndefVal"
        using evalDet p(1) p(2) va by blast
      then have 2: "intval_sign_extend In Out va \<noteq> UndefVal"
        by auto
      then have 21: "(0::nat) < b"
        using eval_bits_1_64 p(4) by blast
      then have 3: "b \<sqsubseteq> (64::nat)"
        using eval_bits_1_64 p(4) by blast
      then have 4: "- ((2::int) ^ b div (2::int)) \<sqsubseteq> sint (signed_take_bit (b - Suc (0::nat)) (take_bit b e))"
        by (simp add: "21" int_power_div_base signed_take_bit_int_greater_eq_minus_exp_word)
      then have 5: "sint (signed_take_bit (b - Suc (0::nat)) (take_bit b e)) < (2::int) ^ b div (2::int)"
        by (simp add: "21" "3" Suc_le_lessD int_power_div_base signed_take_bit_int_less_exp_word)
      then have 6: "[m,p] \<turnstile> UnaryExpr (UnaryZeroExtend In Out)
                 x \<mapsto> intval_and (intval_sign_extend In Out va) (IntVal b (take_bit b e))"
        apply (cases va; simp) 
        apply (simp add: notUndef) defer
        using "2" apply fastforce+
        sorry
      then show ?thesis
        by (metis evalDet p(2) va)
    qed 
  done 

lemma exp_and_neutral:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp b lo hi"
  shows "exp[x & const (new_int b (not 0))] \<ge> x"
  using assms apply auto
  subgoal premises p for m p xa
  proof -
    obtain xb xvv where xv: "[m,p] \<turnstile> x \<mapsto> IntVal xb xvv"
      by (metis p(1,2,3) valid_int wf_stamp_def)
    then have "xb = b"
      by (metis p(1,2) valid_int_same_bits wf_stamp_def xv)
    then show ?thesis
      by (metis evalDet eval_unused_bits_zero intval_and.simps(1) new_int.simps new_int_bin.simps
          p(3) take_bit_eq_mask xv)
  qed
  done

text \<open>Optimisations\<close>

optimization AndEqual: "x & x \<longmapsto> x"
  using exp_and_equal by blast

optimization AndEqualNot: "x & (~x) \<longmapsto> const (new_int b 0)
                           when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  using exp_and_commutative exp_and_equal_not by fastforce

optimization AndSelf: "(~n) & n \<longmapsto> const (new_int b 0)
                       when (stamp_expr n = IntegerStamp b l h \<and> wf_stamp n)"
  using exp_and_equal_not by force

optimization AndSelf2: "n & (~n) \<longmapsto> const (new_int b 0)
                        when (stamp_expr n = IntegerStamp b l h \<and> wf_stamp n)"
  using AndSelf exp_and_commutative by auto

optimization AndShiftConstantRight: "(const x) & y \<longmapsto> y & (const x) when \<not>(is_ConstantExpr y)"
  using exp_and_commutative by blast

optimization AndNots: "(~x) & (~y) \<longmapsto> ~(x | y)"
  apply (simp add: less_SucI size_bin_cycle1_lt_succ_sum) using exp_and_nots by auto

(* TODO need to prove exp_sign_extend *)
optimization AndSignExtend: "exp[(UnaryExpr (UnarySignExtend In Out) x) & const (new_int b e)]
                             \<longmapsto> (UnaryExpr (UnaryZeroExtend In Out) x)
                             when (e = (1 << In) - 1)"
   using exp_sign_extend by simp

optimization AndNeutral: "x & (const (new_int b (not 0))) \<longmapsto> x
                          when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  using exp_and_neutral by auto

optimization AndRightFallThrough: "(x & y) \<longmapsto> y
                                   when (((and (not (IRExpr_down x)) (IRExpr_up y)) = 0))"
  using simple_mask.AndRightFallthrough by blast

optimization AndLeftFallThrough: "(x & y) \<longmapsto> x
                                  when (((and (not (IRExpr_down y)) (IRExpr_up x)) = 0))"
  using simple_mask.AndLeftFallthrough by auto

end (* End of AndPhase *)

end (* End of file *)