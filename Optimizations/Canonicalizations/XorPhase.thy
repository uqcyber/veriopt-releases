subsection \<open>XorNode Phase\<close>

theory XorPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase XorNode
  terminating size
begin

(* Word level proofs *)
lemma bin_xor_self_is_false:
 "bin[x \<oplus> x] = 0"
  by simp

lemma bin_xor_commute:
  fixes y::int64
  fixes x::int64
  shows "xor (not x) (not y) = xor y x"
  by (simp add: xor.commute)

lemma bin_eliminate_redundant_false:
 "bin[x \<oplus> 0] = bin[x]"
  by simp

lemma bin_xor_cancel: 
  shows "bin[xor (~x) (~y)] = bin[xor x y]"
  by simp

(* Value level proofs *)
lemma val_xor_self_is_false:
  assumes "val[x \<oplus> x] \<noteq> UndefVal"
  shows "val_to_bool (val[x \<oplus> x]) = False"
  by (cases x; auto simp: assms)

lemma val_xor_self_is_false_2:
  assumes "val[x \<oplus> x] \<noteq> UndefVal"
  and     "x = IntVal 32 v"
  shows "val[x \<oplus> x] = bool_to_val False"
  by (auto simp: assms)

(* Not sure if I need this; Optimization uses ConstantExpr False which is IntVal32 0 *)
lemma val_xor_self_is_false_3:
  assumes "val[x \<oplus> x] \<noteq> UndefVal \<and> x = IntVal 64 v"
  shows "val[x \<oplus> x] = IntVal 64 0"
  by (auto simp: assms)

lemma val_eliminate_redundant_false:
  assumes "x = new_int b v"
  assumes "val[x \<oplus> (bool_to_val False)] \<noteq> UndefVal"
  shows   "val[x \<oplus> (bool_to_val False)] = x"
  using assms by (auto; meson)

lemma val_eliminate_redundant_zero:
  assumes "x = new_int b xv"
  shows "val[x \<oplus> (IntVal b 0)] = val[x]"
  using assms by (cases x; auto)

lemma val_xor_cancel:
  assumes "x = IntVal 64 v"
  assumes "y = IntVal 64 e"
  assumes "val[\<not>x] \<noteq> UndefVal"
  assumes "val[\<not>y] \<noteq> UndefVal"
  shows "val[(\<not>x) \<oplus> \<not>y] = val[x \<oplus> y]"
  using assms apply (cases x; cases y; auto)
  by (metis (no_types, lifting) bin_xor_commute take_bit_xor word_bw_comms(3))

lemma XorInverseVal:
  assumes "n = IntVal 32 v"
  shows "val[n \<oplus> ~n] \<approx> new_int 32 (-1)"
  apply (auto simp: assms)
  by (metis (no_types, opaque_lifting) bit.compl_zero bit.xor_compl_right bit.xor_self take_bit_xor
      mask_eq_take_bit_minus_one)

lemma val_xor_inverse:
  assumes "x = new_int b xv"
  assumes "val[x \<oplus> ~x] \<noteq> UndefVal"
  shows "val[x \<oplus> ~x] = val[new_int b (not 0)]"
  using assms apply (cases x; auto)
  by (metis (no_types, opaque_lifting) bin_xor_self_is_false bit.xor_compl_right le_refl min.idem
      take_bit_not_mask_eq_0 take_bit_not_take_bit take_bit_of_mask take_bit_xor word_not_not)

(* Exp level proofs *)
lemma exp_xor_self_is_false:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp b xl xh"
  shows   "exp[x \<oplus> x] \<ge> exp[const (IntVal b 0)]"
  using assms apply auto
  subgoal premises p for m p xa ya
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(3) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis evalDet evaltree_not_undef intval_is_null.cases intval_xor.simps(3) p(1,3,5) xv
          valid_value.simps(11,12) wf_stamp_def)
    have "[m,p] \<turnstile> exp[const (IntVal b 0)] \<mapsto> val[IntVal b 0]"
      by (metis new_int_zero_is_intval p(1,2,4) stamp_eval_int wf_integerstamp_eval_is_new_int)
    then show ?thesis
      by (metis evalDet p(1,2,3,4) val_xor_self valid_int_same_bits wf_stamp_def xv xvv)
  qed
  done

lemma exp_eliminate_redundant_false:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp b xl xh"
  shows "exp[x \<oplus> (const (IntVal b 0))] \<ge> exp[x]"
  using assms apply auto
  subgoal premises p for m p xa
    proof -
      obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
        using p(3) by auto
      obtain xb xvv where xvv: "xv = new_int xb xvv"
        using p(1,2) wf_integerstamp_eval_is_new_int xv by blast
      have "val[xv \<oplus> (IntVal b 0)] = val[xv]"
        using p(1,2) stamp_eval_same_bits val_eliminate_redundant_zero xv xvv by blast
      then show ?thesis
        by (metis evalDet p(3) xv)
    qed
  done

lemma exp_xor_cancel:
  shows "exp[(\<not>x) \<oplus> \<not>y] \<ge> exp[x \<oplus> y]"
  apply auto subgoal premises p for m p xa xb
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(2) by auto
    obtain b xv where xv: "xa = IntVal b xv"
      by (metis Value.exhaust evalDet evaltree_not_undef intval_not.simps(3,4,5) p(2,3) xa)
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using p(4) by auto
    obtain b yv where yv: "ya = IntVal b yv"
      by (metis constantAsStamp.cases evalDet evaltree_not_undef intval_not.simps(3,4,5) p(4,5) ya)
    then have "val[(\<not>xa) \<oplus> (\<not>ya)] \<noteq> UndefVal"
      by (metis evalDet p(1,2,4) xa ya)
    then have unfoldXor: "val[(\<not>xa) \<oplus> (\<not>ya)] = new_int b (xor xv yv)"
      using xv yv apply simp
      by (metis (no_types, opaque_lifting) bit.xor_compl_left bit.xor_compl_right take_bit_xor
          word_not_not)
    then have "[m,p] \<turnstile> exp[x \<oplus> y] \<mapsto> new_int b (xor xv yv)"
      by (metis BinaryExpr Value.distinct(1) bin_eval.simps(8) xv yv intval_not.simps(1) xa ya
          intval_xor.simps(1) new_int.simps new_int_bin.simps)
    then show ?thesis
      by (metis evalDet p(2,4) unfoldXor xa ya)
  qed
  done

lemma exp_xor_inverse:
  assumes "stamp_expr x = IntegerStamp b l h"
  assumes "wf_stamp x"
  shows "exp[x \<oplus> ~x] \<ge> exp[const (new_int b (not 0))]"
  using assms apply auto
  subgoal premises p for m p xa xaa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(3) by blast
    obtain xb xvv where xvv: "xv = new_int xb xvv"
      using p(1,2) wf_integerstamp_eval_is_new_int xv by blast
    have width: "xb = b"
      using p(1,2) stamp_eval_same_bits xv xvv by blast
    have rhsEval: "[m,p] \<turnstile> exp[const (new_int b (not 0))] \<mapsto> val[new_int b (not 0)]"
      using p(1,2) stamp_eval_int xv xvv by blast
    have evalEq: "val[xv \<oplus> ~xv] = val[new_int b (not 0)]"
      using val_xor_inverse width xvv by auto
    then show ?thesis
      by (metis (no_types, opaque_lifting) dual_order.refl evalDet neg_one.elims neg_one_value xv
          new_int.simps p(3,5) rhsEval take_bit_not_mask_eq_0 take_bit_not_take_bit word_not_not)
  qed
  done

text \<open>Optimisations\<close>

optimization XorSelfIsFalse: "(x \<oplus> x) \<longmapsto> const (IntVal b 0)
                              when (wf_stamp x \<and> stamp_expr x = IntegerStamp b xl xh)"
  apply (metis Suc_lessI bot_nat_0.not_eq_extremum less_one size_binary_rhs size_pos)
  using exp_xor_self_is_false by blast

optimization XorShiftConstantRight: "((const x) \<oplus> y) \<longmapsto> y \<oplus> (const x) when \<not>(is_ConstantExpr y)"
  using size_flip_binary val_xor_commutative by auto

optimization EliminateRedundantFalse: "(x \<oplus> (const (IntVal b 0))) \<longmapsto> x
                                       when (wf_stamp x \<and> stamp_expr x = IntegerStamp b xl xh)"
  using exp_eliminate_redundant_false by auto

(* BW: this doesn't seem right *)
(* Doesn't have any subgoals *)
(*
optimization MaskOutRHS: "(x \<oplus> y) \<longmapsto> ~x
                          when (is_ConstantExpr y
                             \<and> (stamp_expr (BinaryExpr BinXor x y) = IntegerStamp stampBits l h) 
                             \<and> (BinaryExpr BinAnd y (ConstantExpr (new_int stampBits (not 0))) 
                                                   = ConstantExpr (new_int stampBits (not 0))))"
  sorry
*)

optimization XorNot: "((~x) \<oplus> (~y)) \<longmapsto> (x \<oplus> y) when \<not>(is_ConstantExpr y)"
  using size_non_add apply (simp add: less_Suc_eq) using exp_xor_cancel by blast

optimization XorInverse: "(x \<oplus> ~x) \<longmapsto> (const (new_int b (not 0)))
                          when (stamp_expr x = IntegerStamp b l h \<and> wf_stamp x)"
  using exp_xor_inverse by force

optimization XorInverseCommute: "((~x) \<oplus> x) \<longmapsto> (const (new_int b (not 0)))
                                 when (stamp_expr x = IntegerStamp b l h \<and> wf_stamp x)"
  apply (metis bot_nat_0.not_eq_extremum less_Suc0 linorder_neqE_nat size_binary_rhs size_pos)
  using XorInverse exp_xor_commutative by auto

end (* End of XorPhase *)

end (* End of file *)
