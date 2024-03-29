subsection \<open>SubNode Phase\<close>

theory SubPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase SubNode
  terminating size
begin

(* Word level proofs *)
lemma bin_sub_after_right_add:
  shows "((x::('a::len) word) + (y::('a::len) word)) - y = x"
  by simp

lemma sub_self_is_zero:
  shows "(x::('a::len) word) - x = 0"
  by simp

lemma bin_sub_then_left_add:
  shows "(x::('a::len) word) - (x + (y::('a::len) word)) = -y"
  by simp

lemma bin_sub_then_left_sub:
  shows "(x::('a::len) word) - (x - (y::('a::len) word)) = y"
  by simp

lemma bin_subtract_zero:
  shows "(x :: 'a::len word) - (0 :: 'a::len word) = x"
  by simp

lemma bin_sub_negative_value:
 "(x :: ('a::len) word) - (-(y :: ('a::len) word)) = x + y"
  by simp

lemma bin_sub_self_is_zero:
 "(x :: ('a::len) word) - x = 0"
  by simp

lemma bin_sub_negative_const:
"(x :: 'a::len word) - (-(y :: 'a::len word)) = x + y"
  by simp

(* Value level proofs *)
lemma val_sub_after_right_add_2:
  assumes "x = new_int b v"
  assumes "val[(x + y) - y] \<noteq> UndefVal"
  shows   "val[(x + y) - y] = x"
  using assms apply (cases x; cases y; auto)
  by (metis (full_types) intval_sub.simps(2))

lemma val_sub_after_left_sub:
  assumes "val[(x - y) - x] \<noteq> UndefVal"
  shows   "val[(x - y) - x] = val[-y]"
  using assms intval_sub.elims apply (cases x; cases y; auto)
  by fastforce

lemma val_sub_then_left_sub:
  assumes "y = new_int b v"
  assumes "val[x - (x - y)] \<noteq> UndefVal"
  shows   "val[x - (x - y)] = y"
  using assms apply (cases x; auto)
  by (metis (mono_tags) intval_sub.simps(6))

lemma val_subtract_zero:
  assumes "x = new_int b v"
  assumes "val[x - (IntVal b 0)] \<noteq> UndefVal"
  shows   "val[x - (IntVal b 0)] = x"
  by (cases x; simp add: assms)

lemma val_zero_subtract_value:
  assumes "x = new_int b v"
  assumes "val[(IntVal b 0) - x] \<noteq> UndefVal"
  shows   "val[(IntVal b 0) - x] = val[-x]"
  by (cases x; simp add: assms)

lemma val_sub_then_left_add:
  assumes "val[x - (x + y)] \<noteq> UndefVal"
  shows   "val[x - (x + y)] = val[-y]"
  using assms apply (cases x; cases y; auto)
  by (metis (mono_tags, lifting) intval_sub.simps(6))

lemma val_sub_negative_value:
  assumes "val[x - (-y)] \<noteq> UndefVal"
  shows   "val[x - (-y)] = val[x + y]"
  by (cases x; cases y; simp add: assms)

lemma val_sub_self_is_zero:
  assumes "x = new_int b v \<and> val[x - x] \<noteq> UndefVal"
  shows   "val[x - x] = new_int b 0"
  by (cases x; simp add: assms)

lemma val_sub_negative_const:
  assumes "y = new_int b v \<and> val[x - (-y)] \<noteq> UndefVal"
  shows "val[x - (-y)] = val[x + y]"
  by (cases x; simp add: assms)

(* Exp level proofs *)
lemma exp_sub_after_right_add:
  shows "exp[(x + y) - y] \<ge> x"
  apply auto
  subgoal premises p for m p ya xa yaa
  proof-
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(3) by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis Value.exhaust evalDet evaltree_not_undef intval_add.simps(3,4,5) intval_sub.simps(2)
          p(2,3) xv)
    obtain yb yvv where yvv: "yv = IntVal yb yvv"
      by (metis evalDet evaltree_not_undef intval_add.simps(7,8,9) intval_logic_negation.cases yv
          intval_sub.simps(2) p(2,4))
    then have lhsDefined: "val[(xv + yv) - yv] \<noteq> UndefVal"
      using xvv yvv apply (cases xv; cases yv; auto)
      by (metis evalDet intval_add.simps(1) p(3,4,5) xv yv)
     then show ?thesis
       by (metis \<open>\<And>thesis. (\<And>(xb) xvv. (xv) = IntVal xb xvv \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> evalDet xv yv
           eval_unused_bits_zero lhsDefined new_int.simps p(1,3,4) val_sub_after_right_add_2)
  qed
  done

lemma exp_sub_after_right_add2:
  shows "exp[(x + y) - x] \<ge> y"
  using exp_sub_after_right_add apply auto
  by (metis bin_eval.simps(1,2) intval_add_sym unfold_binary)

lemma exp_sub_negative_value:
 "exp[x - (-y)] \<ge> exp[x + y]"
  apply auto
  subgoal premises p for m p xa ya
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p(3) by auto
    then have rhsEval: "[m,p] \<turnstile> exp[x + y] \<mapsto> val[xv + yv]"
      by (metis bin_eval.simps(1) evalDet p(1,2,3) unfold_binary val_sub_negative_value xv)
    then show ?thesis
      by (metis evalDet p(1,2,3) val_sub_negative_value xv yv)
  qed
  done

lemma exp_sub_then_left_sub:
  "exp[x - (x - y)] \<ge> y"
  using val_sub_then_left_sub apply auto
  subgoal premises p for m p xa xaa ya
    proof- 
      obtain xa where xa: "[m, p] \<turnstile> x \<mapsto> xa"
        using p(2) by blast
      obtain ya where ya: "[m, p] \<turnstile> y \<mapsto> ya"
        using p(5) by auto
      obtain xaa where xaa: "[m, p] \<turnstile> x \<mapsto> xaa"
        using p(2) by blast
      have 1: "val[xa - (xaa - ya)] \<noteq> UndefVal"
        by (metis evalDet p(2,3,4,5) xa xaa ya)
      then have "val[xaa - ya] \<noteq> UndefVal"
        by auto
      then have "[m, p] \<turnstile> y \<mapsto> val[xa - (xaa - ya)]"
        by (metis "1" Value.exhaust eval_unused_bits_zero evaltree_not_undef xa xaa ya new_int.simps
            intval_sub.simps(6,7,8,9) evalDet val_sub_then_left_sub)
      then show ?thesis
        by (metis evalDet p(2,4,5) xa xaa ya)
    qed 
  done

thm_oracles exp_sub_then_left_sub

lemma SubtractZero_Exp:
  "exp[(x - (const IntVal b 0))] \<ge> x"
  apply auto
  subgoal premises p for m p xa
  proof-
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis array_length.cases evalDet evaltree_not_undef intval_sub.simps(3,4,5) p(1,2) xv)
    then have widthSame: "xb=b"
      by (metis evalDet intval_sub.simps(1) new_int_bin.simps p(1) p(2) xv)
    then have unfoldSub: "val[xv - (IntVal b 0)] = (new_int xb (xvv-0))"
      by (simp add: xvv)
    then have rhsSame: "val[xv] = (new_int xb (xvv))"
      using eval_unused_bits_zero xv xvv by auto
    then show ?thesis
      by (metis diff_zero evalDet p(1) unfoldSub xv)
  qed
  done

lemma ZeroSubtractValue_Exp:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "\<not>(is_ConstantExpr x)"
  shows "exp[(const IntVal b 0) - x] \<ge> exp[-x]"
  using assms apply auto
  subgoal premises p for m p xa
  proof-
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(4) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis constantAsStamp.cases evalDet evaltree_not_undef intval_sub.simps(7,8,9) p(4,5) xv)
    then have unfoldSub: "val[(IntVal b 0) - xv] = (new_int xb (0-xvv))"
      by (metis intval_sub.simps(1) new_int_bin.simps p(1,2) valid_int_same_bits wf_stamp_def xv)
    then show ?thesis
      by (metis UnaryExpr intval_negate.simps(1) p(4,5) unary_eval.simps(2) verit_minus_simplify(3)
          evalDet xv xvv)
  qed
  done

text \<open>Optimisations\<close>

optimization SubAfterAddRight: "((x + y) - y) \<longmapsto>  x"
  using exp_sub_after_right_add by blast

optimization SubAfterAddLeft: "((x + y) - x) \<longmapsto>  y"
  using exp_sub_after_right_add2 by blast

optimization SubAfterSubLeft: "((x - y) - x) \<longmapsto>  -y"
  by (smt (verit) Suc_lessI add_2_eq_Suc' add_less_cancel_right less_trans_Suc not_add_less1 evalDet
      size_binary_const size_binary_lhs size_binary_rhs size_non_add BinaryExprE bin_eval.simps(2)
      le_expr_def unary_eval.simps(2) unfold_unary val_sub_after_left_sub)+

optimization SubThenAddLeft: "(x - (x + y)) \<longmapsto> -y"
   apply auto
  by (metis evalDet unary_eval.simps(2) unfold_unary val_sub_then_left_add)

optimization SubThenAddRight: "(y - (x + y)) \<longmapsto> -x"
   apply auto
  by (metis evalDet intval_add_sym unary_eval.simps(2) unfold_unary val_sub_then_left_add)

optimization SubThenSubLeft: "(x - (x - y)) \<longmapsto> y"
  using size_simps exp_sub_then_left_sub by auto
 
optimization SubtractZero: "(x - (const IntVal b 0)) \<longmapsto> x"
  using SubtractZero_Exp by fast

thm_oracles SubtractZero

(* Doesn't have any subgoals? *)
(*
optimization SubNegativeConstant: "(x - (const (IntVal b y))) \<longmapsto> 
                                    x + (const (IntVal b y))  when (y < 0)"  
  done
*)

optimization SubNegativeValue: "(x - (-y)) \<longmapsto> x + y"
  apply (metis add_2_eq_Suc' less_SucI less_add_Suc1 not_less_eq size_binary_const size_non_add)
  using exp_sub_negative_value by blast

thm_oracles SubNegativeValue

lemma negate_idempotent:
  assumes "x = IntVal b v \<and> take_bit b v = v"
  shows "x = val[-(-x)]"
  by (auto simp: assms is_IntVal_def)

(*
lemma remove_sub_preserve_take_bit:
  fixes v :: "64 word"
  assumes "b > 0 \<and> b \<le> 64"
  assumes "take_bit b (-v) = -v"
  shows "take_bit b v = v"
  using assms sorry

value "-1::64 word"
value "take_bit 64 (-1)::64 word"
value "take_bit 64 (-(-1))::64 word"

(* if sign extend take bits of b v get back v *)

lemma valid_sub_const:
  assumes "y = IntVal b v \<and> b > 0"
  assumes "valid_value (val[-y]) (constantAsStamp (val[-y]))"
  shows "valid_value y (constantAsStamp y)"
  using assms apply (cases y; auto)
  apply (simp add: int_power_div_base signed_take_bit_int_greater_eq_minus_exp_word)
  apply (metis (no_types, opaque_lifting) One_nat_def Suc_diff_Suc Suc_le_lessD cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel gr0_conv_Suc lessI less_imp_le_nat signed_take_bit_int_less_exp_word size64 size_word.rep_eq upper_bounds_equiv)
  apply (metis One_nat_def Suc_less_eq Suc_pred le_imp_less_Suc signed_take_bit_int_greater_eq_minus_exp_word size64 upper_bounds_equiv wsst_TYs(3))
  apply (metis One_nat_def Suc_le_lessD Suc_pred signed_take_bit_int_less_exp_word size64 upper_bounds_equiv wsst_TYs(3))
  using remove_sub_preserve_take_bit 
  sorry
  (* (smt (verit) Groups.add_ac(2) One_nat_def Suc_diff_Suc Suc_less_eq Suc_pred add.inverse_inverse add_Suc_right bit_last_iff bit_take_bit_iff bot_nat_0.not_eq_extremum cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel diff_zero gr0_conv_Suc int_signed_value.simps intval_word.simps len_gt_0 lessI less_imp_diff_less less_imp_le_nat less_numeral_extra(1) linorder_not_le mask_1 mask_eq_take_bit_minus_one nat.simps(1) nat.simps(3) neg_one.elims neg_one_signed neg_one_value new_int_take_bits not_less numeral.simps(2) numeral_eq_Suc numerals(2) one_le_numeral order_le_less order_trans plus_nat.simps(2) remove_sub_preserve_take_bit signed_take_bit_take_bit size64 take_bit_length_eq wsst_TYs(3) zero_le zero_le_numeral)
*)

lemma unnegated_rhs_evals:
  assumes "[m, p] \<turnstile> exp[const val[-y]] \<mapsto> v"
  shows "[m, p] \<turnstile> exp[const val[y]] \<mapsto> intval_negate v"
proof -
  obtain b vv where vv: "[m, p] \<turnstile> exp[const val[-y]] \<mapsto> IntVal b vv"
    using assms
    by (metis evaltree_not_undef intval_negate.elims new_int.elims unfold_const)
  then have "take_bit b vv = vv"
    by (simp add: eval_unused_bits_zero)
  then have "v = val[-(-v)]"
    using vv
    by (metis assms negate_idempotent unfold_const)
  then obtain yv where yv: "[m, p] \<turnstile> exp[const val[y]] \<mapsto> IntVal b yv"
    using vv apply auto using evaltree.ConstantExpr valid_sub_const
    by (metis Value.distinct(1) Value.inject(1) eval_bits_1_64 intval_negate.elims new_int.simps)
  then show ?thesis
    using assms apply auto
    using yv by fastforce
qed

optimization SubNegativeConstant: "x - (const (val[-y])) \<longmapsto> x + (const y)"
   defer
   apply simp apply ((rule allI)+; rule impI)
  subgoal premises eval for m p v
  proof -
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
      using eval by auto
    obtain yv where yv: "[m, p] \<turnstile> exp[const (val[-y])] \<mapsto> intval_negate yv"
      using eval by auto
    obtain lhs where lhsdef: "[m, p] \<turnstile> exp[x - (const (val[-y]))] \<mapsto> lhs"
      using eval by auto
    then have lhs: "lhs = val[xv - (-yv)]"
      by (metis BinaryExprE bin_eval.simps(3) evalDet xv yv)
    obtain rhs where rhsdef: "[m, p] \<turnstile> exp[x + (const y)] \<mapsto> rhs"
      using eval unnegated_rhs_evals
      by (metis EvalTreeE(1) bin_eval.simps(1) bin_eval.simps(3) unfold_binary val_sub_negative_value)
    then have rhs: "rhs = val[xv + yv]"
      by (metis BinaryExprE EvalTreeE(1) bin_eval.simps(1) evalDet unnegated_rhs_evals xv yv)
    have "lhs = rhs"
      using val_sub_negative_value lhs rhs
      by (metis bin_eval.simps(3) eval evalDet unfold_binary xv yv)
    then show ?thesis
      by (metis eval evalDet lhsdef rhsdef)
  qed
  sorry
*)

(*Additional check for not constant for termination *)
optimization ZeroSubtractValue: "((const IntVal b 0) - x) \<longmapsto> (-x) 
                                  when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and> \<not>(is_ConstantExpr x))"
  using size_flip_binary ZeroSubtractValue_Exp by simp+

(*
fun forPrimitive :: "Stamp \<Rightarrow> int64 \<Rightarrow> IRExpr" where
  "forPrimitive (IntegerStamp b lo hi) v = ConstantExpr (if take_bit b v = v then (IntVal b v) else UndefVal)" |
  "forPrimitive _ _ = ConstantExpr UndefVal"

lemma unfold_forPrimitive:
  "forPrimitive s v = ConstantExpr (if is_IntegerStamp s \<and> take_bit (stp_bits s) v = v then (IntVal (stp_bits s) v) else UndefVal)"
  by (cases s; auto) 

lemma forPrimitive_size[size_simps]: "size (forPrimitive s v) = 1"
  by (cases s; auto)

lemma forPrimitive_eval: 
  (*assumes "valid_value (IntVal b v) s"*)
  assumes "s = IntegerStamp b lo hi"
  assumes "take_bit b v = v"
  shows "[m, p] \<turnstile> forPrimitive s v \<mapsto> (IntVal b v)"
  unfolding unfold_forPrimitive using assms apply auto
  apply (rule evaltree.ConstantExpr)
  sorry

lemma evalSubStamp:
  assumes "[m, p] \<turnstile> exp[x - y] \<mapsto> v"
  assumes "wf_stamp exp[x - y]"
  shows "\<exists>b lo hi. stamp_expr exp[x - y] = IntegerStamp b lo hi"
proof -
  have "valid_value v (stamp_expr exp[x - y])"
    using assms unfolding wf_stamp_def by auto
  then have "stamp_expr exp[x - y] \<noteq> IllegalStamp"
    by force
  then show ?thesis
    unfolding stamp_expr.simps using stamp_binary.simps
    by (smt (z3) stamp_binary.elims unrestricted_stamp.simps(2))
qed


lemma evalSubArgsStamp:
  assumes "[m, p] \<turnstile> exp[x - y] \<mapsto> v"
  assumes "\<exists>lo hi. stamp_expr exp[x - y] = IntegerStamp b lo hi"
  shows "\<exists>lo hi. stamp_expr exp[x] = IntegerStamp b lo hi"
  using assms sorry

optimization SubSelfIsZero: "(x - x) \<longmapsto> forPrimitive (stamp_expr exp[x - x]) 0 when ((wf_stamp x) \<and> (wf_stamp exp[x - x]))"
  using size_non_const apply fastforce
   apply simp apply (rule impI; (rule allI)+; rule impI)
  subgoal premises eval for m p v 
  proof -
    obtain b where "\<exists>lo hi. stamp_expr exp[x - x] = IntegerStamp b lo hi"
    using evalSubStamp eval
    by meson
  then show ?thesis sorry
qed
  done
*)

optimization SubSelfIsZero: "(x - x) \<longmapsto> const IntVal b 0 when 
                      (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  using size_non_const apply auto
  by (smt (verit) wf_value_def ConstantExpr  eval_bits_1_64 eval_unused_bits_zero new_int.simps
      take_bit_of_0 val_sub_self_is_zero validDefIntConst valid_int wf_stamp_def One_nat_def
      evalDet)

end (* End of SubPhase *)

end (* End of file *)
