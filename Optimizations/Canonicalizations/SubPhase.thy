theory SubPhase
  imports
    Common
begin

section \<open>Optimizations for Sub Nodes\<close>

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
  shows "val[(x + y) - (y)] = val[x]"
  using bin_sub_after_right_add 
  using assms apply (cases x; cases y; auto)
  by (metis (full_types) intval_sub.simps(2))

lemma val_sub_after_left_sub:
  assumes "val[(x - y) - x] \<noteq> UndefVal"
  shows "val[(x - y) - x] = val[-y]"
  using assms apply (cases x; cases y; auto)
  using intval_sub.elims by fastforce

lemma val_sub_then_left_sub:
  assumes "y = new_int b v"
  assumes "val[x - (x - y)] \<noteq> UndefVal"
  shows "val[x - (x - y)] = val[y]"
  using assms apply (cases x; cases y; auto)
  by (metis (mono_tags) intval_sub.simps(5))

lemma val_subtract_zero:
  assumes "x = new_int b v"
  assumes "intval_sub x (IntVal 32 0) \<noteq> UndefVal "
  shows "intval_sub x (IntVal 32 0) = val[x]"
  using assms apply (induction x; simp)
  by presburger

lemma val_zero_subtract_value:
  assumes "x = new_int b v"
  assumes "intval_sub (IntVal 32 0) x \<noteq> UndefVal "
  shows "intval_sub (IntVal 32 0) x = val[-x]"
  using assms apply (induction x; simp)
  by presburger

lemma val_zero_subtract_value_64:
  assumes "x = new_int b v"
  assumes "intval_sub (IntVal 64 0) x \<noteq> UndefVal "
  shows "intval_sub (IntVal 64 0) x = val[-x]"
  using assms apply (induction x; simp)
  by presburger

lemma val_sub_then_left_add:
  assumes "val[x - (x + y)] \<noteq> UndefVal"
  shows "val[x - (x + y)] = val[-y]"
  using assms apply (cases x; cases y; auto)
  by (metis (mono_tags, lifting) intval_sub.simps(5))

lemma val_sub_negative_value:
  assumes "val[x - (- y)] \<noteq> UndefVal"
  shows "val[x - (-y)] = val[x + y]"
  using assms by (cases x; cases y; auto)

lemma val_sub_self_is_zero:
  assumes "x = new_int b v \<and> x - x \<noteq> UndefVal"
  shows "val[x - x] = new_int b 0"
  using assms by (cases x; auto)

lemma val_sub_negative_const:
  assumes "y = new_int b v \<and> val[x - (-y)] \<noteq> UndefVal"
  shows "val[x - (- y)] = val[x + y]"
  using assms by (cases x; cases y; auto)


(* Expression level proofs *)
lemma exp_sub_after_right_add:
  shows "exp[(x+y)-y] \<ge> exp[x]"
  apply auto using val_sub_after_right_add_2
  using evalDet eval_unused_bits_zero intval_add.elims new_int.simps
  by (smt (verit)) 

lemma exp_sub_after_right_add2:
  shows "exp[(x+y)-x] \<ge> exp[y]"
  using exp_sub_after_right_add apply auto 
  using bin_eval.simps(1) bin_eval.simps(3) intval_add_sym unfold_binary
  by (smt (z3) Value.inject(1) diff_eq_eq evalDet eval_unused_bits_zero intval_add.elims 
      intval_sub.elims new_int.simps new_int_bin.simps take_bit_dist_subL)

lemma exp_sub_negative_value:
 "exp[x - (-y)] \<ge> exp[x + y]"
  apply simp using val_sub_negative_value
  by (smt (verit) bin_eval.simps(1) bin_eval.simps(3) evaltree_not_undef minus_Value_def 
      unary_eval.simps(2) unfold_binary unfold_unary)

lemma exp_sub_then_left_sub:
  "exp[x - (x - y)] \<ge> exp[y]"
proof -
  have "exp[x - (-y)] \<ge> exp[x + y]"
    using exp_sub_negative_value  by simp
  then have "exp[x - (x - y)] \<ge> exp[x - x + y]"
    using exp_sub_negative_value sorry
  then show ?thesis
    sorry
  qed

(* Optimizations *)
optimization SubAfterAddRight: "((x + y) - y) \<longmapsto>  x"
  using exp_sub_after_right_add by blast

optimization SubAfterAddLeft: "((x + y) - x) \<longmapsto>  y"
  using exp_sub_after_right_add2 by blast

optimization SubAfterSubLeft: "((x - y) - x) \<longmapsto>  -y"
   apply auto 
   apply (metis One_nat_def less_add_one less_numeral_extra(3) less_one linorder_neqE_nat 
          pos_add_strict size_pos)
  by (metis evalDet unary_eval.simps(2) unfold_unary val_sub_after_left_sub)


optimization SubThenAddLeft: "(x - (x + y)) \<longmapsto> -y"
   apply auto 
   apply (simp add: Suc_lessI one_is_add) 
  by (metis evalDet unary_eval.simps(2) unfold_unary 
      val_sub_then_left_add)

optimization SubThenAddRight: "(y - (x + y)) \<longmapsto> -x"
   apply auto 
   apply (metis less_1_mult less_one linorder_neqE_nat mult.commute mult_1 numeral_1_eq_Suc_0 
          one_eq_numeral_iff one_less_numeral_iff semiring_norm(77) size_pos zero_less_iff_neq_zero)
  by (metis evalDet intval_add_sym unary_eval.simps(2) unfold_unary 
      val_sub_then_left_add)

optimization SubThenSubLeft: "(x - (x - y)) \<longmapsto> y"
  using val_sub_then_left_sub sledgehammer sorry (*
   apply auto
  by (metis evalDet val_sub_then_left_sub)*)


(* wf_stamp definition borrowed from ConditionalPhase *)
definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

optimization SubtractZero: "(x - (const IntVal b 0)) \<longmapsto> x 
                             when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  apply auto
  by (smt (verit) add.right_neutral diff_add_cancel eval_unused_bits_zero intval_sub.elims 
      intval_word.simps new_int.simps new_int_bin.simps)


(* Ln 146 rewrite, 32-bit *)(*
optimization sub_negative_const2: "(x - (const (intval_negate (IntVal32 y)))) \<longmapsto> 
                                    x + (const (IntVal32 y)) 
                                    when (y < 0)"
  done 

(* Ln 146 rewrite, 64-bit *)
optimization sub_negative_const2_64: "(x - (const (intval_negate (IntVal64 y)))) \<longmapsto> 
                                       x + (const (IntVal64 y)) 
                                       when (y < 0)"
   apply auto
  done *)

optimization ZeroSubtractValue: "((const IntVal b 0) - x) \<longmapsto> (-x) when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  apply auto unfolding wf_stamp_def defer
  apply (smt (verit) diff_0 intval_negate.simps(1) intval_sub.elims intval_word.simps new_int_bin.simps unary_eval.simps(2) unfold_unary)
  sorry (* very odd goal produced *)

fun forPrimitive :: "Stamp \<Rightarrow> int64 \<Rightarrow> IRExpr" where
  "forPrimitive (IntegerStamp b lo hi) v = ConstantExpr (IntVal b v)" |
  "forPrimitive _ _ = ConstantExpr UndefVal"

lemma forPrimitive_size: "size (forPrimitive s v) = 1"
  by (cases s; auto)

lemma forPrimitive_eval: 
  assumes "valid_value (IntVal b v) s"
  assumes "s = IntegerStamp b lo hi"
  shows "[m, p] \<turnstile> forPrimitive s v \<mapsto> (IntVal b v)"
  using assms evaltree.ConstantExpr
  by simp

optimization SubSelfIsZero: "(x - x) \<longmapsto> forPrimitive (stamp_expr x) 0 when (wf_stamp x)"
  unfolding forPrimitive_size
  using IRExpr.disc(42) size_non_const apply blast
   apply simp_all using forPrimitive_eval unfolding wf_stamp_def sorry
(*  
  apply (meson less_add_same_cancel1 less_trans_Suc size_pos)
  by (smt (verit) Value.inject(1) eq_iff_diff_eq_0 evalDet intval_sub.elims new_int.elims new_int_bin.elims take_bit_of_0 unfold_const validDefIntConst valid_stamp.simps(1) valid_value.simps(1) wf_stamp_def)
*)

end (* End of SubPhase *)

end (* End of file *)