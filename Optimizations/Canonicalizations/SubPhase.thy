subsection \<open>SubNode Phase\<close>

theory SubPhase
  imports
    Common
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
  assumes "x = new_int b v \<and> val[x - x] \<noteq> UndefVal"
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
  shows "exp[(x + y) - x] \<ge> exp[y]"
  using exp_sub_after_right_add apply auto 
  using bin_eval.simps(1) bin_eval.simps(3) intval_add_sym unfold_binary
  by (smt (z3) Value.inject(1) diff_eq_eq evalDet eval_unused_bits_zero intval_add.elims 
      intval_sub.elims new_int.simps new_int_bin.simps take_bit_dist_subL)

lemma exp_sub_negative_value:
 "exp[x - (-y)] \<ge> exp[x + y]"
  apply simp using val_sub_negative_value
  by (smt (verit) bin_eval.simps(1) bin_eval.simps(3) evaltree_not_undef 
      unary_eval.simps(2) unfold_binary unfold_unary)


(* wf_stamp definition borrowed from ConditionalPhase *)
definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

(* exp[x - (x - y)] = exp[x - x + y] \<Rightarrow> false *)
lemma exp_sub_then_left_sub:
  assumes "wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi"
  shows "exp[x - (x - y)] \<ge> exp[y]"
  using val_sub_then_left_sub assms
proof -
  have 1: "exp[x - (x - y)] = exp[x - x + y]"
    apply simp
    sorry
  have "exp[x - (x - y)] \<ge> exp[(const (new_int b 0)) + y]"
    sorry
  have "exp[(const IntVal b 0) + y] \<ge> exp[y]"
    sorry
  then show ?thesis
    using "1" by fastforce
qed

text \<open>Optimisations\<close>

optimization SubAfterAddRight: "((x + y) - y) \<longmapsto>  x"
  using exp_sub_after_right_add by blast

optimization SubAfterAddLeft: "((x + y) - x) \<longmapsto>  y"
  using exp_sub_after_right_add2 by blast

optimization SubAfterSubLeft: "((x - y) - x) \<longmapsto>  -y"
   apply auto
  by (metis evalDet unary_eval.simps(2) unfold_unary val_sub_after_left_sub)


optimization SubThenAddLeft: "(x - (x + y)) \<longmapsto> -y"
   apply auto
  by (metis evalDet unary_eval.simps(2) unfold_unary 
      val_sub_then_left_add)

optimization SubThenAddRight: "(y - (x + y)) \<longmapsto> -x"
   apply auto 
  by (metis evalDet intval_add_sym unary_eval.simps(2) unfold_unary 
      val_sub_then_left_add)

optimization SubThenSubLeft: "(x - (x - y)) \<longmapsto> y 
                               when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  using exp_sub_then_left_sub by blast
 

optimization SubtractZero: "(x - (const IntVal b 0)) \<longmapsto> x 
                             when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  apply auto
  by (smt (verit) add.right_neutral diff_add_cancel eval_unused_bits_zero intval_sub.elims 
      intval_word.simps new_int.simps new_int_bin.simps)

(*
optimization SubNegativeConstant: "(x - (const (IntVal b y))) \<longmapsto> 
                                    x + (const (IntVal b y)) 
                                    when (y < 0)"  
  done
*)

(* Strange final subgoal 
   Canonicalization.size y = (0::nat)
*)
optimization SubNegativeValue: "(x - (-y)) \<longmapsto> x + y"  
   defer using exp_sub_negative_value apply simp
  sorry

optimization ZeroSubtractValue: "((const IntVal b 0) - x) \<longmapsto> (-x) 
                                  when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
   apply auto unfolding wf_stamp_def
  by (smt (verit) diff_0 intval_negate.simps(1) intval_sub.elims intval_word.simps 
          new_int_bin.simps unary_eval.simps(2) unfold_unary)

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
  apply (simp add: Suc_lessI size_pos)
   apply simp apply (rule impI; (rule allI)+; rule impI)
  subgoal premises eval for m p v 
  proof -
    obtain b where "\<exists>lo hi. stamp_expr exp[x - x] = IntegerStamp b lo hi"
    using evalSubStamp eval
    by meson
  then show ?thesis sorry
qed
  done


end (* End of SubPhase *)

end (* End of file *)