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
  shows   "val[(x + y) - y] = val[x]"
  using bin_sub_after_right_add 
  using assms apply (cases x; cases y; auto)
  by (metis (full_types) intval_sub.simps(2))

lemma val_sub_after_left_sub:
  assumes "val[(x - y) - x] \<noteq> UndefVal"
  shows   "val[(x - y) - x] = val[-y]"
  using assms apply (cases x; cases y; auto)
  using intval_sub.elims by fastforce

lemma val_sub_then_left_sub:
  assumes "y = new_int b v"
  assumes "val[x - (x - y)] \<noteq> UndefVal"
  shows   "val[x - (x - y)] = val[y]"
  using assms apply (cases x; cases y; auto)
  by (metis (mono_tags) intval_sub.simps(5))

lemma val_subtract_zero:
  assumes "x = new_int b v"
  assumes "intval_sub x (IntVal b 0) \<noteq> UndefVal "
  shows   "intval_sub x (IntVal b 0) = val[x]"
  using assms by (induction x; simp)

lemma val_zero_subtract_value:
  assumes "x = new_int b v"
  assumes "intval_sub (IntVal b 0) x \<noteq> UndefVal "
  shows   "intval_sub (IntVal b 0) x = val[-x]"
  using assms by (induction x; simp)

lemma val_sub_then_left_add:
  assumes "val[x - (x + y)] \<noteq> UndefVal"
  shows   "val[x - (x + y)] = val[-y]"
  using assms apply (cases x; cases y; auto)
  by (metis (mono_tags, lifting) intval_sub.simps(5))

lemma val_sub_negative_value:
  assumes "val[x - (-y)] \<noteq> UndefVal"
  shows   "val[x - (-y)] = val[x + y]"
  using assms by (cases x; cases y; auto)

lemma val_sub_self_is_zero:
  assumes "x = new_int b v \<and> val[x - x] \<noteq> UndefVal"
  shows   "val[x - x] = new_int b 0"
  using assms by (cases x; auto)

lemma val_sub_negative_const:
  assumes "y = new_int b v \<and> val[x - (-y)] \<noteq> UndefVal"
  shows "val[x - (-y)] = val[x + y]"
  using assms by (cases x; cases y; auto)

(* Exp level proofs *)
lemma exp_sub_after_right_add:
  shows "exp[(x + y) - y] \<ge> exp[x]"
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

lemma exp_sub_then_left_sub:
  shows   "exp[x - (x - y)] \<ge> exp[y]"
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
        by (metis evalDet p(2) p(3) p(4) p(5) xa xaa ya)
      then have "val[xaa - ya] \<noteq> UndefVal"
        by auto
      then have "[m,p] \<turnstile> y \<mapsto> val[xa - (xaa - ya)]"
        by (metis "1" Value.exhaust evalDet eval_unused_bits_zero evaltree_not_undef intval_sub.simps(6) intval_sub.simps(7) new_int.simps p(5) val_sub_then_left_sub xa xaa ya)
      then show ?thesis
        by (metis evalDet p(2) p(4) p(5) xa xaa ya)
    qed 
    done

thm_oracles exp_sub_then_left_sub

text \<open>Optimisations\<close>

optimization SubAfterAddRight: "((x + y) - y) \<longmapsto>  x"
  using exp_sub_after_right_add by blast

optimization SubAfterAddLeft: "((x + y) - x) \<longmapsto>  y"
  using exp_sub_after_right_add2 by blast

optimization SubAfterSubLeft: "((x - y) - x) \<longmapsto>  -y"
  apply (metis Suc_lessI add_2_eq_Suc' add_less_cancel_right less_trans_Suc not_add_less1 size_binary_const size_binary_lhs size_binary_rhs size_non_add)
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

optimization SubThenSubLeft: "(x - (x - y)) \<longmapsto> y"
  using size_simps apply simp
  using exp_sub_then_left_sub by blast
 
optimization SubtractZero: "(x - (const IntVal b 0)) \<longmapsto> x 
                             when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  apply auto
  by (smt (verit) add.right_neutral diff_add_cancel eval_unused_bits_zero intval_sub.elims 
      intval_word.simps new_int.simps new_int_bin.simps)

(* Doesn't have any subgoals? *)
(*
optimization SubNegativeConstant: "(x - (const (IntVal b y))) \<longmapsto> 
                                    x + (const (IntVal b y))  when (y < 0)"  
  done
*)

optimization SubNegativeValue: "(x - (-y)) \<longmapsto> x + y"
  apply (metis add_2_eq_Suc' less_SucI less_add_Suc1 not_less_eq size_binary_const size_non_add)
  using exp_sub_negative_value by simp

thm_oracles SubNegativeValue

optimization SubNegativeConstant: "x - (const (intval_negate y)) \<longmapsto> x + (const y)"
   defer
  apply auto sorry

optimization ZeroSubtractValue: "((const IntVal b 0) - x) \<longmapsto> (-x) 
                                  when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  defer
   apply auto unfolding wf_stamp_def
  apply (smt (verit) diff_0 intval_negate.simps(1) intval_sub.elims intval_word.simps 
          new_int_bin.simps unary_eval.simps(2) unfold_unary)
  sorry

fun forPrimitive :: "Stamp \<Rightarrow> int64 \<Rightarrow> IRExpr" where
  "forPrimitive (IntegerStamp b lo hi) v = ConstantExpr (if take_bit b v = v then (IntVal b v) else UndefVal)" |
  "forPrimitive _ _ = ConstantExpr UndefVal"

(*
optimization SubSelfIsZero: "(x - x) \<longmapsto> const IntVal b 0 when 
                      (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
   apply auto
   apply (meson less_add_same_cancel1 less_trans_Suc size_pos)
  by (smt (verit) Value.inject(1) eq_iff_diff_eq_0 evalDet intval_sub.elims new_int.elims 
      new_int_bin.elims take_bit_of_0 unfold_const validDefIntConst valid_stamp.simps(1) 
      valid_value.simps(1) wf_stamp_def)
*)

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


end (* End of SubPhase *)

end (* End of file *)
