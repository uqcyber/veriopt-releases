subsection \<open>SubNode Phase\<close>

theory SubPhase
  imports
    Common
    Proofs.StampEvalThms
begin

(* SubNode size calculation
   - Due to subtraction not being commutative, some optimisations prefer to remove it even if the
     resultant expression is the same size, so we make subtraction slightly larger.
*)
fun sub_size :: "IRExpr \<Rightarrow> nat" where
  "sub_size (UnaryExpr op x) = (un_exp_size ((sub_size x) + 1) op)" |
  "sub_size (BinaryExpr BinSub x y) = (bin_exp_size ((sub_size x) + (sub_size y) + 2) BinSub) + 1" |
  "sub_size (BinaryExpr op x y) = (bin_exp_size ((sub_size x) + (sub_size y) + 2) op)" |
  "sub_size (ConditionalExpr c t f) = (sub_size c) + (sub_size t) + (sub_size f) + cond_cycles" |
  "sub_size (ConstantExpr c) = 1" |
  "sub_size (ParameterExpr ind s) = 2" |
  "sub_size (LeafExpr nid s) = 2" |
  "sub_size (ConstantVar c) = 2" |
  "sub_size (VariableExpr x s) = 2"

phase SubNode
  terminating sub_size
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
  using assms apply (cases x; cases y; auto) by (metis (full_types) intval_sub.simps(2))

lemma val_sub_after_left_sub:
  assumes "val[(x - y) - x] \<noteq> UndefVal"
  shows   "val[(x - y) - x] = val[-y]"
  using assms apply (cases x; cases y; auto) by (metis (full_types) intval_sub.simps(2))

lemma val_sub_then_left_sub:
  assumes "y = new_int b v"
  assumes "val[x - (x - y)] \<noteq> UndefVal"
  shows   "val[x - (x - y)] = y"
  using assms apply (cases x; auto) by (metis (mono_tags) intval_sub.simps(6))

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
  using assms apply (cases x; cases y; auto) by (metis (mono_tags, lifting) intval_sub.simps(6))

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

lemma val_negate_idempotent:
  assumes "x = IntVal b v \<and> take_bit b v = v"
  shows "x = val[-(-x)]"
  by (auto simp: assms is_IntVal_def)

(* Exp level proofs *)
lemma exp_sub_after_right_add:
  shows "exp[(x + y) - y] \<ge> x"
  apply auto
  subgoal premises p for m p ya xa yaa
  proof -
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
    then have "val[(xv + yv) - yv] \<noteq> UndefVal"
      using xvv yvv apply (cases xv; cases yv; auto)
      by (metis evalDet intval_add.simps(1) p(3,4,5) xv yv)
     then show ?thesis
       by (metis xvv xv yv eval_unused_bits_zero new_int.simps p(1,3,4) val_sub_after_right_add_2
           evalDet)
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
    then have "[m,p] \<turnstile> exp[x + y] \<mapsto> val[xv + yv]"
      by (metis bin_eval.simps(1) evalDet p(1,2,3) unfold_binary val_sub_negative_value xv)
    then show ?thesis
      by (metis evalDet p(1,2,3) val_sub_negative_value xv yv)
  qed
  done

lemma exp_sub_then_left_sub:
  "exp[x - (x - y)] \<ge> y"
  using val_sub_then_left_sub apply auto
  subgoal premises p for m p xa xaa ya
    proof -
      obtain xa where xa: "[m, p] \<turnstile> x \<mapsto> xa"
        using p(2) by blast
      obtain ya where ya: "[m, p] \<turnstile> y \<mapsto> ya"
        using p(5) by auto
      obtain xaa where xaa: "[m, p] \<turnstile> x \<mapsto> xaa"
        using p(2) by blast
      have "val[xa - (xaa - ya)] \<noteq> UndefVal"
        by (metis evalDet p(2,3,4,5) xa xaa ya)
      then have "[m, p] \<turnstile> y \<mapsto> val[xa - (xaa - ya)]"
        by (metis Value.exhaust eval_unused_bits_zero evaltree_not_undef xa xaa ya new_int.simps
            intval_sub.simps(6,7,8,9) evalDet val_sub_then_left_sub)
      then show ?thesis
        by (metis evalDet p(2,4,5) xa xaa ya)
    qed
  done

thm_oracles exp_sub_then_left_sub

lemma exp_subtract_zero:
  "exp[(x - (const IntVal b 0))] \<ge> x"
  apply auto
  subgoal premises p for m p xa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis array_length.cases evalDet evaltree_not_undef intval_sub.simps(3,4,5) p(1,2) xv)
    then have widthSame: "xb = b"
      by (metis evalDet intval_sub.simps(1) new_int_bin.simps p(1,2) xv)
    then have unfoldSub: "val[xv - (IntVal b 0)] = (new_int xb (xvv - 0))"
      by (simp add: xvv)
    have "xv = new_int xb (xvv)"
      using eval_unused_bits_zero xv xvv by auto
    then show ?thesis
      by (metis diff_zero evalDet p(1) unfoldSub xv)
  qed
  done

lemma exp_zero_subtract_value:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "\<not>(is_ConstantExpr x)"
  shows "exp[(const IntVal b 0) - x] \<ge> exp[-x]"
  using assms apply auto
  subgoal premises p for m p xa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(4) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis constantAsStamp.cases evalDet evaltree_not_undef intval_sub.simps(7,8,9) p(4,5) xv)
    then have "val[(IntVal b 0) - xv] = (new_int xb (0 - xvv))"
      by (metis intval_sub.simps(1) new_int_bin.simps p(1,2) valid_int_same_bits wf_stamp_def xv)
    then show ?thesis
      by (metis UnaryExpr intval_negate.simps(1) p(4,5) unary_eval.simps(2) verit_minus_simplify(3)
          evalDet xv xvv)
  qed
  done

lemma exp_sub_after_sub_left:
  shows "exp[((x - y) - x)] \<ge> exp[-y]"
  apply auto
  subgoal premises p for m p xa xaa ya
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p(4) by blast
    have lhsEval: "[m,p] \<turnstile> exp[(x - y) - x] \<mapsto> val[(xv - yv) - xv]"
      by (metis BinaryExpr bin_eval.simps(2) evalDet p xv yv)
    have rhsEval: "[m,p] \<turnstile> exp[-y] \<mapsto> val[-yv]"
      by (metis evalDet p(1,2,3,4) unary_eval.simps(2) unfold_unary val_sub_after_left_sub yv)
    have "val[(xv - yv) - xv] = val[-yv]"
      using val_sub_after_left_sub lhsEval unfold_binary by auto
    then show ?thesis
      by (metis evalDet p(1,3,4) rhsEval xv yv)
  qed
  done

lemma exp_sub_self_is_zero:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp b lo hi"
  shows "exp[x - x] \<ge> exp[const (IntVal b 0)]"
  using assms apply auto subgoal premises p for m p xa xaa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(3) by auto
    obtain xvv where xvv: "xv = IntVal b xvv"
      by (metis ExpIntBecomesIntVal p(1,2) wf_stamp_def xv)
    have rhsE: "[m,p] \<turnstile> exp[const (IntVal b 0)] \<mapsto> val[IntVal b 0]"
      using p(1,2) wf_integerstamp_implies_zero_evals xv by auto
    have "val[xv - xv] = val[IntVal b 0]"
      unfolding xvv by simp
    then show ?thesis
      by (metis evalDet p(3,4) rhsE xv)
  qed
  done

text \<open>Optimisations\<close>

optimization SubAfterAddRight: "(x + y) - y \<longmapsto> x"
  using exp_sub_after_right_add by blast

optimization SubAfterAddLeft: "(x + y) - x \<longmapsto> y"
  using exp_sub_after_right_add2 by blast

optimization SubAfterSubLeft: "(x - y) - x \<longmapsto> -y"
  using exp_sub_after_sub_left by simp

optimization SubThenAddLeft: "x - (x + y) \<longmapsto> -y"
  apply auto by (metis evalDet unary_eval.simps(2) unfold_unary val_sub_then_left_add)

optimization SubThenAddRight: "y - (x + y) \<longmapsto> -x"
  apply auto
  by (metis intval_add_sym unary_eval.simps(2) unfold_unary val_sub_then_left_add evalDet)

optimization SubThenSubLeft: "x - (x - y) \<longmapsto> y"
  using exp_sub_then_left_sub by blast

optimization SubtractZero: "x - (const new_int b 0) \<longmapsto> x"
  using exp_subtract_zero by fast

thm_oracles SubtractZero

(* doesn't have any subgoals? *)
(*
optimization SubNegativeConstant: "(x - (const (IntVal b y))) \<longmapsto> 
                                    x + (const (IntVal b y))  when (y < 0)"  
  done
*)

optimization SubNegativeValue: "x - (-y) \<longmapsto> x + y"
  using exp_sub_negative_value by blast

thm_oracles SubNegativeValue

optimization ZeroSubtractValue: "(const new_int b 0) - x \<longmapsto> (-x)
                                 when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and>
                                       \<not>(is_ConstantExpr x))"
  using exp_zero_subtract_value by auto

optimization SubSelfIsZero: "(x - x) \<longmapsto> const new_int b 0
                             when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  using exp_sub_self_is_zero by blast

end (* End of SubPhase *)

end (* End of file *)
