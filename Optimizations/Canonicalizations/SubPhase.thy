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
  by (metis intval_sub.simps(2))

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

(* 32 *)
lemma val_sub_self_is_zero:
  assumes "x = new_int 32 v \<and> x - x \<noteq> UndefVal"
  shows "val[x - x] = IntVal 32 0"
  using assms by (cases x; auto)

(* 64 *)
lemma val_sub_self_is_zero_2:
  assumes "x = new_int 64 v \<and> x - x \<noteq> UndefVal"
  shows "val[x - x] = IntVal 64 0"
  using assms by (cases x; auto)

lemma val_sub_negative_const:
  assumes "y = new_int b v \<and> val[x - (-y)] \<noteq> UndefVal"
  shows "val[x - (- y)] = val[x + y]"
  using assms by (cases x; cases y; auto)


(* Expression level proofs *)
lemma exp_sub_after_right_add:
  shows "exp[(x+y)-y] \<ge> exp[x]"
  apply auto using val_sub_after_right_add_2 sorry (*
  by (metis evalDet  minus_Value_def plus_Value_def val_sub_after_right_add_2)*)

lemma exp_sub_negative_value:
 "exp[x - (-y)] \<ge> exp[x + y]"
  apply simp using val_sub_negative_value
  by (smt (verit) bin_eval.simps(1) bin_eval.simps(3) evaltree_not_undef minus_Value_def 
      unary_eval.simps(2) unfold_binary unfold_unary)

(* Optimizations *)
optimization sub_after_right_add: "((x + y) - y) \<longmapsto>  x"
  using exp_sub_after_right_add by blast

optimization sub_after_left_add: "((x + y) - x) \<longmapsto>  y"
  sorry(*
   apply auto
  by (metis add.commute evalDet minus_Value_def plus_Value_def val_sub_after_right_add_2)*)

optimization sub_after_left_sub: "((x - y) - x) \<longmapsto>  -y"
   apply auto 
   apply (metis One_nat_def less_add_one less_numeral_extra(3) less_one linorder_neqE_nat 
          pos_add_strict size_pos)
  by (metis evalDet unary_eval.simps(2) unfold_unary val_sub_after_left_sub)


optimization sub_then_left_add: "(x - (x + y)) \<longmapsto> -y"
   apply auto 
   apply (simp add: Suc_lessI one_is_add) 
  by (metis evalDet unary_eval.simps(2) unfold_unary 
      val_sub_then_left_add)

optimization sub_then_right_add: "(y - (x + y)) \<longmapsto> -x"
   apply auto 
   apply (metis less_1_mult less_one linorder_neqE_nat mult.commute mult_1 numeral_1_eq_Suc_0 
          one_eq_numeral_iff one_less_numeral_iff semiring_norm(77) size_pos zero_less_iff_neq_zero)
  by (metis evalDet intval_add_sym unary_eval.simps(2) unfold_unary 
      val_sub_then_left_add)

optimization sub_then_left_sub: "(x - (x - y)) \<longmapsto> y"
  sorry (*
   apply auto
  by (metis evalDet val_sub_then_left_sub)*)

(* 32-bit *)
optimization subtract_zero: "(x - (const IntVal 32 0)) \<longmapsto> x"
  sorry (*
  apply auto
  by (metis val_subtract_zero)*)

(* 64-bit *)
optimization subtract_zero_64: "(x - (const IntVal 64 0)) \<longmapsto> x"
  sorry (*
   apply auto 
  by (smt (z3) Value.sel(2) diff_zero intval_sub.elims intval_sub.simps(12)) *)


optimization sub_negative_value: "(x - (-y)) \<longmapsto> x + y"
   using exp_sub_negative_value
   defer apply blast sorry

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

(* 32-bit *)
optimization zero_sub_value: "((const IntVal 32 0) - x) \<longmapsto> -x"
  unfolding size.simps
   apply simp_all
   apply auto defer
  apply (smt (verit) UnaryExpr Value.inject(1) intval_negate.simps(1) intval_sub.elims new_int_bin.simps unary_eval.simps(2) verit_minus_simplify(3))
  sorry

(* 64-bit *)
optimization zero_sub_value_64: "((const IntVal 64 0) - x) \<longmapsto> -x"
   unfolding size.simps
   apply simp_all
   apply auto defer
   apply (smt (verit) UnaryExpr Value.inject(1) intval_negate.simps(1) intval_sub.elims new_int_bin.simps unary_eval.simps(2) verit_minus_simplify(3))
  sorry

(* wf_stamp definition borrowed from ConditionalPhase *)
definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

(* 32-bit *)
optimization opt_sub_self_is_zero32: "(x - x) \<longmapsto> const IntVal32 0 when 
                      (wf_stamp x \<and> stamp_expr x = default_stamp)"
   apply simp_all 
   apply auto (* 
   apply (metis less_1_mult less_one linorder_neqE_nat mult.commute mult_1 numeral_1_eq_Suc_0 
          one_eq_numeral_iff one_less_numeral_iff semiring_norm(77) size_pos 
          zero_less_iff_neq_zero)
   apply (metis (no_types, lifting) Value.distinct(1) a0a_helper add.inverse_neutral evalDet 
         intval_negate.simps(1) intval_sub.simps(10) minus_Value_def plus_Value_def unfold_const32 
         val_sub_then_left_add wf_stamp_def)
  done*) sorry

(* 64-bit *)
(*
optimization opt_sub_self_is_zero64: "(x - x) \<longmapsto> const IntVal64 0 when 
                      (wf_stamp x \<and> stamp_expr x = (unrestricted_stamp (IntegerStamp 64 0 0)))"
   apply unfold_optimization 
   apply simp_all 
   apply auto defer
   apply (metis less_1_mult less_one linorder_neqE_nat mult.commute mult_1 numeral_1_eq_Suc_0 
          one_eq_numeral_iff one_less_numeral_iff semiring_norm(77) size_pos 
          zero_less_iff_neq_zero) using val_sub_self_is_zero_2 wf_stamp_def
   apply (metis (no_types, lifting) evalDet intval_sub.simps(10) is_IntVal64_def minus_Value_def 
          unfold_const64 valid_int64)  
  done
*)

end (* End of SubPhase *)

end (* End of file *)