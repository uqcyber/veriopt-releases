theory SubPhase
  imports
    Common
begin

section \<open>Optimizations for Sub Nodes\<close>

phase SubPhase
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
  assumes "y \<noteq> UndefVal \<and> x \<noteq> UndefVal \<and> ((x + y) - y \<noteq> UndefVal)"
  shows "val[(x + y) - (y)] = val[x]"
  using bin_sub_after_right_add 
  using assms apply (cases x; cases y; auto) apply (simp add: minus_Value_def plus_Value_def)
  by (simp add: minus_Value_def plus_Value_def)+

lemma val_sub_after_left_sub:
  assumes "y \<noteq> UndefVal \<and> x \<noteq> UndefVal \<and> ((x - y) - x \<noteq> UndefVal)"
  shows "val[(x - y) - x] = val[-y]"
  using assms apply (cases x; cases y; auto) apply (simp add: minus_Value_def)
    by (simp add: minus_Value_def)+

lemma val_sub_then_left_sub:
  assumes "y \<noteq> UndefVal \<and> x \<noteq> UndefVal \<and> (x - (x - y) \<noteq> UndefVal)"
  shows "val[x - (x - y)] = val[y]"
  using assms apply (cases x; cases y; auto) apply (simp add: minus_Value_def)
    by (simp add: minus_Value_def)+

lemma val_subtract_zero:
  assumes "x \<noteq> UndefVal \<and> intval_sub x (IntVal32 0) \<noteq> UndefVal "
  shows "intval_sub x (IntVal32 0) = val[x]"
  using assms by (induction x; simp)

lemma val_zero_subtract_value:
  assumes "x \<noteq> UndefVal \<and> intval_sub (IntVal32 0) x \<noteq> UndefVal "
  shows "intval_sub (IntVal32 0) x = val[-x]"
  using assms by (induction x; simp)

lemma val_zero_subtract_value_64:
  assumes "x \<noteq> UndefVal \<and> intval_sub (IntVal64 0) x \<noteq> UndefVal "
  shows "intval_sub (IntVal64 0) x = val[-x]"
  using assms by (induction x; simp)

lemma val_sub_then_left_add:
  assumes "y \<noteq> UndefVal \<and> x \<noteq> UndefVal \<and> (x - (x + y) \<noteq> UndefVal)"
  shows "val[x - (x + y)] = val[-y]"
  using assms apply (cases x; cases y; auto) apply (simp add: minus_Value_def plus_Value_def)
  by (simp add: minus_Value_def plus_Value_def)+

lemma val_sub_negative_value:
  assumes "y \<noteq> UndefVal \<and> x \<noteq> UndefVal \<and> (x - (intval_negate y) \<noteq> UndefVal)"
  shows "val[x - (-y)] = val[x + y]"
  using assms apply (cases x; cases y)
  by (simp add: minus_Value_def plus_Value_def)+

(* 32 *)
lemma val_sub_self_is_zero:
  assumes "is_IntVal32 x \<and> x \<noteq> UndefVal \<and> x - x \<noteq> UndefVal"
  shows "val[x - x] = IntVal32 0"
  using assms apply (cases x; auto)
  done

(* 64 *)
lemma val_sub_self_is_zero_2:
  assumes "is_IntVal64 x \<and> x \<noteq> UndefVal \<and> x - x \<noteq> UndefVal"
  shows "val[x - x] = IntVal64 0"
  using assms apply (cases x; auto)
  done

lemma val_sub_negative_const:
  assumes "is_IntVal32 y \<or> is_IntVal64 y \<and> y \<noteq> UndefVal \<and> x \<noteq> UndefVal \<and> 
           x - (intval_negate y) \<noteq> UndefVal"
  shows "x - (intval_negate y) = x + y"
  using assms apply (cases x; cases y; auto)
    by (simp add: minus_Value_def plus_Value_def)+


(* Expression level proofs *)

lemma exp_sub_after_right_add:
  shows "exp[(x+y)-y] \<ge> exp[x]"
  apply simp
  apply auto
  by (metis evalDet evaltree_not_undef minus_Value_def plus_Value_def val_sub_after_right_add_2)

lemma exp_sub_negative_value:
 "exp[x - (-y)] \<ge> exp[x + y]"
  apply simp using val_sub_negative_value
  by (smt (verit) bin_eval.simps(1) bin_eval.simps(3) evaltree_not_undef minus_Value_def 
      unary_eval.simps(2) unfold_binary unfold_unary)

(* Optimizations *)
optimization sub_after_right_add: "((x + y) - y) \<longmapsto>  x"
   apply unfold_optimization
   apply simp_all
   apply auto
  by (metis evalDet evaltree_not_undef minus_Value_def plus_Value_def val_sub_after_right_add_2)

optimization sub_after_left_add: "((x + y) - x) \<longmapsto>  y"
   apply unfold_optimization
   apply simp_all
   apply auto
  by (metis add.commute evalDet intval_add.simps(10) minus_Value_def plus_Value_def 
      val_sub_after_right_add_2)

optimization sub_after_left_sub: "((x - y) - x) \<longmapsto>  -y"
   apply unfold_optimization
   apply simp_all
   apply auto
   apply (metis evalDet intval_sub.simps(10) minus_Value_def unary_eval.simps(2) unfold_unary 
          val_sub_after_left_sub)
  done 

optimization sub_then_left_add: "(x - (x + y)) \<longmapsto> -y"
   apply unfold_optimization
   apply simp_all
   apply auto
   apply (metis UnaryExpr evalDet evaltree_not_undef minus_Value_def plus_Value_def 
          unary_eval.simps(2) val_sub_then_left_add)
  done

optimization sub_then_right_add: "(y - (x + y)) \<longmapsto> -x"
   apply unfold_optimization
   apply simp_all
   apply auto
   apply (metis UnaryExpr add.commute evalDet evaltree_not_undef minus_Value_def plus_Value_def 
          unary_eval.simps(2) val_sub_then_left_add)
  done


optimization sub_then_left_sub: "(x - (x - y)) \<longmapsto> y"
   apply unfold_optimization
   apply simp_all
   apply auto
  by (metis evalDet evaltree_not_undef minus_Value_def val_sub_then_left_sub)


(* 32-bit *)
optimization subtract_zero: "(x - (const IntVal32 0)) \<longmapsto> x"
   apply unfold_optimization
   apply simp_all
   apply auto
  by (metis evaltree_not_undef val_subtract_zero)

(* 64-bit *)
optimization subtract_zero_64: "(x - (const IntVal64 0)) \<longmapsto> x"
   apply unfold_optimization
   apply simp_all
   apply auto 
   apply (smt (z3) Value.sel(2) diff_zero intval_sub.elims intval_sub.simps(12)) 
  done

optimization sub_negative_value: "(x - (-y)) \<longmapsto> x + y"
   apply unfold_optimization
   apply simp_all using exp_sub_negative_value 
   apply auto
  done

(* Ln 146 rewrite, 32-bit *)
optimization sub_negative_const2: "(x - (const (intval_negate (IntVal32 y)))) \<longmapsto> 
                                    x + (const (IntVal32 y)) 
                                    when (y < 0)"
   apply unfold_optimization
   apply auto
  done 

(* Ln 146 rewrite, 64-bit *)
optimization sub_negative_const2_64: "(x - (const (intval_negate (IntVal64 y)))) \<longmapsto> 
                                       x + (const (IntVal64 y)) 
                                       when (y < 0)"
   apply unfold_optimization
   apply auto
  done 

(* 32-bit *)
optimization zero_sub_value: "((const IntVal32 0) - x) \<longmapsto> -x"
   apply unfold_optimization unfolding size.simps
   apply simp_all
   apply auto
   apply (metis UnaryExpr intval_sub.simps(10) unary_eval.simps(2) val_zero_subtract_value)
  done

(* 64-bit *)
optimization zero_sub_value_64: "((const IntVal64 0) - x) \<longmapsto> -x"
   apply unfold_optimization unfolding size.simps
   apply simp_all
   apply auto 
   apply (metis UnaryExpr intval_sub.simps(10) unary_eval.simps(2) val_zero_subtract_value_64)
  done

(* wf_stamp definition borrowed from ConditionalPhase *)
definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

(* 32-bit *)
optimization opt_sub_self_is_zero32: "(x - x) \<longmapsto> const IntVal32 0 when 
                      (wf_stamp x \<and> stamp_expr x = default_stamp)"
   apply unfold_optimization 
   apply simp_all 
   apply auto defer
   apply (metis less_1_mult less_one linorder_neqE_nat mult.commute mult_1 numeral_1_eq_Suc_0 
          one_eq_numeral_iff one_less_numeral_iff semiring_norm(77) size_pos 
          zero_less_iff_neq_zero)
   apply (metis (no_types, lifting) Value.distinct(1) a0a_helper add.inverse_neutral evalDet 
         intval_negate.simps(1) intval_sub.simps(10) minus_Value_def plus_Value_def unfold_const32 
         val_sub_then_left_add wf_stamp_def)
  done

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