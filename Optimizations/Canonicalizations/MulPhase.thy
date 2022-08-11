theory MulPhase
  imports
    Common
begin

section \<open>Optimizations for Mul Nodes\<close>

phase MulPhase
  terminating size
begin

(* Word level proofs *)
lemma bin_eliminate_redundant_negative:
 "uminus (x :: 'a::len word) * uminus (y :: 'a::len word) = x * y"
  by simp

lemma bin_multiply_neutral:
 "(x :: 'a::len word) * 1 = x"
  by simp

lemma bin_multiply_zero:
 "(x :: 'a::len word) * 0 = 0"
  by simp

lemma bin_multiply_negative:
 "(x :: 'a::len word) * uminus 1 = uminus x"
  by simp

lemma bin_multiply_power_2:
 "(x:: 'a::len word) * (2^j) = x << j"
  by simp

(* Value level proofs *)
lemma val_eliminate_redundant_negative:
  assumes "x \<noteq> UndefVal \<and> y \<noteq> UndefVal \<and> (intval_negate x * intval_negate y) \<noteq> UndefVal"
  shows "intval_mul val[-x] val[-y] = intval_mul x y"
  apply (cases x; cases y; auto)
  done

lemma val_multiply_neutral_32:
  assumes "is_IntVal32 x"
  shows "val[x] *  (IntVal32 1) = val[x]"
  using assms is_IntVal32_def times_Value_def by fastforce

lemma val_multiply_neutral_64:
  assumes "is_IntVal64 x"
  shows "val[x] *  (IntVal64 1) = val[x]"
  using assms 
   apply (metis Value.collapse(2) intval_mul.simps(2) mult.right_neutral times_Value_def)
  done

lemma val_multiply_zero_32:
  assumes "is_IntVal32 x"
  shows "val[x] * (IntVal32 0) = IntVal32 0"
  using assms 
  by (metis Value.collapse(1) intval_mul.simps(1) mult_not_zero times_Value_def)

lemma val_multiply_zero_64:
  assumes "is_IntVal64 x"
  shows "val[x] * (IntVal64 0) = IntVal64 0"
   using assms intval_mul.simps(2) 
  by (metis Value.collapse(2) mult_zero_right times_Value_def)

lemma val_multiply_negative_32:
  assumes "is_IntVal32 x"
  shows "x * intval_negate (IntVal32 1) = intval_negate x"
  using assms is_IntVal32_def times_Value_def by force

lemma val_multiply_negative_64:
  assumes "is_IntVal64 x"
  shows "x * intval_negate (IntVal64 1) = intval_negate x"
  using assms is_IntVal64_def times_Value_def by fastforce


(* Borrowed from ShiftPhase *)
fun intval_log2 :: "Value \<Rightarrow> Value" where
  "intval_log2 (IntVal32 v) = IntVal32 (word_of_int (SOME e. v=2^e))" |
  "intval_log2 (IntVal64 v) = IntVal64 (word_of_int (SOME e. v=2^e))" |
  "intval_log2 _ = UndefVal"

lemma val_multiply_power_2_2:
  assumes "intval_log2 y \<noteq> UndefVal \<and> is_IntVal32 y \<and> 

           (val_to_bool (intval_less_than (IntVal32 0) (intval_log2 y)) \<or> 
            val_to_bool (intval_equals (IntVal32 0) (intval_log2 y)))"

  shows "x * y = intval_left_shift x (intval_log2 y)"
  using assms apply (cases x; cases y;  auto) 
  apply (simp add: times_Value_def)+ 
  sorry

lemma val_multiply_power_2:
  fixes j :: "32 word"
  assumes "is_IntVal32 x \<and> j \<ge> 0 \<and> j_AsNat = (nat (Values.intval (IntVal32 j)))"
  shows "x * IntVal32 (2 ^ j_AsNat) = intval_left_shift x (IntVal32 j)"
  using assms apply (cases x; cases j; cases j_AsNat; auto)
  sorry


(* Exp-level proofs *)

lemma exp_multiply_zero_64:
 "BinaryExpr BinMul x (ConstantExpr (IntVal64 0)) \<ge> ConstantExpr (IntVal64 0)"
   apply (cases x; auto) using val_multiply_zero_64 unfold_const64 
   apply (metis intval_mul.simps(12) is_IntVal32_def is_IntVal_def times_Value_def unary_eval_int)
          using val_multiply_zero_64 unfold_const64 
   apply (metis bin_eval_int intval_mul.simps(12) is_IntVal32_def is_IntVal_def times_Value_def)
          using val_multiply_zero_64 intval_mul.simps(2) unfold_const64 
   apply (metis (no_types, opaque_lifting) Value.exhaust intval_mul.simps(12) intval_mul.simps(8) 
          intval_mul.simps(9) mult.commute mult_zero_left) 
          using val_multiply_zero_64 bin_multiply_zero intval_mul.simps(2) unfold_const64 
                intval_mul.simps(12) 
   apply (smt (verit, ccfv_SIG) Value.disc(8) Value.sel(2) intval_mul.simps(11) intval_mul.simps(8) 
          is_ObjRef_def times_Value_def val_to_bool.elims(3) val_to_bool.simps(4) 
          valid_value.simps(19) wf_bool.elims(2) wf_bool.elims(3))

           using val_multiply_zero_64 bin_multiply_zero intval_mul.simps(2) unfold_const64 
                intval_mul.simps(12) 
           sorry

(* Optimizations *)
optimization opt_EliminateRedundantNegative: "-x * -y \<longmapsto> x * y"
   unfolding le_expr_def
   apply auto using val_eliminate_redundant_negative bin_eval.simps(2)
  by (metis BinaryExpr intval_negate.simps(3) times_Value_def)


optimization opt_MultiplyNeutral32: "x * ConstantExpr (IntVal32 1) \<longmapsto> x"
    unfolding le_expr_def
    apply auto using val_multiply_neutral_32 bin_eval.simps(2) 
  by (smt (z3) Value.discI(1) Value.distinct(9) intval_mul.elims times_Value_def)


optimization opt_MultiplyNeutral64: "x * ConstantExpr (IntVal64 1) \<longmapsto> x"
   unfolding le_expr_def
   apply auto using val_multiply_neutral_64 
  by (metis Value.exhaust evaltree_not_undef intval_mul.simps(12) intval_mul.simps(13) 
      intval_mul.simps(14) is_IntVal64_def times_Value_def) 

optimization opt_MultiplyZero32: "x * ConstantExpr (IntVal32 0) \<longmapsto> ConstantExpr (IntVal32 0)"
    unfolding le_expr_def
    apply auto using val_multiply_zero_32 bin_eval.simps(2) intval_mul.simps(1)
  by (metis Value.disc(2) Value.exhaust intval_mul.simps(3) intval_mul.simps(5) intval_mul.simps(8) 
      intval_mul.simps(9) times_Value_def unfold_const32)

(* Need to prove exp_multiply_zero_64 *)
optimization opt_MultiplyZero64: "x * ConstantExpr (IntVal64 0) \<longmapsto> ConstantExpr (IntVal64 0)"
    unfolding le_expr_def using exp_multiply_zero_64 
   apply simp+ 
  done

(* Size issue *)
optimization opt_MultiplyNegative32: "x * - (ConstantExpr (IntVal32 1)) \<longmapsto> UnaryExpr UnaryNeg x"
    apply auto using val_multiply_negative_32 intval_negate.simps(1) unfold_unary (*
   apply (smt (z3) Value.discI(1) Value.distinct(9) intval_mul.elims intval_negate.simps(1) 
      times_Value_def unary_eval.simps(2) unfold_unary)*)
  sorry 

optimization opt_MultiplyNegative64: "x * - (ConstantExpr (IntVal64 1)) \<longmapsto> UnaryExpr UnaryNeg x"
    unfolding le_expr_def apply auto using val_multiply_negative_64 intval_negate.simps(1) unfold_unary 
  sorry


end (* End of MulPhase *)

end (* End of file *)
