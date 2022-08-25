theory AndPhase
  imports
    Common
    NewAnd (* Allows access to mask operations *)
begin

section \<open>Optimizations for And Nodes\<close>

phase AndPhase
  terminating size
begin

(* Word level proofs *)
lemma bin_and_nots:
 "(~x & ~y) = (~(x | y))"
  by simp

lemma bin_and_neutral:
 "(x & ~False) = x"
  by simp

(* Value level proofs *)
lemma val_and_equal:
  assumes "val[x & x] \<noteq> UndefVal"
  shows "val[x & x] = x"
   using assms 
  by (cases x; auto)

lemma val_and_nots:
  "val[~x & ~y] = val[~(x | y)]"
  by (cases x; cases y; auto)

lemma val_and_neutral_32:
  assumes "is_IntVal32 x"
  shows "val[x & ~(IntVal32 0)] = x"
   using assms 
  by (cases x; auto)
 
lemma val_and_neutral_64:
  assumes "is_IntVal64 x"
  shows "val[x & ~(IntVal64 0)] = x"
   using assms 
  by (cases x; auto) 

(* Not sure if this one is written correctly *)
(* Rewrite is AndNode line 129 *)
lemma val_and_sign_extend:
  assumes "e = (1 << In)-1"
  shows "val[(intval_sign_extend In Out x) & (IntVal32 e)] = intval_zero_extend In Out x"
  using assms apply (cases x; auto) 
  sorry

lemma val_and_sign_extend_2:
  assumes "e = (1 << In)-1 \<and> intval_and (intval_sign_extend In Out x) (IntVal32 e) \<noteq> UndefVal"
  shows "val[(intval_sign_extend In Out x) &  (IntVal32 e)] = intval_zero_extend In Out x"
  using assms apply (cases x;  auto) 
  sorry

(* Extras which were missing *)
lemma val_and_zero_32:
  assumes "is_IntVal32 x"
  shows "val[x & (IntVal32 0)] = IntVal32 0"
   using assms 
  by (cases x; auto) 

lemma val_and_zero_64:
  assumes "is_IntVal64 x"
  shows "val[x & (IntVal64 0)] = IntVal64 0"
   using assms 
  by (cases x; auto) 

(* Exp level proofs *)
lemma exp_and_equal:
  "exp[x & x] \<ge> exp[x]"
   apply simp using val_and_equal 
  by (metis bin_eval.simps(4) evalDet evaltree_not_undef unfold_binary)

lemma exp_and_nots:
  "exp[~x & ~y] \<ge> exp[~(x | y)]"
   apply (cases x; cases y; auto) using val_and_nots 
  by fastforce+ 

lemma exp_and_neutral_64: 
  "exp[x & ~(const (IntVal64 0))] \<ge> x"
  apply (cases x; simp) using val_and_neutral_64 bin_eval.simps(4)  
  apply (smt (verit) BinaryExprE Value.collapse(1) intval_and.simps(12) intval_not.simps(2) 
         is_IntVal_def unary_eval.simps(3) unary_eval_int unfold_const64 unfold_unary) 
         using val_and_neutral_64 bin_eval.simps(4) 
  apply (metis (no_types, lifting) BinaryExprE UnaryExprE Value.collapse(1) bin_eval_int 
         intval_and.simps(12) intval_not.simps(2) is_IntVal_def unary_eval.simps(3) unfold_const64)
         using val_and_neutral_64 bin_eval.simps(4) unary_eval.simps(3)
  apply (smt (z3) BinaryExprE UnaryExprE Value.discI(2) Value.distinct(9) intval_and.elims 
         intval_not.simps(2) unfold_const64) 
         using val_and_neutral_64 bin_eval.simps(4) unary_eval.simps(3) bin_and_neutral 
               unfold_const64 intval_and.elims intval_not.simps(2) 
         sorry
  

lemma exp_and_neutral_32: 
  "exp[x & ~(const (IntVal32 0))] \<ge> x"
  apply simp_all apply (cases x; simp) using val_and_neutral_32 bin_eval.simps(4) 
  apply (metis (no_types, lifting) UnaryExprE Value.collapse(2) intval_and.simps(5) 
         intval_not.simps(1) is_IntVal_def unary_eval.simps(3) unary_eval_int unfold_binary 
         unfold_const32)
         using val_and_neutral_32 bin_eval.simps(4) 
  apply (smt (verit) UnaryExprE Value.collapse(2) bin_eval_int intval_and.simps(5) 
         intval_not.simps(1) is_IntVal_def unary_eval.simps(3) unfold_binary unfold_const32) 
         using val_and_neutral_32 bin_eval.simps(4) unary_eval.simps(3)
               unfold_const32 intval_and.elims 
  apply (smt (z3) BinaryExprE UnaryExprE Value.discI(1) Value.distinct(1) intval_and.simps(12))
         using val_and_neutral_32 bin_eval.simps(4) unary_eval.simps(3) bin_and_neutral 
               unfold_const32 intval_and.elims intval_not.simps(2) 
  sorry


(* Optimisations *)
optimization opt_and_equal: "x & x \<longmapsto> x"
  using exp_and_equal by blast

optimization opt_AndShiftConstantRight: "((const x) & y) \<longmapsto> y & (const x) 
                                         when \<not>(is_ConstantExpr y)"
     using intval_and_commute bin_eval.simps(4) apply auto  
  sorry

optimization opt_and_right_fall_through: "(x & y) \<longmapsto> y
                                when (((and (not (IRExpr_down x)) (IRExpr_up y)) = 0))"
  by (simp add: IRExpr_down_def IRExpr_up_def)

optimization opt_and_left_fall_through: "(x & y) \<longmapsto> x
                                when (((and (not (IRExpr_down y)) (IRExpr_up x)) = 0))"
   by (simp add: IRExpr_down_def IRExpr_up_def) 
 
optimization opt_and_nots: "(~x) & (~y) \<longmapsto> ~(x | y)"
    using exp_and_nots 
   by auto 

optimization opt_and_sign_extend: "BinaryExpr BinAnd (UnaryExpr (UnarySignExtend In Out) x) 
                                                     (ConstantExpr (IntVal32 e))
                                   \<longmapsto> (UnaryExpr (UnaryZeroExtend In Out) x)
                                                   when (e = (1 << In) - 1)"
   apply simp_all 
   apply auto
  sorry 

(* Borrowed from ConditionalPhase *)
definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"


optimization opt_and_neutral_32: "(x & ~(const (IntVal32 0))) \<longmapsto> x 
   when (wf_stamp x \<and> stamp_expr x = default_stamp)"
   apply auto 
  apply (cases x; simp) using unary_eval.simps unfold_const32 val_and_neutral_32 
  sorry (*
   apply (metis UnaryExprE intval_and.simps(5) is_IntVal64_def is_IntVal_def unary_eval_int)
    using unary_eval.simps(2) unfold_const32 val_and_neutral_32 val_and_neutral_64 
  sorry*)

(* Extra ones which were missing *)
(*
optimization opt_and_zero_32: "(x & (ConstantExpr (IntVal32 0))) \<longmapsto> ConstantExpr (IntVal32 0)"
   apply unfold_optimization apply simp_all apply auto 
   apply (smt (verit) Value.disc(2) intval_and.simps(3) intval_and_associative intval_and_commute 
          intval_eliminate_y_32 intval_or_absorb_and intval_or_commute unfold_const32 
          val_and_zero_32)
  done

optimization opt_and_zero_64: "(x & (ConstantExpr (IntVal64 0))) \<longmapsto> ConstantExpr (IntVal64 0)"
   apply unfold_optimization apply simp_all apply auto 
   apply (smt (verit) Value.disc(8) intval_and_absorb_or intval_and_commute intval_eliminate_y_64 
          intval_or_commute unfold_const64 val_and_zero_64)
  done
*)

(* Need to prove exp-level proofs above
optimization opt_and_neutral_32: "(x & (UnaryExpr UnaryNot (ConstantExpr (IntVal32 0)))) \<longmapsto> x"
   apply unfold_optimization apply simp_all
  apply (metis exp_and_neutral_32 le_expr_def) 
  done

optimization opt_and_neutral_64: "(x & (UnaryExpr UnaryNot (ConstantExpr (IntVal64 0)))) \<longmapsto> x"
   apply unfold_optimization 
   apply simp_all
  using exp_and_neutral_64
  apply (meson le_expr_def)
  done
*)

end (* End of AndPhase *)

end (* End of file *)