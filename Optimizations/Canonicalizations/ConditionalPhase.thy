subsection \<open>Conditional Expression\<close>

theory ConditionalPhase
  imports
    Common
begin

phase ConditionalNode
  terminating size
begin

lemma negates: "is_IntVal e \<Longrightarrow> val_to_bool (val[e]) \<equiv> \<not>(val_to_bool (val[!e]))"
  using intval_logic_negation.simps unfolding logic_negate_def
  sorry
(* WAS:
  by (smt (verit, best) Value.collapse(1) is_IntVal_def val_to_bool.simps(1) val_to_bool.simps(2) zero_neq_one)
*)

lemma negation_condition_intval: 
(* WAS:
  assumes "e \<noteq> UndefVal \<and> \<not>(is_ObjRef e) \<and> \<not>(is_ObjStr e)"
*)
  assumes "e = IntVal b ie"
  assumes "0 < b"
  shows "val[(!e) ? x : y] = val[e ? y : x]"
  using assms by (cases e; auto simp: negates logic_negate_def)

optimization NegateConditionFlipBranches: "((!e) ? x : y) \<longmapsto> (e ? y : x)"
    apply simp using negation_condition_intval
  by (smt (verit, ccfv_SIG) ConditionalExpr ConditionalExprE Value.collapse Value.exhaust_disc evaltree_not_undef intval_logic_negation.simps(4) intval_logic_negation.simps negates unary_eval.simps(4) unfold_unary)

optimization DefaultTrueBranch: "(true ? x : y) \<longmapsto> x" .

optimization DefaultFalseBranch: "(false ? x : y) \<longmapsto> y" .

optimization ConditionalEqualBranches: "(e ? x : x) \<longmapsto> x" .

(* this will be removable after some work *)
definition wff_stamps :: bool where
  "wff_stamps = (\<forall>m p expr val . ([m,p] \<turnstile> expr \<mapsto> val) \<longrightarrow> valid_value val (stamp_expr expr))"

definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

(*
lemma stamp_under_defn:
  assumes "stamp_under (stamp_expr x) (stamp_expr y)"
  assumes "wf_stamp x \<and> wf_stamp y"
  assumes "([m, p] \<turnstile> x \<mapsto> xv) \<and> ([m, p] \<turnstile> y \<mapsto> yv)"
  shows "val_to_bool val[xv < yv]"
proof -
  have xval: "valid_value xv (stamp_expr x)"
    using assms wf_stamp_def by blast
  have yval: "valid_value yv (stamp_expr y)"
    using assms wf_stamp_def by blast
  show ?thesis using xval yval
    apply (cases "stamp_expr x"; cases "stamp_expr y"; auto simp: valid_value.simps)
    using assms(1) unfolding stamp_under.simps sorry
qed
    

optimization condition_bounds_x: "((u < v) ? x : y) \<longmapsto> x 
    when (stamp_under (stamp_expr u) (stamp_expr v) \<and> wf_stamp u \<and> wf_stamp v)"
  apply simp apply (rule impI) apply (rule allI)+ apply (rule impI)
  using stamp_under_defn
  by force
  by (metis intval_less_than.simps(15) stamp_under.elims(3) val_to_bool.simps(3))
  apply (smt (verit, best) ConditionalExprE le_expr_def stamp_under.simps)
  unfolding size.simps by simp

optimization condition_bounds_y: "((x < y) ? x : y) \<longmapsto> y 
    when (stamp_under (stamp_expr y) (stamp_expr x) \<and> wf_stamp x \<and> wf_stamp y)"
   apply unfold_optimization
  using stamp_under_semantics_inversed
  using wf_stamp_def
  apply (smt (verit, best) ConditionalExprE le_expr_def stamp_under.simps)
  unfolding size.simps by simp

(*extra one*)
optimization b[intval]: "((x eq y) ? x : y) \<longmapsto> y"
   apply unfold_optimization
    apply (smt (z3) bool_to_val.simps(2) intval_equals.elims val_to_bool.simps(1) val_to_bool.simps(3))
    unfolding intval.simps
    apply (smt (z3) BinaryExprE ConditionalExprE Value.inject(1) Value.inject(2) bin_eval.simps(10) bool_to_val.simps(2) evalDet intval_equals.simps(1) intval_equals.simps(10) intval_equals.simps(12) intval_equals.simps(15) intval_equals.simps(16) intval_equals.simps(2) intval_equals.simps(5) intval_equals.simps(8) intval_equals.simps(9) le_expr_def val_to_bool.cases val_to_bool.elims(2))
  unfolding size.simps by auto
*)


(** Start of new proofs **)

(* Value-level proofs *)
lemma val_optimise_integer_test: 
  assumes "is_IntVal32 x"
  shows "intval_conditional (intval_equals val[(x & (IntVal32 1))] (IntVal32 0)) 
         (IntVal32 0) (IntVal32 1) = 
         val[x & IntVal32 1]"
   apply simp_all 
  apply auto 
  using bool_to_val.elims intval_equals.elims val_to_bool.simps(1) val_to_bool.simps(3)
  sorry

optimization ConditionalEliminateKnownLess: "((x < y) ? x : y) \<longmapsto> x 
                                 when (stamp_under (stamp_expr x) (stamp_expr y)
                                      \<and> wf_stamp x \<and> wf_stamp y)"
       apply auto
    using stamp_under.simps wf_stamp_def val_to_bool.simps 
    sorry

(* Optimisations *)
optimization ConditionalEqualIsRHS: "((x eq y) ? x : y) \<longmapsto> y"
   apply simp_all apply auto using Canonicalization.intval.simps(1) evalDet 
          intval_conditional.simps evaltree_not_undef
  by (metis (no_types, opaque_lifting) Value.discI(2) Value.distinct(1) intval_and.simps(3) intval_equals.simps(2) val_optimise_integer_test val_to_bool.simps(2))

(* todo not sure if this is done properly *)
optimization normalizeX: "((x eq const (IntVal 32 0)) ? 
                                (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> x
                                when (x = ConstantExpr (IntVal 32 0) | (x = ConstantExpr (IntVal 32 1)))" 
  done

(* todo not sure if this is done properly *)
optimization normalizeX2: "((x eq (const (IntVal 32 1))) ? 
                                 (const (IntVal 32 1)) : (const (IntVal 32 0))) \<longmapsto> x
                                 when (x = ConstantExpr (IntVal 32 0) | (x = ConstantExpr (IntVal 32 1)))"
  done

(* todo not sure if this is done properly *)
optimization flipX: "((x eq (const (IntVal 32 0))) ? 
                           (const (IntVal 32 1)) : (const (IntVal 32 0))) \<longmapsto> 
                            x \<oplus> (const (IntVal 32 1))
                            when (x = ConstantExpr (IntVal 32 0) | (x = ConstantExpr (IntVal 32 1)))"
  done

(* todo not sure if this is done properly *)
optimization flipX2: "((x eq (const (IntVal 32 1))) ? 
                            (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> 
                            x \<oplus> (const (IntVal 32 1))
                            when (x = ConstantExpr (IntVal 32 0) | (x = ConstantExpr (IntVal 32 1)))"
  done


optimization OptimiseIntegerTest: 
     "(((x & (const (IntVal 32 1))) eq (const (IntVal 32 0))) ? 
      (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> 
       x & (const (IntVal 32 1))
       when (stamp_expr x = default_stamp)"
   apply simp_all 
   apply auto
  using val_optimise_integer_test  sorry

(* todo not sure if this is done properly *)
optimization opt_optimise_integer_test_2: 
     "(((x & (const (IntVal 32 1))) eq (const (IntVal 32 0))) ? 
                   (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> 
                   x
                   when (x = ConstantExpr (IntVal 32 0) | (x = ConstantExpr (IntVal 32 1)))"
  done

optimization opt_conditional_eliminate_known_less: "((x < y) ? x : y) \<longmapsto> x 
                                 when (((stamp_under (stamp_expr x) (stamp_expr y)) |
                                      ((stpi_upper (stamp_expr x)) = (stpi_lower (stamp_expr y))))
                                      \<and> wf_stamp x \<and> wf_stamp y)"
   unfolding le_expr_def apply auto
  using stamp_under.simps wf_stamp_def 
  sorry


(*
optimization opt_normalize_x_original: "((BinaryExpr BinIntegerEquals x (ConstantExpr (IntVal32 0))) ? 
                                (ConstantExpr (IntVal32 0)) : (ConstantExpr (IntVal32 1))) \<longmapsto> x
                                when (stamp_expr x = IntegerStamp 32 0 1 \<and> 
                                      wf_stamp x)"
   apply unfold_optimization apply simp_all
  using wf_stamp_def apply (cases x; simp) 
  
  sorry
*)

(** End of new proofs **)

end

end
