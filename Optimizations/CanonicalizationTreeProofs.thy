section \<open>Canonicalization Phase\<close>

theory CanonicalizationTreeProofs
  imports
    CanonicalizationTree
    Semantics.IRTreeEvalThms
begin

lemma valid32or64:
  assumes "valid_value (IntegerStamp b lo hi) x"
  shows "(\<exists> v1. (x = IntVal32 v1)) \<or> (\<exists> v2. (x = IntVal64 v2))"
  using valid32 valid64 assms valid_value.elims(2) by blast

lemma valid32or64_both:
  assumes "valid_value (IntegerStamp b lox hix) x"
  and "valid_value (IntegerStamp b loy hiy) y"
  shows "(\<exists> v1 v2. x = IntVal32 v1 \<and> y = IntVal32 v2) \<or> (\<exists> v3 v4. x = IntVal64 v3 \<and> y = IntVal64 v4)"
  using assms valid32or64 valid32 valid_value.elims(2) valid_value.simps(1) by metis

(* -(-x) = x *)
lemma double_negate_refinement:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "stamp_expr expr = IntegerStamp b lo hi"
  shows "(UnaryExpr UnaryNeg (UnaryExpr UnaryNeg (expr))) \<le> expr"
proof -
  have "valid_value (IntegerStamp b lo hi) val"
    by (metis assms int_stamp_implies_valid_value)
  moreover have "x = intval_negate (intval_negate x)" if "valid_value (IntegerStamp b lo hi) x" for x
    using valid32or64 that by fastforce
  ultimately show ?thesis using assms by (auto; (metis int_stamp_implies_valid_value)+)
qed


(* -(x-y) = (x-y) *)
lemma negate_xsuby_helper:
  assumes "valid_value (IntegerStamp b lox hix) x"
  and "valid_value (IntegerStamp b loy hiy) y"
  shows "intval_negate (intval_sub x y) = intval_sub y x"
proof -
  have "(\<exists> v1 v2. x = IntVal32 v1 \<and> y = IntVal32 v2) \<or> (\<exists> v3 v4. x = IntVal64 v3 \<and> y = IntVal64 v4)"
    using valid32or64_both assms by auto
  thus ?thesis by auto
qed

lemma neg_sub_refinement:
  assumes "[m,p] \<turnstile> x \<mapsto> xval"
  assumes "[m,p] \<turnstile> y \<mapsto> yval"
  assumes "stamp_expr x = IntegerStamp b lox hix"
  assumes "stamp_expr y = IntegerStamp b loy hiy"
  shows "(UnaryExpr UnaryNeg (BinaryExpr BinSub x y)) \<le> (BinaryExpr BinSub y x)"
  unfolding le_expr_def
  by (smt (verit, ccfv_threshold) assms negate_xsuby_helper int_stamp_implies_valid_value
        evaltree.simps BinaryExprE UnaryExprE bin_eval.simps(3) unary_eval.simps(6))

lemma CanonicalizeNegateProof:
  assumes "CanonicalizeNegate before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeNegate.induct)
  case (negate_negate nx x)
  thus ?case using double_negate_refinement
    by (metis evalDet is_IntegerStamp_def le_expr_def negate_negate.hyps(1) negate_negate.prems(1) negate_negate.prems(2))
next
  case (negate_sub e x y stampx stampy)
  thus ?case
    using assms neg_sub_refinement le_expr_def evalDet is_IntegerStamp_def negate_sub.hyps negate_sub.prems
    by (smt (verit, ccfv_SIG) BinaryExprE Stamp.collapse(1))
qed

end