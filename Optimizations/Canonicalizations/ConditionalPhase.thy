subsection \<open>ConditionalNode Phase\<close>

theory ConditionalPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase ConditionalNode
  terminating size
begin

(* Helpers *)
lemma preserve_boolean:
  assumes "is_boolean c"
  shows "is_boolean exp[!c]"
  using assms unfolding is_boolean_def val_is_boolean_def bool_values_def apply auto
  by (metis (no_types, opaque_lifting) intval_logic_negation.simps(1) logic_negate_def new_int_zero
      IntVal1)

lemma negation_preserve_eval0:
  assumes "[m, p] \<turnstile> exp[e] \<mapsto> v"
  assumes "is_boolean e"
  shows "\<exists>v'. ([m, p] \<turnstile> exp[!e] \<mapsto> v')"
  using assms
proof -
  obtain b vv where vIntVal: "v = IntVal b vv"
    using is_boolean_def assms unfolding val_is_boolean_def bool_values_def by blast
  then show ?thesis
    using assms(1) by fastforce
qed

lemma negation_preserve_eval2:
  assumes "[m, p] \<turnstile> exp[e] \<mapsto> v"
  assumes "is_boolean e"
  shows "\<exists>v'. ([m, p] \<turnstile> exp[!e] \<mapsto> v') \<and> v = val[!v']"
  using assms
proof -
  obtain notEval where notEval: "([m, p] \<turnstile> exp[!e] \<mapsto> notEval)"
    by (metis assms negation_preserve_eval0)
  then have logicNegateEquiv: "notEval = intval_logic_negation v"
    using evalDet assms(1) unary_eval.simps(4) by blast
  then have vRange: "v = val[false] \<or> v = val[true]"
    using assms by (auto simp add: is_boolean_def val_is_boolean_def bool_values_def)
  have "v = intval_logic_negation notEval"
    using assms(1,2) intval_logic_negation_bool_self is_boolean_def logicNegateEquiv by auto
  then show ?thesis
    using notEval by auto
qed

(* Value level proofs *)
lemma negates: "\<exists>v b. e = IntVal b v \<and> b > 0 \<Longrightarrow> val_to_bool (val[e]) \<longleftrightarrow> \<not>(val_to_bool (val[!e]))"
  by (metis (mono_tags, lifting) intval_logic_negation.simps(1) logic_negate_def new_int.simps
      of_bool_eq(2) one_neq_zero take_bit_of_0 take_bit_of_1 val_to_bool.simps(1))

lemma negation_condition_intval: 
  assumes "e = IntVal b ie"
  assumes "0 < b"
  shows "val[(!e) ? x : y] = val[e ? y : x]"
  by (metis assms intval_conditional.simps negates)

lemma val_optimise_integer_test:
  assumes "\<exists>v. x = IntVal 32 v"
  shows "val[((x & true) eq false) ? false : true] = val[x & true]"
  using assms apply auto
  apply (metis (full_types) bool_to_val.simps(2) val_to_bool.simps(1))
  by (metis (mono_tags, lifting) bool_to_val.simps(1) val_to_bool.simps(1) even_iff_mod_2_eq_zero
      odd_iff_mod_2_eq_one and_one_eq)

lemma intval_self_is_true:
  assumes "y = IntVal b yv"
  shows "val[y eq y] = val[true]"
  using assms by (cases yv; auto)

(* Exp level proofs *)
lemma negation_preserve_eval:
  assumes "[m, p] \<turnstile> exp[!e] \<mapsto> v"
  shows "\<exists>v'. ([m, p] \<turnstile> exp[e] \<mapsto> v') \<and> v = val[!v']"
  using assms by auto

lemma negation_preserve_eval_intval:
  assumes "[m, p] \<turnstile> exp[!e] \<mapsto> v"
  shows "\<exists>v' b vv. ([m, p] \<turnstile> exp[e] \<mapsto> v') \<and> v' = IntVal b vv \<and> b > 0"
  by (metis assms eval_bits_1_64 intval_logic_negation.elims negation_preserve_eval unfold_unary)

text \<open>Optimisations\<close>

optimization NegateConditionFlipBranches: "((!e) ? x : y) \<longmapsto> (e ? y : x)"
  by (smt (z3) le_expr_def ConditionalExpr ConditionalExprE Value.distinct(1) evalDet negates
      negation_preserve_eval negation_preserve_eval_intval)

optimization DefaultTrueBranch: "(true ? x : y) \<longmapsto> x" .

optimization DefaultFalseBranch: "(false ? x : y) \<longmapsto> y" .

optimization ConditionalEqualBranches: "(e ? x : x) \<longmapsto> x" .

optimization condition_bounds_x: "((u < v) ? x : y) \<longmapsto> x
    when (stamp_under (stamp_expr u) (stamp_expr v) \<and> wf_stamp u \<and> wf_stamp v)"
  using stamp_under_defn by fastforce

optimization condition_bounds_y: "((u < v) ? x : y) \<longmapsto> y
    when (stamp_under (stamp_expr v) (stamp_expr u) \<and> wf_stamp u \<and> wf_stamp v)"
  using stamp_under_defn_inverse by fastforce

(* TODO update condition, stamp_under uses < but compiler is <= *)
optimization ConditionalEliminateKnownLess: "((x < y) ? x : y) \<longmapsto> x
                       when (stamp_under (stamp_expr x) (stamp_expr y) \<and> wf_stamp x \<and> wf_stamp y)"
  using stamp_under_defn by fastforce

optimization ConditionalIntegerEquals_1: "((c ? x : y) eq x) \<longmapsto> c
                                          when stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x \<and>
                                               stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y \<and>
                                               (alwaysDistinct (stamp_expr x) (stamp_expr y)) \<and>
                                               is_boolean c"
  apply (metis dual_order.strict_trans size_bin_lhs size_cond_gt_cond) apply auto
  subgoal premises p for m p cExpr xv cond
  proof -
    obtain cond where cond: "[m,p] \<turnstile> c \<mapsto> cond"
      using p by blast
    have cRange: "cond = val[false] \<or> cond = val[true]"
      using p cond is_boolean_def unfolding val_is_boolean_def bool_values_def by blast
    then obtain yv where yVal: "[m,p] \<turnstile> y \<mapsto> yv"
      using p(15) by auto
    obtain xvv where xvv: "xv = IntVal b xvv"
      by (metis p(1,2,7) valid_int wf_stamp_def)
    obtain yvv where yvv: "yv = IntVal b yvv"
      by (metis ExpIntBecomesIntVal p(3,4) wf_stamp_def yVal)
    have yxDiff: "xvv \<noteq> yvv"
      by (smt (verit, del_insts) yVal xvv wf_stamp_def valid_int_signed_range p yvv)
    have "val[yv eq xv] = val[false]"
      unfolding xvv yvv apply auto by (metis (mono_tags) bool_to_val.simps(2) yxDiff)
    then have valEvalSame: "cond =  val[(cond ? xv : yv) eq xv]"
      apply (cases "cond = val[false]"; simp) using cRange xvv by auto
    then have condTrue: "val_to_bool cond \<Longrightarrow> cExpr = xv"
      by (metis (mono_tags, lifting) cond evalDet p(7,9,11))
    then have "\<not>(val_to_bool cond) \<Longrightarrow> cExpr = yv"
      by (metis (full_types) cond evalDet p(9,11) yVal)
    then show ?thesis
      using cond condTrue valEvalSame by fastforce
  qed
  done

optimization ConditionalIntegerEquals_2: "((c ? x : y) eq y) \<longmapsto> (!c)
                                          when stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x \<and>
                                               stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y \<and>
                                               (alwaysDistinct (stamp_expr x) (stamp_expr y)) \<and>
                                               is_boolean c"
  apply (meson less_trans_Suc size_bin_lhs size_cond_gt_cond) apply auto
  subgoal premises p for m p cExpr yv cond trE faE
  proof -
    obtain cond where cond: "[m,p] \<turnstile> c \<mapsto> cond"
      using p by blast
    then obtain notCond where notCond: "[m,p] \<turnstile> exp[!c] \<mapsto> notCond"
      by (meson p(6) negation_preserve_eval2 cond)
    have cRange: "cond = val[false] \<or> cond = val[true]"
      using p cond by (simp add: is_boolean_def val_is_boolean_def bool_values_def)
    then have cNotRange: "notCond = val[false] \<or> notCond = val[true]"
      by (metis (no_types, lifting) IntVal0 IntVal1 cond evalDet intval_logic_negation.simps(1)
          logic_negate_def negation_preserve_eval notCond)
    then obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p by auto
    then have trueCond: "(notCond = val[true]) \<Longrightarrow> [m,p] \<turnstile> (ConditionalExpr c x y) \<mapsto> yv"
      by (smt (verit, ccfv_SIG) cRange negates negation_preserve_eval2 notCond ConditionalExpr cond
          evalDet val_to_bool.simps(1) eval_bits_1_64 p(10,13,14,15,16,6,7,9))
    obtain xvv where xvv: "xv = IntVal b xvv"
      by (metis p(1,2) valid_int wf_stamp_def xv)
    then have opposites: "notCond = intval_logic_negation cond"
      by (metis cond evalDet negation_preserve_eval notCond)
    then have negate: "(intval_logic_negation cond = val[false]) \<Longrightarrow> (cond = val[true])"
      using cRange intval_logic_negation.simps negates by fastforce
    have falseCond: "(notCond = val[false]) \<Longrightarrow> [m,p] \<turnstile> (ConditionalExpr c x y) \<mapsto> xv"
      unfolding opposites using negate cond evalDet p(13,14,15,16) xv by auto
    obtain yvv where yvv: "yv = IntVal b yvv"
      by (metis p(3,4,7) wf_stamp_def ExpIntBecomesIntVal)
    have yxDiff: "xv \<noteq> yv"
      by (metis linorder_not_less max.absorb1 max.absorb4 max_less_iff_conj min_def xv yvv
          wf_stamp_def valid_int_signed_range p(1,2,3,4,5,7))
    then have trueEvalCond: "(cond = val[false]) \<Longrightarrow> [m,p] \<turnstile> exp[(c ? x : y) eq y] \<mapsto> val[yv eq yv]"
      by (smt (verit) cNotRange trueCond ConditionalExprE cond bin_eval.simps(13) evalDet p
          falseCond unfold_binary val_to_bool.simps(1))
    then have falseEval: "(notCond = val[false]) \<Longrightarrow> [m,p] \<turnstile> exp[(c ? x : y) eq y] \<mapsto> val[xv eq yv]"
      using p by (metis ConditionalExprE bin_eval.simps(13) evalDet falseCond unfold_binary)
    have eqEvalFalse: "val[yv eq xv] = val[false]"
      unfolding xvv yvv apply auto by (metis (mono_tags) bool_to_val.simps(2) yxDiff yvv xvv)
    have "[m,p] \<turnstile> exp[(c ? x : y) eq y] \<mapsto> notCond"
      by (metis cNotRange cRange eqEvalFalse falseEval intval_self_is_true negates opposites yvv
          trueEvalCond val_eq_commutative zero_less_numeral)
    then show ?thesis
      by (metis cNotRange falseEval notCond trueCond falseCond intval_self_is_true p(9,11) evalDet
          yvv ConditionalExprE)
  qed
  done

optimization ConditionalExtractCondition: "(c ? true : false) \<longmapsto> c when is_boolean c"
  using is_boolean_def unfolding val_is_boolean_def bool_values_def by fastforce

optimization ConditionalExtractCondition2: "(c ? false : true) \<longmapsto> !c when is_boolean c"
  apply auto subgoal premises p for m p cExpr cond
  proof -
    obtain cond where cond: "[m,p] \<turnstile> c \<mapsto> cond"
      using p(2) by auto
    obtain notCond where notCond: "[m,p] \<turnstile> exp[!c] \<mapsto> notCond"
      by (metis cond negation_preserve_eval2 p(1))
    then have cRange: "cond = val[false] \<or> cond = val[true]"
      using is_boolean_def cond p(1) unfolding val_is_boolean_def bool_values_def by auto
    then have condTrue: "cond = val[true] \<Longrightarrow> cExpr = val[false]"
      using cond evalDet p(2) p(4) by fastforce
    then have "cond = val[false] \<Longrightarrow> cExpr = val[true]"
      using p cond evalDet by fastforce
    then have "notCond = cExpr"
      by (metis (no_types, lifting) IntVal0 IntVal1 cRange cond condTrue evalDet notCond
          intval_logic_negation.simps(1) logic_negate_def negation_preserve_eval)
    then show ?thesis
      using notCond by auto
  qed
  done

optimization ConditionalEqualIsRHS: "((x eq y) ? x : y) \<longmapsto> y"
  apply auto subgoal premises p for m p v true false xa ya
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(8) by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p(9) by auto
    have notUndef: "xv \<noteq> UndefVal \<and> yv \<noteq> UndefVal"
      using evaltree_not_undef xv yv by blast
    have evalNotUndef: "val[xv eq yv] \<noteq> UndefVal"
      by (metis evalDet p(1,8,9) xv yv)
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis Value.exhaust evalNotUndef intval_equals.simps(3,4,5) notUndef)
    obtain yb yvv where yvv: "yv = IntVal yb yvv"
      by (metis evalNotUndef intval_equals.simps(7,8,9) intval_logic_negation.cases notUndef)
    obtain vv where evalLHS: "[m,p] \<turnstile> if val_to_bool (val[xv eq yv]) then x else y \<mapsto> vv"
      by (metis (full_types) p(4) yv)
    obtain equ where equ: "equ = val[xv eq yv]"
      by fastforce
    have trueEval: "equ = val[true] \<Longrightarrow> vv = xv"
      using evalLHS by (simp add: evalDet xv equ)
    have falseEval: "equ = val[false] \<Longrightarrow> vv = yv"
      using evalLHS by (simp add: evalDet yv equ)
    then have "vv = v"
      by (metis evalDet evalLHS p(2,8,9) xv yv)
    then show ?thesis
      by (metis (full_types) bool_to_val.simps(1,2) bool_to_val_bin.simps equ evalNotUndef falseEval
          intval_equals.simps(1) trueEval xvv yv yvv)
  qed
  done

(* TODO may require more complex stamp definition *)
optimization normalizeX: "((x eq const val[false]) ? (const val[false]) : (const val[true])) \<longmapsto> x
                            when stamp_expr x = IntegerStamp 32 0 1 \<and> wf_stamp x \<and> is_boolean x"
  apply auto
  subgoal premises p for m p v
    proof -
      obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
        using p by blast
      have eval: "[m,p] \<turnstile> if val_to_bool (val[xa eq false])
                           then ConstantExpr val[false]
                           else ConstantExpr val[true] \<mapsto> v"
        using evalDet p(3,4,5,6,7) xa by blast
      then have xaRange: "xa = val[false] \<or> xa = val[true]"
        using is_boolean_def val_is_boolean_def bool_values_def p(3) xa by blast
      then have "v = xa"
        using eval by auto
      then show ?thesis
        by (auto simp: xa)
    qed
  done

(* TODO may require more complex stamp definition *)
optimization normalizeX2: "((x eq (const val[true])) ? (const val[true]) : (const val[false])) \<longmapsto> x
                             when (x = ConstantExpr val[false] | (x = ConstantExpr val[true]))" .

(* TODO may require more complex stamp definition *)
optimization flipX: "((x eq (const val[false])) ? (const val[true]) : (const val[false])) \<longmapsto>
                       x \<oplus> (const val[true])
                       when (x = ConstantExpr val[false] | (x = ConstantExpr val[true]))" .

(* TODO may require more complex stamp definition *)
optimization flipX2: "((x eq (const val[true])) ? (const val[false]) : (const val[true])) \<longmapsto>
                        x \<oplus> (const val[true])
                        when (x = ConstantExpr val[false] | (x = ConstantExpr val[true]))" .

optimization OptimiseIntegerTest:
     "(((x & (const val[true])) eq (const val[false])) ? (const val[false]) : (const val[true])) \<longmapsto>
         x & (const val[true])
         when (stamp_expr x = default_stamp \<and> wf_stamp x)"
  apply (simp; rule impI; (rule allI)+; rule impI)
  subgoal premises eval for m p v
proof -
  obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
    using eval by fast
  then have x32: "\<exists>v. xv = IntVal 32 v"
    using stamp_of_default eval by auto
  obtain lhs where lhs: "[m, p] \<turnstile> exp[(((x & (const val[true])) eq (const val[false])) ?
                                      (const val[false]) : (const val[true]))] \<mapsto> lhs"
    using eval(2) by auto
  then have lhsV: "lhs = val[((xv & true) eq false) ? false : true]"
    by (smt (verit, del_insts) ConditionalExprE ConstantExprE evalDet xv intval_conditional.simps
        unfold_binary bin_eval.simps(6,13))
  obtain rhs where rhs: "[m, p] \<turnstile> exp[x & (const val[true])] \<mapsto> rhs"
    using eval(2) by blast
  then have rhsV: "rhs = val[xv & true]"
    by (metis BinaryExprE ConstantExprE bin_eval.simps(6) evalDet xv)
  then show ?thesis
    by (metis eval(2) evalDet lhs lhsV rhs val_optimise_integer_test x32)
qed
  done

(** End of new proofs **)

end (* End of ConditionalPhase *)

end (* End of file *)