theory NewAnd
  imports
    Common
    "HOL-Library.FSet"
    Semantics.IRTreeEvalThms
begin

lemma bin_distribute_and_over_or:
  "and z (or x y) = or (and z x) (and z y)"
  by (smt (verit, best) bit_and_iff bit_eqI bit_or_iff)

lemma intval_distribute_and_over_or:
  "val[z & (x | y)] = val[(z & x) | (z & y)]"
  apply (cases x; cases y; cases z; auto)
  by (simp add: bit.conj_disj_distrib)+

lemma exp_distribute_and_over_or:
  "exp[z & (x | y)] \<ge> exp[(z & x) | (z & y)]"
  apply simp using intval_distribute_and_over_or
  using BinaryExpr bin_eval.simps(4,5)
  using intval_or.simps(10) intval_or.simps(3)
  by fastforce


lemma intval_and_commute:
  "val[x & y] = val[y & x]"
  by (cases x; cases y; auto simp: and.commute)

lemma intval_or_commute:
  "val[x | y] = val[y | x]"
  by (cases x; cases y; auto simp: or.commute)

lemma intval_xor_commute:
  "val[x \<oplus> y] = val[y \<oplus> x]"
  by (cases x; cases y; auto simp: xor.commute)

lemma exp_and_commute:
  "exp[x & z] \<ge> exp[z & x]"
  apply simp using intval_and_commute by auto

lemma exp_or_commute:
  "exp[x | y] \<ge> exp[y | x]"
  apply simp using intval_or_commute by auto

lemma exp_xor_commute:
  "exp[x \<oplus> y] \<ge> exp[y \<oplus> x]"
  apply simp using intval_xor_commute by auto


lemma bin_eliminate_y:
  assumes "and y z = 0"
  shows "and (or x y) z = and x z"
  using assms
  by (simp add: and.commute bin_distribute_and_over_or)

lemma intval_eliminate_y_64:
  assumes "val[y & z] = IntVal64 0"
  shows "val[(x | y) & z] = val[x & z]"
  using assms bin_eliminate_y by (cases x; cases y; cases z; auto)

lemma intval_eliminate_y_32:
  assumes "val[y & z] = IntVal32 0"
  shows "val[(x | y) & z] = val[x & z]"
  using assms bin_eliminate_y by (cases x; cases y; cases z; auto)


lemma intval_and_associative:
  "val[(x & y) & z] = val[x & (y & z)]"
  apply (cases x; cases y; cases z; auto)
  by (simp add: and.assoc)+

lemma intval_or_associative:
  "val[(x | y) | z] = val[x | (y | z)]"
  apply (cases x; cases y; cases z; auto)
  by (simp add: or.assoc)+

lemma intval_xor_associative:
  "val[(x \<oplus> y) \<oplus> z] = val[x \<oplus> (y \<oplus> z)]"
  apply (cases x; cases y; cases z; auto)
  by (simp add: xor.assoc)+

lemma exp_and_associative:
  "exp[(x & y) & z] \<ge> exp[x & (y & z)]"
  apply simp using intval_and_associative by fastforce

lemma exp_or_associative:
  "exp[(x | y) | z] \<ge> exp[x | (y | z)]"
  apply simp using intval_or_associative by fastforce

lemma exp_xor_associative:
  "exp[(x \<oplus> y) \<oplus> z] \<ge> exp[x \<oplus> (y \<oplus> z)]"
  apply simp using intval_xor_associative by fastforce


lemma intval_and_absorb_or:
  assumes "val[x & (x | y)] \<noteq> UndefVal"
  shows "val[x & (x | y)] = val[x]"
  using assms by (cases x; cases y; auto)

lemma intval_or_absorb_and:
  assumes "val[x | (x & y)] \<noteq> UndefVal"
  shows "val[x | (x & y)] = val[x]"
  using assms by (cases x; cases y; auto)

lemma exp_and_absorb_or:
  "exp[x & (x | y)] \<ge> exp[x]"
  apply simp using intval_and_absorb_or
  by (smt (verit, best) BinaryExprE bin_eval.simps(4) bin_eval.simps(5) evalDet)

lemma exp_or_absorb_and:
  "exp[x | (x & y)] \<ge> exp[x]"
  apply simp using intval_or_absorb_and
  by (smt (verit) BinaryExprE bin_eval.simps(4) bin_eval.simps(5) evalDet)

context
  includes bit_operations_syntax
begin
definition IRExpr_up :: "IRExpr \<Rightarrow> int64" where
  "IRExpr_up e = NOT 0"

definition IRExpr_down :: "IRExpr \<Rightarrow> int64" where
  "IRExpr_down e = 0"
end

lemma negative_all_set_32:
  "n < 32 \<Longrightarrow> bit (-1::int32) n"
  apply transfer by auto

locale stamp_mask =
  fixes up :: "IRExpr \<Rightarrow> int64" ("\<up>")
  fixes down :: "IRExpr \<Rightarrow> int64" ("\<down>")
  assumes up_spec32: "[m, p] \<turnstile> e \<mapsto> IntVal32 v \<Longrightarrow> (and v (not ((ucast (\<up>e))))) = 0"
      and up_spec64: "[m, p] \<turnstile> e \<mapsto> IntVal64 v' \<Longrightarrow> (and v' (not (\<up>e))) = 0"
      and down_spec32: "[m, p] \<turnstile> e \<mapsto> IntVal32 v \<Longrightarrow> (and (not v) (ucast (\<down>e))) = 0"
      and down_spec64: "[m, p] \<turnstile> e \<mapsto> IntVal64 v' \<Longrightarrow> (and (not v') (\<down>e)) = 0"
begin

lemma may_implies_either_32:
  "[m, p] \<turnstile> e \<mapsto> IntVal32 v \<Longrightarrow> bit (\<up>e) n \<Longrightarrow> bit v n = False \<or> bit v n = True"
  by simp
lemma may_implies_either_64:
  "[m, p] \<turnstile> e \<mapsto> IntVal64 v \<Longrightarrow> bit (\<up>e) n \<Longrightarrow> bit v n = False \<or> bit v n = True"
  by simp

lemma not_may_implies_false_32:
  "[m, p] \<turnstile> e \<mapsto> IntVal32 v \<Longrightarrow> \<not>(bit (\<up>e) n) \<Longrightarrow> bit v n = False"
  using up_spec32 
  using bit_and_iff bit_eq_iff bit_not_iff bit_unsigned_iff down_spec32
  by (smt (verit, best) bit.double_compl)
lemma not_may_implies_false_64:
  "[m, p] \<turnstile> e \<mapsto> IntVal64 v \<Longrightarrow> \<not>(bit (\<up>e) n) \<Longrightarrow> bit v n = False"
  using up_spec64
  using bit_and_iff bit_eq_iff bit_not_iff bit_unsigned_iff down_spec64
  by (smt (verit, best) bit.double_compl)

lemma must_implies_true_32:
  "[m, p] \<turnstile> e \<mapsto> IntVal32 v \<Longrightarrow> n < 32 \<Longrightarrow> bit (\<down>e) n \<Longrightarrow> bit v n = True"
  using down_spec32
  by (metis bit.compl_zero bit_and_iff bit_not_iff bit_unsigned_iff negative_all_set_32)
lemma must_implies_true_64:
  "[m, p] \<turnstile> e \<mapsto> IntVal64 v \<Longrightarrow> bit (\<down>e) n \<Longrightarrow> bit v n = True"
  using down_spec64
  by (metis bit.compl_zero bit_and_iff bit_minus_1_iff bit_not_iff_eq impossible_bit)

lemma not_must_implies_either_32:
  "[m, p] \<turnstile> e \<mapsto> IntVal32 v \<Longrightarrow> \<not>(bit (\<down>e) n) \<Longrightarrow> bit v n = False \<or> bit v n = True"
  by simp
lemma not_must_implies_either_64:
  "[m, p] \<turnstile> e \<mapsto> IntVal64 v \<Longrightarrow> \<not>(bit (\<down>e) n) \<Longrightarrow> bit v n = False \<or> bit v n = True"
  by simp

lemma must_implies_may_32:
  "[m, p] \<turnstile> e \<mapsto> IntVal32 v \<Longrightarrow> n < 32 \<Longrightarrow> bit (\<down>e) n \<Longrightarrow> bit (\<up>e) n"
  by (meson must_implies_true_32 not_may_implies_false_32)
lemma must_implies_may_64:
  "[m, p] \<turnstile> e \<mapsto> IntVal64 v \<Longrightarrow> bit (\<down>e) n \<Longrightarrow> bit (\<up>e) n"
  by (meson must_implies_true_64 not_may_implies_false_64)

lemma zero_anded_up_zero_value_32:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal32 xv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal32 yv"
  shows "and xv yv = 0"
  using assms
  by (smt (verit) and.commute bit.compl_one bit.compl_zero bit.conj_disj_distrib bit.de_Morgan_disj or_eq_not_not_and stamp_mask.up_spec32 stamp_mask_axioms ucast_0 unsigned_and_eq word_log_esimps(3) word_not_dist(2))

lemma zero_anded_up_zero_value_64:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal64 xv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal64 yv"
  shows "and xv yv = 0"
  using assms
  by (smt (verit) and_eq_not_not_or bit.conj_disj_distrib bit.conj_disj_distrib2 stamp_mask.up_spec64 stamp_mask_axioms word_ao_absorbs(2) word_ao_absorbs(8) word_log_esimps(3) word_not_dist(2))

lemma intval_stepup_32:
  assumes "and xv yv = 0"
  assumes "intval_and (IntVal32 xv) (IntVal32 yv) \<noteq> UndefVal"
  shows "(intval_and (IntVal32 xv) (IntVal32 yv)) = IntVal32 0"
  using assms
  by force

lemma intval_stepup_64:
  assumes "and xv yv = 0"
  assumes "intval_and (IntVal64 xv) (IntVal64 yv) \<noteq> UndefVal"
  shows "(intval_and (IntVal64 xv) (IntVal64 yv)) = IntVal64 0"
  using assms
  by force

lemma zero_anded_up_zero_value_intval:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> xv"
  assumes "[m, p] \<turnstile> y \<mapsto> yv"
  assumes "intval_and xv yv \<noteq> UndefVal"
  shows "intval_and xv yv = IntVal32 0 \<or> intval_and xv yv = IntVal64 0"
  using assms apply (cases xv; cases yv; auto)
  using zero_anded_up_zero_value_32 apply presburger
  using zero_anded_up_zero_value_64 by blast

lemma opt_semantics:
  "and (\<up>y) (\<up>z) = 0 \<longrightarrow> BinaryExpr BinAnd (BinaryExpr BinOr x y) z \<ge> BinaryExpr BinAnd x z"
  apply simp apply (rule impI; rule allI; rule allI; rule allI)
  subgoal premises p for m p v apply (rule impI) subgoal premises e
    proof -
      obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
        using e by auto
      obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
        using e by auto
      obtain zv where zv: "[m,p] \<turnstile> z \<mapsto> zv"
        using e by auto
      have and_or_is_def: "intval_and (intval_or xv yv) zv \<noteq> UndefVal"
        using e 
        by (smt (verit, best) BinaryExprE bin_eval.simps(4) bin_eval.simps(5) evalDet xv yv zv)
      then have type_safe: "(is_IntVal32 xv \<and> is_IntVal32 yv \<and> is_IntVal32 zv) \<or> (is_IntVal64 xv \<and> is_IntVal64 yv \<and> is_IntVal64 zv)"
        by (cases xv; cases yv; cases zv; auto)
      then have and_is_def: "intval_and yv zv \<noteq> UndefVal"
        using is_IntVal32_def is_IntVal64_def by force
      then have up_implies: "(intval_and yv zv) = IntVal32 0 \<or> (intval_and yv zv) = IntVal64 0"
        using p yv zv zero_anded_up_zero_value_intval
        by blast
      have lhs: "v = intval_and (intval_or xv yv) zv"
        using e xv yv zv
        by (smt (verit) BinaryExprE bin_eval.simps(4) bin_eval.simps(5) evalDet)
      then have rhs: "v = intval_and xv zv"
        using intval_eliminate_y_32 intval_eliminate_y_64 up_implies
        by presburger
      from lhs rhs show ?thesis
        using and_or_is_def xv zv by auto
    qed
    done
  done

lemma opt_semantics_2:
  "and (\<up>x) (\<up>z) = 0 \<longrightarrow> BinaryExpr BinAnd (BinaryExpr BinOr x y) z \<ge> BinaryExpr BinAnd y z"
  apply simp apply (rule impI; rule allI; rule allI; rule allI)
  subgoal premises p for m p v apply (rule impI) subgoal premises e
    proof -
      obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
        using e by auto
      obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
        using e by auto
      obtain zv where zv: "[m,p] \<turnstile> z \<mapsto> zv"
        using e by auto
      have and_or_is_def: "intval_and (intval_or xv yv) zv \<noteq> UndefVal"
        using e 
        by (smt (verit, best) BinaryExprE bin_eval.simps(4) bin_eval.simps(5) evalDet xv yv zv)
      then have type_safe: "(is_IntVal32 xv \<and> is_IntVal32 yv \<and> is_IntVal32 zv) \<or> (is_IntVal64 xv \<and> is_IntVal64 yv \<and> is_IntVal64 zv)"
        by (cases xv; cases yv; cases zv; auto)
      then have and_is_def: "intval_and xv zv \<noteq> UndefVal"
        using is_IntVal32_def is_IntVal64_def by force
      then have up_implies: "(intval_and xv zv) = IntVal32 0 \<or> (intval_and xv zv) = IntVal64 0"
        using p xv zv zero_anded_up_zero_value_intval
        by blast
      have lhs: "v = intval_and (intval_or xv yv) zv"
        using e xv yv zv
        by (smt (verit) BinaryExprE bin_eval.simps(4) bin_eval.simps(5) evalDet)
      then have rhs: "v = intval_and yv zv"
        using intval_eliminate_y_32 intval_eliminate_y_64 up_implies
        using intval_or_commute by auto
      from lhs rhs show ?thesis
        using and_or_is_def yv zv by auto
    qed
    done
  done

end

lemma ucast_zero: "(ucast (0::int64)::int32) = 0"
  by simp

lemma ucast_minus_one: "(ucast (-1::int64)::int32) = -1"
  apply transfer by auto

interpretation simple_mask: stamp_mask
  "IRExpr_up :: IRExpr \<Rightarrow> int64"
  "IRExpr_down :: IRExpr \<Rightarrow> int64"
  unfolding IRExpr_up_def IRExpr_down_def
  apply unfold_locales
  by (simp add: ucast_minus_one)+



phase NewAnd
  terminating size
begin

optimization redundant_lhs_y_or: "((x | y) & z) \<longmapsto> x & z
                                when (((and (IRExpr_up y) (IRExpr_up z)) = 0))"
   apply unfold_optimization
  using simple_mask.opt_semantics apply blast
  by simp

optimization redundant_lhs_x_or: "((x | y) & z) \<longmapsto> y & z
                                when (((and (IRExpr_up x) (IRExpr_up z)) = 0))"
   apply unfold_optimization
  using simple_mask.opt_semantics_2 apply blast
  by simp

optimization redundant_rhs_y_or: "(z & (x | y)) \<longmapsto> z & x
                                when (((and (IRExpr_up y) (IRExpr_up z)) = 0))"
   apply unfold_optimization
  using simple_mask.opt_semantics
  apply (meson exp_and_commute order.trans)
  by simp

optimization redundant_rhs_x_or: "(z & (x | y)) \<longmapsto> z & y
                                when (((and (IRExpr_up x) (IRExpr_up z)) = 0))"
   apply unfold_optimization
  using simple_mask.opt_semantics_2
  apply (meson exp_and_commute order_trans)
  by simp

(*
optimization redundant_lhs_add: "((x + y) & z) \<longmapsto> x & z
                               when ((and (IRExpr_up y) (IRExpr_down z)) = 0)"
*)

end

end