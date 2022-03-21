theory NewAnd
  imports
    Common
    Semantics.IRTreeEvalThms
begin

lemma bin_distribute_and_over_or:
  "bin[z & (x | y)] = bin[(z & x) | (z & y)]"
  by (smt (verit, best) bit_and_iff bit_eqI bit_or_iff)

lemma intval_distribute_and_over_or:
  "val[z & (x | y)] = val[(z & x) | (z & y)]"
  apply (cases x; cases y; cases z; auto)
  using bin_distribute_and_over_or by blast+

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
  assumes "bin[y & z] = 0"
  shows "bin[(x | y) & z] = bin[x & z]"
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
end

context stamp_mask
begin

lemma bin_up_and_zero_implies_zero_32:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal32 xv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal32 yv"
  shows "and xv yv = 0"
  using assms
  by (smt (verit) and.commute bit.compl_one bit.compl_zero bit.conj_disj_distrib bit.de_Morgan_disj or_eq_not_not_and stamp_mask.up_spec32 stamp_mask_axioms ucast_0 unsigned_and_eq word_log_esimps(3) word_not_dist(2))

lemma bin_up_and_zero_implies_zero_64:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal64 xv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal64 yv"
  shows "and xv yv = 0"
  using assms
  by (smt (verit) and_eq_not_not_or bit.conj_disj_distrib bit.conj_disj_distrib2 stamp_mask.up_spec64 stamp_mask_axioms word_ao_absorbs(2) word_ao_absorbs(8) word_log_esimps(3) word_not_dist(2))

lemma intval_up_and_zero_implies_zero:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> xv"
  assumes "[m, p] \<turnstile> y \<mapsto> yv"
  assumes "val[xv & yv] \<noteq> UndefVal"
  shows "val[xv & yv] = IntVal32 0 \<or> val[xv & yv] = IntVal64 0"
  using assms apply (cases xv; cases yv; auto)
  using bin_up_and_zero_implies_zero_32 apply presburger
  using bin_up_and_zero_implies_zero_64 by blast

lemma exp_eliminate_y:
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
    have lhs: "v = val[(xv | yv) & zv]"
      using xv yv zv
      by (smt (verit, best) BinaryExprE bin_eval.simps(4) bin_eval.simps(5) e evalDet)
    then have "v = val[(xv & zv) | (yv & zv)]"
      by (simp add: intval_and_commute intval_distribute_and_over_or)
    also have "val[yv & zv] = IntVal32 0 \<or> val[yv & zv] = IntVal64 0"
      using intval_up_and_zero_implies_zero
      by (metis calculation e evaltree_not_undef intval_or.simps(10) p yv zv)
    ultimately have rhs: "v = val[xv & zv]"
      using intval_eliminate_y_32 intval_eliminate_y_64 lhs by presburger
    from lhs rhs show ?thesis
      by (metis BinaryExpr BinaryExprE bin_eval.simps(4) e xv zv)
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
  using simple_mask.exp_eliminate_y apply blast
  by simp

optimization redundant_lhs_x_or: "((x | y) & z) \<longmapsto> y & z
                                when (((and (IRExpr_up x) (IRExpr_up z)) = 0))"
   apply unfold_optimization
  using simple_mask.exp_eliminate_y
  apply (meson exp_or_commute mono_binary order_refl order_trans)
  by simp

optimization redundant_rhs_y_or: "(z & (x | y)) \<longmapsto> z & x
                                when (((and (IRExpr_up y) (IRExpr_up z)) = 0))"
   apply unfold_optimization
  using simple_mask.exp_eliminate_y
  apply (meson exp_and_commute order.trans)
  by simp

optimization redundant_rhs_x_or: "(z & (x | y)) \<longmapsto> z & y
                                when (((and (IRExpr_up x) (IRExpr_up z)) = 0))"
   apply unfold_optimization
  using simple_mask.exp_eliminate_y 
  apply (meson dual_order.trans exp_and_commute exp_or_commute mono_binary order_refl)
  by simp

(*
optimization redundant_lhs_add: "((x + y) & z) \<longmapsto> x & z
                               when ((and (IRExpr_up y) (IRExpr_down z)) = 0)"
*)

end

end