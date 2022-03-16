theory NewAnd
  imports
    Common
    "HOL-Library.FSet"
    Semantics.IRTreeEvalThms
begin

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

lemma distribute_and:
  "and z (or x y) = or (and z x) (and z y)"
  by (smt (verit, best) bit_and_iff bit_eqI bit_or_iff)

lemma distribute_and_intval:
  assumes "intval_and z (intval_or x y) \<noteq> UndefVal"
  assumes "intval_or (intval_and z x) (intval_and z y) \<noteq> UndefVal"
  shows "intval_and z (intval_or x y) = intval_or (intval_and z x) (intval_and z y)" (is "?lhs = ?rhs")
  using assms apply (cases x; cases y; cases z; auto)
  by (simp add: distribute_and)+

lemma eliminate_y:
  assumes "and y z = 0"
  shows "and (or x y) z = and x z"
  using assms distribute_and
  by (metis and.commute or.right_neutral)

lemma intval_eliminate_y_64:
  assumes "intval_and (intval_or x y) z \<noteq> UndefVal"
  assumes "intval_and x z \<noteq> UndefVal"
  assumes "intval_and y z = IntVal64 0"
  shows "intval_and (intval_or x y) z = intval_and x z"
  using assms eliminate_y by (cases x; cases y; cases z; auto)

lemma intval_eliminate_y_32:
  assumes "intval_and (intval_or x y) z \<noteq> UndefVal"
  assumes "intval_and x z \<noteq> UndefVal"
  assumes "intval_and y z = IntVal32 0"
  shows "intval_and (intval_or x y) z = intval_and x z"
  using assms eliminate_y by (cases x; cases y; cases z; auto)


lemma opt_semantics:
  "and (\<up>y) (\<up>z) = 0 \<longrightarrow>
    BinaryExpr BinAnd (BinaryExpr BinOr x y) z \<ge> BinaryExpr BinAnd x z"
  proof -
    show ?thesis apply simp apply (rule impI; rule allI; rule allI; rule allI)
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
          using e
          by (smt (verit) BinaryExprE \<open>[m,p] \<turnstile> x \<mapsto> xv\<close> \<open>[m,p] \<turnstile> y \<mapsto> yv\<close> \<open>[m,p] \<turnstile> z \<mapsto> zv\<close> bin_eval.simps(4) bin_eval.simps(5) evalDet)
        then have rhs: "v = intval_and xv zv"
          using intval_eliminate_y_32 intval_eliminate_y_64 up_implies
          by (metis (no_types, opaque_lifting) Value.distinct(1) Value.distinct(3) and_or_is_def intval_and.simps(1) intval_and.simps(2) is_IntVal32_def is_IntVal64_def type_safe)
        from lhs rhs show ?thesis
          using and_or_is_def xv zv by auto
      qed
      done
    done
  qed
 
lemma opt_termination:
  "and (\<up>y) (\<up>z) = 0 \<longrightarrow>
    Common.size (BinaryExpr BinAnd x z) < Common.size (BinaryExpr BinAnd (BinaryExpr BinOr x y) z)"
  unfolding size.simps by simp

end

lemma ucast_zero: "(ucast (0::int64)::int32) = 0"
  by simp

lemma ucast_minus_one: "(ucast (-1::int64)::int32) = -1"
  apply transfer by auto

interpretation dummy: stamp_mask
  "IRExpr_up :: IRExpr \<Rightarrow> int64"
  "IRExpr_down :: IRExpr \<Rightarrow> int64"
  unfolding IRExpr_up_def IRExpr_down_def
  apply unfold_locales
  by (simp add: ucast_minus_one)+

phase NewAnd
  terminating size
begin

optimization opt: "((x | y) & z) \<longmapsto> x & z
                   when (((and (IRExpr_up y) (IRExpr_up z)) = 0))"
   apply unfold_optimization
  using dummy.opt_semantics apply blast
  by simp

end

end