theory NewAnd
  imports
    Common
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
  using intval_or.simps(1) unfolding new_int_bin.simps new_int.simps apply auto
  by (metis bin_eval.simps(4) bin_eval.simps(5) intval_or.simps(2) intval_or.simps(5))


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

lemma intval_eliminate_y:
  assumes "val[y & z] = IntVal b 0"
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
  assumes "\<exists>b v . x = new_int b v" (* TODO: required? *)
  assumes "val[x & (x | y)] \<noteq> UndefVal"
  shows "val[x & (x | y)] = val[x]"
  using assms apply (cases x; cases y; auto)
  by (metis (mono_tags, lifting) intval_and.simps(5))

lemma intval_or_absorb_and:
  assumes "\<exists>b v . x = new_int b v" (* TODO: required? *)
  assumes "val[x | (x & y)] \<noteq> UndefVal"
  shows "val[x | (x & y)] = val[x]"
  using assms apply (cases x; cases y; auto)
  by (metis (mono_tags, lifting) intval_or.simps(5))

lemma exp_and_absorb_or:
  "exp[x & (x | y)] \<ge> exp[x]"
  apply simp using intval_and_absorb_or sorry (*
  by (smt (verit, best) BinaryExprE bin_eval.simps(4) bin_eval.simps(5) evalDet)*)

lemma exp_or_absorb_and:
  "exp[x | (x & y)] \<ge> exp[x]"
  apply simp using intval_or_absorb_and sorry (*
  by (smt (verit) BinaryExprE bin_eval.simps(4) bin_eval.simps(5) evalDet)*)

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
  assumes up_spec: "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> (and v (not ((ucast (\<up>e))))) = 0"
      and down_spec: "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> (and (not v) (ucast (\<down>e))) = 0"
begin

(*
lemma bitsets:
  "\<down>x \<subseteq> x \<and> x \<subseteq> \<up>x"
*)

lemma may_implies_either:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> bit (\<up>e) n \<Longrightarrow> bit v n = False \<or> bit v n = True"
  by simp

lemma not_may_implies_false:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> \<not>(bit (\<up>e) n) \<Longrightarrow> bit v n = False"
  using up_spec
  using bit_and_iff bit_eq_iff bit_not_iff bit_unsigned_iff down_spec
  by (smt (verit, best) bit.double_compl)

lemma must_implies_true:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> bit (\<down>e) n \<Longrightarrow> bit v n = True"
  using down_spec
  by (metis bit.compl_one bit_and_iff bit_minus_1_iff bit_not_iff impossible_bit ucast_id)

lemma not_must_implies_either:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> \<not>(bit (\<down>e) n) \<Longrightarrow> bit v n = False \<or> bit v n = True"
  by simp

lemma must_implies_may:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> n < 32 \<Longrightarrow> bit (\<down>e) n \<Longrightarrow> bit (\<up>e) n"
  by (meson must_implies_true not_may_implies_false)
end

context stamp_mask
begin

lemma bin_up_and_zero_implies_zero:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  shows "and xv yv = 0"
  using assms
  by (smt (z3) and.commute and.right_neutral and_zero_eq bit.compl_zero bit.conj_cancel_right bit.conj_disj_distribs(1) ucast_id up_spec word_bw_assocs(1) word_not_dist(2))

lemma intval_up_and_zero_implies_zero:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> xv"
  assumes "[m, p] \<turnstile> y \<mapsto> yv"
  assumes "val[xv & yv] \<noteq> UndefVal"
  shows "\<exists> b . val[xv & yv] = new_int b 0"
  using assms apply (cases xv; cases yv; auto)
  using bin_up_and_zero_implies_zero
  apply (smt (verit, best) take_bit_and take_bit_of_0)
  by presburger

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
    also have "\<exists>b. val[yv & zv] = new_int b 0"
      using intval_up_and_zero_implies_zero
      by (metis calculation e intval_or.simps(5) new_int.simps p take_bit_of_0 unfold_binary yv zv)
    ultimately have rhs: "v = val[xv & zv]"
      using intval_eliminate_y lhs by force
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
  using simple_mask.exp_eliminate_y by blast

optimization redundant_lhs_x_or: "((x | y) & z) \<longmapsto> y & z
                                when (((and (IRExpr_up x) (IRExpr_up z)) = 0))"
  using simple_mask.exp_eliminate_y
  by (meson exp_or_commute mono_binary order_refl order_trans)

optimization redundant_rhs_y_or: "(z & (x | y)) \<longmapsto> z & x
                                when (((and (IRExpr_up y) (IRExpr_up z)) = 0))"
  using simple_mask.exp_eliminate_y
  by (meson exp_and_commute order.trans)

optimization redundant_rhs_x_or: "(z & (x | y)) \<longmapsto> z & y
                                when (((and (IRExpr_up x) (IRExpr_up z)) = 0))"
  using simple_mask.exp_eliminate_y
  by (meson dual_order.trans exp_and_commute exp_or_commute mono_binary order_refl)

(*
optimization redundant_lhs_add: "((x + y) & z) \<longmapsto> x & z
                               when ((and (IRExpr_up y) (IRExpr_down z)) = 0)"
*)

end

end