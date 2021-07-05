theory
  CanonicalizationProofs
imports
  Canonicalization
begin

lemma intstamp:
  assumes "wf_stamps g"
  assumes "[g, m, p] \<turnstile> kind g tb \<mapsto> IntVal32 tbval"
  shows "stamp g tb = (IntegerStamp x l h) \<and> sint tbval \<ge> l \<and> sint tbval \<le> h"
  using assms unfolding wf_stamps.simps
proof -
  obtain x l h where stampdef: "stamp g tb = IntegerStamp x l h"
    using assms
    by (metis Value.distinct(1) eval_in_ids valid_value.elims(2) wf_stamps.elims(2))
  then have "sint tbval \<ge> l \<and> sint tbval \<le> h"
    using valid_value.simps assms
    by (metis eval_in_ids wf_stamps.elims(2))
  then show ?thesis
    using stampdef sorry
qed

lemma
  assumes "wf_stamps g"
  assumes "stpi_upper (stamp g tb) \<le> stpi_lower (stamp g fb)"
  assumes "[g, m, p] \<turnstile> kind g tb \<mapsto> IntVal32 tbval"
  assumes "[g, m, p] \<turnstile> kind g fb \<mapsto> IntVal32 fbval"
  shows "tbval \<le> fbval"
  using assms intstamp
  by (metis Stamp.sel(1) one_neq_zero)


experiment begin
lemma CanonicalizeConditionalProof:
  assumes "CanonicalizeConditional g before after"
  assumes "wf_graph g \<and> wf_stamps g"
  assumes "[g, m, p] \<turnstile> before \<mapsto> res"
  assumes "[g, m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms(1) assms 
proof (induct rule: CanonicalizeConditional.induct)
  case (negate_condition g cond flip tb fb)
  obtain condv where condv: "[g, m, p] \<turnstile> kind g cond \<mapsto> IntVal32 condv"
    using negate_condition.prems(3) by blast
  then obtain flipv where flipv: "[g, m, p] \<turnstile> kind g flip \<mapsto> IntVal32 flipv"
    by (metis LogicNegationNodeE negate_condition.hyps)
  have invert: "(val_to_bool (IntVal32 condv)) \<longleftrightarrow> \<not>(val_to_bool (IntVal32 flipv))" 
    by (metis bool_to_val.simps(1) bool_to_val.simps(2) condv eval.LogicNegationNode evalDet flipv negate_condition.hyps val_to_bool.simps(1) zero_neq_one)
  obtain tbval where tbval: "[g, m, p] \<turnstile> kind g tb \<mapsto> IntVal32 tbval"
    using negate_condition.prems(3) by blast
  obtain fbval where fbval: "[g, m, p] \<turnstile> kind g fb \<mapsto> IntVal32 fbval"
    using negate_condition.prems(3) by blast
  show ?case proof (cases "condv = 0")
    case True
    have "flipv \<noteq> 0"
      using eval.LogicNegationNode condv flipv
      using True evalDet negate_condition.hyps by fastforce
    then have "res' = IntVal32 (if (val_to_bool (IntVal32 flipv)) then fbval else tbval)"
      using eval.ConditionalNode tbval fbval negate_condition(5)
      evalDet
      by (meson flipv)
    then have "IntVal32 fbval = res'"
      using True invert by auto
    have "res = IntVal32 (if (val_to_bool (IntVal32 condv)) then tbval else fbval)"
      using eval.ConditionalNode tbval fbval condv negate_condition(4)
      by (meson evalDet)
    then have "IntVal32 fbval = res"
      using eval.ConditionalNode tbval fbval True condv
      negate_condition(4) evalDet ConditionalNodeE
      by fastforce
    then show ?thesis
      using \<open>IntVal32 fbval = res'\<close> by blast
  next
    case False
    have "\<exists>x. bool_to_val x = IntVal32 condv"
      using eval.LogicNegationNode flipv negate_condition(1)
      bool_to_val.simps
      by (metis LogicNegationNodeE condv)
    have "condv \<in> {0, 1}"
      using eval.LogicNegationNode flipv negate_condition(1)
      bool_to_val.simps
      by (metis (mono_tags, lifting) Value.inject(1) \<open>\<exists>x. bool_to_val x = IntVal32 condv\<close> insertCI)
    have "val_to_bool (IntVal32 condv)"
      using eval.LogicNegationNode condv flipv
      using False evalDet negate_condition.hyps invert
      by (metis Value.sel(1) bool_to_val.elims)
    then have "res' = IntVal32 (if (val_to_bool (IntVal32 flipv)) then fbval else tbval)"
      using eval.ConditionalNode tbval fbval negate_condition(5)
      evalDet
      by (meson flipv)
    then have "IntVal32 tbval = res'"
      using \<open>val_to_bool (IntVal32 condv)\<close> invert by presburger
    have "res = IntVal32 (if (val_to_bool (IntVal32 condv)) then tbval else fbval)"
      using eval.ConditionalNode tbval fbval condv negate_condition(4)
      by (meson evalDet)
    then have "IntVal32 tbval = res"
      using eval.ConditionalNode tbval fbval False condv
      negate_condition(4) evalDet ConditionalNodeE
      using \<open>val_to_bool (IntVal32 condv)\<close> by presburger
    then show ?thesis
      by (simp add: \<open>IntVal32 tbval = res'\<close>)
  qed
next
  case (const_true g cond val tb fb)
  then show ?case
    using eval.RefNode evalDet by force
next
  case (const_false g cond val tb fb)
  then show ?case
    using eval.RefNode evalDet eval.ConditionalNode
    by auto
next
  case (eq_branches tb fb g cond)
  then show ?case
    using eval.RefNode evalDet by force
next
  case (cond_eq g cond tb fb)
  then obtain condv where condv: "[g, m, p] \<turnstile> kind g cond \<mapsto> IntVal32 condv"
    by blast
  obtain tbval where tbval: "[g, m, p] \<turnstile> kind g tb \<mapsto> IntVal32 tbval"
    using cond_eq.prems(3) by blast
  obtain fbval where fbval: "[g, m, p] \<turnstile> kind g fb \<mapsto> IntVal32 fbval"
    using cond_eq.prems(3) by blast
  from cond_eq show ?case proof (cases "condv \<noteq> 0")
    case True
    have "tbval = fbval" using IntegerEqualsNodeE condv cond_eq(1)
      tbval fbval True
      by (metis (full_types) Value.inject(1) bool_to_val.simps(2) evalDet)
    have "res' = IntVal32 tbval"
      using RefNode \<open>tbval = fbval\<close> cond_eq.prems(4) evalDet fbval by presburger
    have "res' = IntVal32 fbval"
      by (simp add: \<open>res' = IntVal32 tbval\<close> \<open>tbval = fbval\<close>)
    have "res = IntVal32 (if val_to_bool (IntVal32 condv) then tbval else fbval)"
      by (meson cond_eq.prems(3) condv eval.ConditionalNode evalDet fbval tbval)
    then have "res = IntVal32 tbval \<or> res = IntVal32 fbval"
      using eval.ConditionalNode evalDet tbval fbval condv cond_eq.prems(3)
      by (simp add: \<open>[g, m, p] \<turnstile> ConditionalNode cond tb fb \<mapsto> res\<close> \<open>res = IntVal32 (if val_to_bool (IntVal32 condv) then tbval else fbval)\<close> condv eval.ConditionalNode evalDet fbval tbval)
    then show ?thesis using cond_eq
      evalDet fbval tbval eval.ConditionalNode eval.IntegerEqualsNode
      using \<open>res' = IntVal32 fbval\<close> \<open>res' = IntVal32 tbval\<close> by fastforce
  next
    case False
    have "\<not>(val_to_bool (IntVal32 condv))"
      using False by auto
    have "(val_to_bool (IntVal32 condv)) = (tbval = fbval)"
    proof -
      have "bool_to_val True \<noteq> IntVal32 condv"
        using \<open>\<not> val_to_bool (IntVal32 condv)\<close> by fastforce
      then have "\<not> [g, m, p] \<turnstile> kind g tb \<mapsto> IntVal32 fbval"
        by (metis (full_types) IntegerEqualsNode cond_eq.hyps condv evalDet fbval)
      then show ?thesis
        using \<open>\<not> val_to_bool (IntVal32 condv)\<close> tbval by force
    qed
    then have "tbval \<noteq> fbval" 
      using eval.IntegerEqualsNode condv cond_eq(1)
      tbval fbval False
      using \<open>\<not> val_to_bool (IntVal32 condv)\<close> by linarith
    have "res' = IntVal32 fbval"
      by (meson RefNode cond_eq.prems(4) evalDet fbval)
    have "res = IntVal32 (if val_to_bool (IntVal32 condv) then tbval else fbval)"
      by (meson cond_eq.prems(3) condv eval.ConditionalNode evalDet fbval tbval)
    then have "res = IntVal32 fbval"
      using eval.ConditionalNode evalDet tbval fbval condv cond_eq.prems(3)
      using \<open>\<not> val_to_bool (IntVal32 condv)\<close> by presburger
    then show ?thesis using cond_eq
        evalDet fbval tbval eval.ConditionalNode eval.IntegerEqualsNode
      using \<open>res' = IntVal32 fbval\<close> by force
  qed
next
  case (condition_bounds_x g cond tb fb)
  obtain tbval where tbval: "[g, m, p] \<turnstile> kind g tb \<mapsto> IntVal32 tbval"
    using condition_bounds_x.prems(3) by blast
  obtain fbval where fbval: "[g, m, p] \<turnstile> kind g fb \<mapsto> IntVal32 fbval"
    using condition_bounds_x.prems(3) by blast
  have "tbval \<le> fbval"
    using condition_bounds_x.prems(2) tbval fbval condition_bounds_x.hyps(2) int_valid_range
    unfolding wf_stamps.simps using valid_value.simps
    sorry
  then have "res = IntVal32 tbval"
    using ConditionalNodeE tbval fbval
    eval.IntegerLessThanNode
    sorry
  then show ?case
    using condition_bounds_x.prems(3) eval.RefNode evalDet tbval
    using ConditionalNodeE Value.sel(1) condition_bounds_x.prems(4) by blast
next
  case (condition_bounds_y g cond fb tb)
  obtain tbval where tbval: "[g, m, p] \<turnstile> kind g tb \<mapsto> IntVal32 tbval"
    using condition_bounds_y.prems(3) by blast
  obtain fbval where fbval: "[g, m, p] \<turnstile> kind g fb \<mapsto> IntVal32 fbval"
    using condition_bounds_y.prems(3) by blast
  have "tbval \<ge> fbval"
    using condition_bounds_y.prems(2) tbval fbval condition_bounds_y.hyps(2) int_valid_range
    unfolding wf_stamps.simps 
    sorry
  then have "res = IntVal32 tbval"
    using ConditionalNodeE tbval fbval
    sorry
  then show ?case
    using condition_bounds_y.prems(3) eval.RefNode evalDet tbval
    using ConditionalNodeE Value.sel(1) condition_bounds_y.prems(4) by blast
qed
end

lemma add_zero_32:
  shows "(IntVal32 0) + (IntVal32 y) = (IntVal32 y)"
  using plus_Value_def by auto

lemma add_zero_64:
  shows "(IntVal64 0) + (IntVal64 y) = (IntVal64 y)"
  using plus_Value_def by auto

lemma
  fixes xval yval :: "32 word"
  shows "(0 - xval) + yval = yval - xval"
  by simp

lemma add_int32_typesafe:
  fixes x y :: Value
  shows "(\<exists>res. x + y = IntVal32 res) = (\<exists>xval yval. x = IntVal32 xval \<and> y = IntVal32 yval)"
  unfolding plus_Value_def
  by (induction rule: intval_add.induct; simp)

lemma sub_int32_typesafe:
  fixes x y :: Value
  shows "(\<exists>res. x - y = IntVal32 res) = (\<exists>xval yval. x = IntVal32 xval \<and> y = IntVal32 yval)"
  unfolding minus_Value_def
  by (induction rule: intval_add.induct; simp)

lemma add_int64_typesafe:
  fixes x y :: Value
  shows "(\<exists>res. x + y = IntVal64 res) = (\<exists>xval yval. x = IntVal64 xval \<and> y = IntVal64 yval)"
  unfolding plus_Value_def
  by (induction rule: intval_add.induct; simp)

lemma sub_int64_typesafe:
  fixes x y :: Value
  shows "(\<exists>res. x - y = IntVal64 res) = (\<exists>xval yval. x = IntVal64 xval \<and> y = IntVal64 yval)"
  unfolding minus_Value_def
  by (induction rule: intval_add.induct; simp)

lemma CanonicalizeAddProof:
  assumes "CanonicalizeAdd g before after"
  assumes "wf_graph g \<and> wf_stamps g"
  assumes "[g, m, p] \<turnstile> before \<mapsto> IntVal32 res"
  assumes "[g, m, p] \<turnstile> after \<mapsto> IntVal32 res'"
  shows "res = res'"
proof -
  obtain x y where addkind: "before = AddNode x y"
    using CanonicalizeAdd.simps assms by auto
  from addkind
  obtain xval where xval: "[g, m, p] \<turnstile> kind g x \<mapsto> xval"
    using assms(3) by blast
  from addkind
  obtain yval where yval: "[g, m, p] \<turnstile> kind g y \<mapsto> yval"
    using assms(3) by blast
  have res: "IntVal32 res = intval_add xval yval"
    using assms(3) eval.AddNode
    using addkind evalDet xval yval plus_Value_def by metis
  show ?thesis
    using assms addkind xval yval res
  proof (induct rule: "CanonicalizeAdd.induct")
case (add_both_const x c_1 y c_2 val)
  then show ?case using eval.ConstantNode
    by (metis ConstantNodeE IRNode.inject(2) Value.inject(1))
next
  case (add_xzero x c_1 y)
  have xeval: "[g, m, p] \<turnstile> kind g x \<mapsto> (IntVal32 0)"
    by (simp add: ConstantNode add_xzero.hyps(1) add_xzero.hyps(3))
  have yeval: "[g, m, p] \<turnstile> kind g y \<mapsto> yval"
    using add_xzero.prems(4) yval by blast
  have y: "IntVal32 res' = yval"
    by (meson RefNodeE add_xzero.prems(3) evalDet yeval)
  then have res_val: "IntVal32 res = intval_add (IntVal32 0) yval"
    using eval.AddNode eval.ConstantNode add_xzero(1,3,5)
    using evalDet by (metis IRNode.inject(2) add_xzero.prems(4) res xval) 
  then show ?case
    using eval.RefNode yval res_val y plus_Value_def
    by fastforce
next
  case (add_yzero x y c_2)
  have yeval: "[g, m, p] \<turnstile> kind g y \<mapsto> (IntVal32 0)"
    by (simp add: ConstantNode add_yzero.hyps(2) add_yzero.hyps(3))
  have xeval: "[g, m, p] \<turnstile> kind g x \<mapsto> xval"
    using add_yzero.prems(4) xval by fastforce
  then have y: "IntVal32 res' = xval"
    by (meson RefNodeE add_yzero.prems(3) evalDet xeval)
  then have "IntVal32 res = intval_add xval (IntVal32 0)"
    using eval.AddNode eval.ConstantNode add_yzero(2,3,5) 
    using evalDet xeval plus_Value_def by metis
  then have res: "IntVal32 res = intval_add (IntVal32 0) xval"
    by (simp add: intval_add_sym)
  then show ?case using eval.RefNode xval plus_Value_def
    using y by force
next
  case (add_xsub x a y)
  obtain yv where "yval = IntVal32 yv"
    using eval.AddNode add_xsub(3,5,6,7) add_int32_typesafe evalDet
    by metis
  obtain xv where "xval = IntVal32 xv"
    using eval.AddNode add_xsub(3,5,6,7) add_int32_typesafe evalDet
    by metis
  obtain aval where aval: "aval = IntVal32 res'"
    by blast
  then have "(aval - yval) + yval = aval"
    using add_int32_typesafe sub_int32_typesafe
    by (simp add: \<open>yval = IntVal32 yv\<close> minus_Value_def plus_Value_def)
  then show ?case using eval.AddNode eval.SubNode eval.RefNode
    by (metis (no_types, lifting) IRNode.inject(2) SubNodeE Value.sel(1) add_xsub.hyps add_xsub.prems(3) add_xsub.prems(4) addkind assms(3) aval evalDet xval yval)
next
  case (add_ysub y a x)
  obtain yv where "yval = IntVal32 yv"
    using eval.AddNode add_ysub(3,5,6,7) add_int32_typesafe evalDet
    by metis
  obtain xv where "xval = IntVal32 xv"
    using eval.AddNode add_ysub(3,5,6,7) add_int32_typesafe evalDet
    by metis
  obtain aval where aval: "aval = IntVal32 res'"
    by blast
  then have "xval + (aval - xval) = aval"
    using add_int32_typesafe sub_int32_typesafe
    by (simp add: \<open>xval = IntVal32 xv\<close> minus_Value_def plus_Value_def)
  then show ?case using eval.AddNode eval.SubNode eval.RefNode
    by (metis IRNode.inject(2) RefNodeE Value.sel(1) add_ysub.hyps add_ysub.prems(3) add_ysub.prems(4) add_ysub.prems(5) add_ysub.prems(6) aval evalDet plus_Value_def res)
next
  case (add_xnegate nx x y)
  obtain yv where yv: "yval = IntVal32 yv"
    using eval.AddNode add_xnegate(3,5,6,7) add_int32_typesafe evalDet
    by metis
  obtain xv where xv: "xval = IntVal32 xv"
    using eval.AddNode add_xnegate(3,5,6,7) add_int32_typesafe evalDet
    by metis
  obtain oxval where oxval: "[g, m, p] \<turnstile> kind g x \<mapsto> oxval"
    using add_xnegate.prems(3) by blast
  have negdef: "xval = (IntVal32 0) - oxval"
    by (metis IRNode.inject(2) add_xnegate.hyps add_xnegate.prems(4) eval.NegateNode evalDet oxval xval)
  then have "\<exists>res. IntVal32 res = IntVal32 0 - oxval"
    using xv by fastforce
  then have "\<exists>oxv. oxval = IntVal32 oxv"
    using sub_int32_typesafe negdef
    by metis
  then obtain oxv where oxv: "oxval = IntVal32 oxv"
    using sub_int32_typesafe xv
    by blast
  obtain negx where negx: "negx = (IntVal32 0) - oxval"
    by blast
  then have "[g, m, p] \<turnstile> NegateNode x \<mapsto> negx"
    using eval.NegateNode
    using oxval by blast
  have "((IntVal32 0) - oxval) + yval = yval - oxval"
    using add_int32_typesafe sub_int32_typesafe yv oxv
    using plus_Value_def minus_Value_def by simp
  then show ?case using eval.NegateNode eval.AddNode eval.SubNode
    by (metis IRNode.inject(2) Value.sel(1) add_xnegate.prems(3) add_xnegate.prems(4) evalDet negdef oxval plus_Value_def res yval)
next
  case (add_ynegate ny y x)
  obtain yv where yv: "yval = IntVal32 yv"
    using eval.AddNode add_ynegate(3,5,6,7) add_int32_typesafe evalDet
    by metis
  obtain xv where xv: "xval = IntVal32 xv"
    using eval.AddNode add_ynegate(3,5,6,7) add_int32_typesafe evalDet
    by metis
  obtain oyval where oyval: "[g, m, p] \<turnstile> kind g y \<mapsto> oyval"
    using add_ynegate.prems(3) by blast
  have negdef: "yval = (IntVal32 0) - oyval"
    using eval.NegateNode
    by (metis IRNode.inject(2) add_ynegate.hyps add_ynegate.prems(4) add_ynegate.prems(6) evalDet oyval)
  then have "\<exists>res. IntVal32 res = IntVal32 0 - oyval"
    using yv by fastforce
  then have "\<exists>oyv. oyval = IntVal32 oyv"
    using sub_int32_typesafe negdef
    by metis
  then obtain oyv where oyv: "oyval = IntVal32 oyv"
    using sub_int32_typesafe yv
    by blast
  obtain negy where negx: "negy = (IntVal32 0) - oyval"
    by blast
  then have "[g, m, p] \<turnstile> NegateNode y \<mapsto> negy"
    using eval.NegateNode
    using oyval by blast
  have "(xval + ((IntVal32 0) - oyval)) = xval - oyval"
    using add_int32_typesafe sub_int32_typesafe yv oyv
    using plus_Value_def minus_Value_def
    by (metis (mono_tags, hide_lams) add.group_left_neutral diff_add_eq intval_add.simps(1) intval_add_sym intval_sub.simps(1) negdef res)
  then show ?case using eval.NegateNode eval.AddNode eval.SubNode
    by (metis IRNode.inject(2) Value.sel(1) add_ynegate.prems(3) add_ynegate.prems(4) add_ynegate.prems(5) evalDet negdef oyval plus_Value_def res)
qed
qed

lemma add_det:
  fixes r x y :: Value
  shows "r = x + y \<Longrightarrow> r' = x + y \<Longrightarrow> r = r'"
  by simp

lemma sub_det:
  fixes r x y :: Value
  shows "r = x - y \<Longrightarrow> r' = x - y \<Longrightarrow> r = r'"
  by simp

lemma add_sub:
  fixes x y :: Value
  assumes "x = IntVal32 xval"
  and "y = IntVal32 yval"
  shows "(x + y) - y = x"
  unfolding plus_Value_def minus_Value_def using assms by simp


lemma CanonicalizeSubProof:
  assumes "CanonicalizeSub g before after"
  assumes "wf_stamps g"
  assumes "[g, m, p] \<turnstile> before \<mapsto> IntVal32 res"
  assumes "[g, m, p] \<turnstile> after \<mapsto> IntVal32 res'"
  shows "res = res'"
proof -
  obtain x y where subkind: "before = SubNode x y"
    using CanonicalizeSub.simps assms by auto
  from subkind
  obtain xval where xval: "[g, m, p] \<turnstile> kind g x \<mapsto> xval"
    using assms(3) by blast
  from subkind
  obtain yval where yval: "[g, m, p] \<turnstile> kind g y \<mapsto> yval"
    using assms(3) by blast
  have res: "IntVal32 res = intval_sub xval yval"
    using assms(3) eval.SubNode
    using subkind evalDet xval yval minus_Value_def by metis
  show ?thesis
    using assms subkind xval yval res
proof (induct rule: "CanonicalizeSub.induct")
  case (sub_same x y b l h)
  have "xval = yval" 
    using evalDet sub_same(1) xval yval sub_same(6)
    by (metis IRNode.inject(39))
  then have "xval - yval = IntVal32 0"
    using sub_int32_typesafe res unfolding minus_Value_def
    by (cases xval; cases yval; auto)
  then have res: "res = 0"
    using sub_same(9) unfolding minus_Value_def by simp
  have "res' = 0"
    using sub_same(5) eval.ConstantNode by auto
  with res show ?case by simp
next
  case (sub_both_const x c_1 y c_2 val)
  have res: "IntVal32 res = xval - yval"
    using sub_both_const(5) xval yval sub_both_const(7) eval.SubNode
    by (simp add: eval.SubNode sub_both_const.prems(2) sub_both_const.prems(4) xval yval minus_Value_def res)
  have "IntVal32 res' = xval - yval"
    using sub_both_const(6) sub_both_const(1,2,3) xval yval sub_both_const(7) minus_Value_def
    by (metis ConstantNodeE IRNode.inject(39))
  with res show ?case using sub_det by blast
next
  case (sub_left_add1 left a b)
  have ytype: "\<exists>v . yval = IntVal32 v"
    using yval sub_int32_typesafe res unfolding minus_Value_def by metis
  obtain aval where aval: "[g, m, p] \<turnstile> kind g a \<mapsto> aval"
    using sub_left_add1.prems(3) by blast
  then have atype: "\<exists>v . aval = IntVal32 v"
    using sub_int32_typesafe sub_left_add1
    by (meson RefNode evalDet)
  have "[g, m, p] \<turnstile> kind g b \<mapsto> yval"
    using evalDet sub_left_add1(5) yval by simp
  have "xval = aval + yval"
    using sub_left_add1(1,5,6,7) eval.AddNode aval
    by (metis IRNode.inject(39) evalDet)
  then have "IntVal32 res = (aval + yval) - yval"
    using sub_left_add1(8) unfolding minus_Value_def plus_Value_def by simp
  then have res: "IntVal32 res = aval"
    using add_sub atype ytype by metis
  have "IntVal32 res' = aval"
    using sub_left_add1(4) eval.RefNode aval evalDet by simp
  with res show ?case by auto
next
  case (sub_left_add2 left a b)
    have ytype: "\<exists>v . yval = IntVal32 v"
    using yval sub_int32_typesafe res unfolding minus_Value_def by metis
  obtain bval where bval: "[g, m, p] \<turnstile> kind g b \<mapsto> bval"
    using sub_left_add2.prems(3) by blast
  then have atype: "\<exists>v . bval = IntVal32 v"
    using sub_left_add2(4) eval.RefNode
    by (meson evalDet)
  have "[g, m, p] \<turnstile> kind g a \<mapsto> yval"
    using evalDet sub_left_add2(5) yval by simp
  then have "xval = yval + bval"
    using sub_left_add2(1,5,6,7) eval.AddNode bval
    using IRNode.inject(39) evalDet by simp
  then have "IntVal32 res = (yval + bval) - yval"
    using sub_left_add2(8) unfolding minus_Value_def plus_Value_def by simp
  then have res: "IntVal32 res = bval"
    using atype ytype unfolding plus_Value_def minus_Value_def by auto
  have "IntVal32 res' = bval"
    using sub_left_add2(4) eval.RefNode bval evalDet by simp
  with res show ?case by auto
next
  case (sub_left_sub left a b)
  obtain bval where bval: "[g, m, p] \<turnstile> kind g b \<mapsto> bval"
    using sub_left_sub(4) eval.NegateNode by auto
  then have resdef: "IntVal32 res = (yval - bval) - yval"
    using sub_left_sub(3,1) bval yval sub_left_sub(5) eval.SubNode
    using evalDet by auto
  have ytype: "\<exists> v. yval = IntVal32 v" using resdef sub_int32_typesafe by metis
  have btype: "\<exists> v. bval = IntVal32 v" using resdef sub_int32_typesafe by metis
  have res: "IntVal32 res = (IntVal32 0) - bval"
    using resdef unfolding minus_Value_def 
    using ytype btype by auto
  have "IntVal32 res' = (IntVal32 0) - bval"
    using sub_left_sub(4) eval.NegateNode bval evalDet by simp
  with res show ?case
    by (metis Value.inject(1))
next
  case (sub_right_add1 right a b)
  obtain bval where bval: "[g, m, p] \<turnstile> kind g b \<mapsto> bval"
    using sub_right_add1(4) eval.NegateNode by auto
  then have resdef: "IntVal32 res = xval - (xval + bval)"
    using sub_right_add1(3,1) bval xval sub_right_add1(5) eval.SubNode eval.AddNode
    using evalDet by simp
  have xtype: "\<exists> v. xval = IntVal32 v" using resdef sub_int32_typesafe by metis
  have btype: "\<exists> v. bval = IntVal32 v" using resdef sub_int32_typesafe add_int32_typesafe by metis
  have res: "IntVal32 res = (IntVal32 0) - bval"
    using resdef unfolding minus_Value_def plus_Value_def
    using xtype btype by auto
  have "IntVal32 res' = (IntVal32 0) - bval"
    using sub_right_add1(4) eval.NegateNode bval evalDet by simp
  with res show ?case
    by (metis Value.inject(1))
next
  case (sub_right_add2 right a b)
  obtain aval where aval: "[g, m, p] \<turnstile> kind g a \<mapsto> aval"
    using sub_right_add2(4) eval.NegateNode by auto
  then have resdef: "IntVal32 res = xval - (aval + xval)"
    using sub_right_add2(3,1) aval xval sub_right_add2(5) eval.SubNode eval.AddNode
    using evalDet by simp
  have xtype: "\<exists> v. xval = IntVal32 v" using resdef sub_int32_typesafe by metis
  have btype: "\<exists> v. aval = IntVal32 v" using resdef sub_int32_typesafe add_int32_typesafe by metis
  have res: "IntVal32 res = (IntVal32 0) - aval"
    using resdef unfolding minus_Value_def plus_Value_def
    using xtype btype by auto
  have "IntVal32 res' = (IntVal32 0) - aval"
    using sub_right_add2(4) eval.NegateNode aval evalDet by simp
  with res show ?case
    by (metis Value.inject(1))
next
  case (sub_right_sub right a b)
  obtain bval where bval: "[g, m, p] \<turnstile> kind g b \<mapsto> bval"
    using sub_right_sub(4) eval.RefNode by auto
  then have resdef: "IntVal32 res = xval - (xval - bval)"
    using sub_right_sub(3,1) bval xval sub_right_sub(5) eval.SubNode
    using evalDet by simp
  have xtype: "\<exists> v. xval = IntVal32 v" using resdef sub_int32_typesafe by metis
  have btype: "\<exists> v. bval = IntVal32 v" using resdef sub_int32_typesafe by metis
  have res: "IntVal32 res = bval"
    using resdef unfolding minus_Value_def plus_Value_def
    using xtype btype by auto
  have "IntVal32 res' = bval"
    using sub_right_sub(4) eval.RefNode bval evalDet by simp
  with res show ?case by auto
next
  case (sub_yzero y x)
  have 0: "IntVal32 res = xval - yval"
    using sub_yzero(8) unfolding minus_Value_def by simp
  then have 1: "\<exists>v . xval = IntVal32 v"
    using sub_int32_typesafe by metis
  have "yval = IntVal32 0"
    using eval.ConstantNode yval sub_yzero(1,5) by auto
  then have res: "IntVal32 res = xval"
    using 0 1 unfolding minus_Value_def by auto
  have "IntVal32 res' = xval"
    using sub_yzero(4,5) xval eval.RefNode evalDet by simp
  with res show ?case by auto
next
  case (sub_xzero x y)
  have 0: "\<exists>v . xval = IntVal32 v"
    using sub_xzero(8) sub_int32_typesafe unfolding minus_Value_def by metis
  have 1: "\<exists>v . yval = IntVal32 v"
    using sub_xzero(8) sub_int32_typesafe unfolding minus_Value_def by metis
  have "xval = IntVal32 0"
    using sub_xzero(1,5) eval.ConstantNode xval by auto
  then have res: "IntVal32 res = (IntVal32 0) - yval"
    using sub_xzero(8) xval unfolding minus_Value_def by simp
  have "IntVal32 res' = (IntVal32 0) - yval"
    using eval.NegateNode sub_xzero(4,5) yval evalDet by simp
  with res show ?case using sub_det by blast 
next
  case (sub_y_negate nb b a)
  obtain bval where bval: "[g, m, p] \<turnstile> kind g b \<mapsto> bval"
    using sub_y_negate(4) by auto
  have xtype: "\<exists>v . xval = IntVal32 v"
    using sub_y_negate(8) sub_int32_typesafe unfolding minus_Value_def by metis
  have ytype: "\<exists>v . yval = IntVal32 v"
    using sub_y_negate(8) sub_int32_typesafe unfolding minus_Value_def by metis
  have yeval: "yval = (IntVal32 0) - bval"
    using sub_y_negate(1,5) eval.NegateNode bval evalDet yval by simp
  then have btype: "\<exists>v . bval = IntVal32 v"
    using sub_int32_typesafe ytype by simp
  have 1: "IntVal32 res = xval - ((IntVal32 0) - bval)"
    using sub_y_negate(8) yeval unfolding minus_Value_def by simp
  have 2: "... = xval + bval"
    using xtype btype unfolding minus_Value_def plus_Value_def by auto
  have 3: "... = IntVal32 res'"
    using sub_y_negate(4,5) xval bval eval.AddNode
    by (metis IRNode.inject(39) evalDet)
  then show ?case using 1 2 3 by simp
qed
qed

lemma CanonicalizeIfProof:
  fixes m::MapState and h::RefFieldHeap
  assumes "kind g nid = before"
  assumes "CanonicalizeIf g before after"
  assumes "g' = replace_node nid (after, s) g"
  assumes "[g, p] \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "nid | g \<sim> g'"
  using assms(2) assms 
proof (induct rule: CanonicalizeIf.induct)
  case (trueConst cond condv tb fb)
  have gstep: "[g, p] \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using ConstantNode IfNode trueConst.hyps(1) trueConst.hyps(2) trueConst.prems(1)
    using step.IfNode by presburger
  have g'step: "[g', p] \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using replace_node_lookup
    by (simp add: stepRefNode trueConst.prems(3))
  from gstep g'step show ?case
    using lockstep_strong_bisimilulation assms(3) by simp
next
  case (falseConst cond condv tb fb)
  have gstep: "[g, p] \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    using ConstantNode IfNode falseConst.hyps(1) falseConst.hyps(2) falseConst.prems(1)
    using step.IfNode by presburger
  have g'step: "[g', p] \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    using replace_node_lookup
    by (simp add: falseConst.prems(3) stepRefNode)
  from gstep g'step show ?case
    using lockstep_strong_bisimilulation assms(3) by simp
next
  case (eqBranch cond tb fb)
  have cval: "\<exists>v. ([g, m, p] \<turnstile> kind g cond \<mapsto> v)"
    using IfNodeCond
    by (meson eqBranch.prems(1) eqBranch.prems(4))
  then have gstep: "[g, p] \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using eqBranch(2,3) assms(4) IfNodeStepCases by blast
  have g'step: "[g', p] \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    by (simp add: eqBranch.prems(3) stepRefNode)
  from gstep g'step show ?thesis
    using lockstep_strong_bisimilulation assms(3) by simp
next
  case (eqCondition cond x tb fb)
  obtain condv where condval: "([g, m, p] \<turnstile> kind g cond \<mapsto> condv)"
    using IfNodeCond
    by (meson eqCondition.prems(1) eqCondition.prems(4))
  have "val_to_bool condv"
    using condval eqCondition.hyps evalDet by fastforce
  then have gstep: "[g, p] \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using step.IfNode
    using condval eqCondition.prems(1) by presburger
  have g'step: "[g', p] \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using replace_node_lookup
    using IRNode.simps(2114) eqCondition.prems(3) stepRefNode by presburger
  from gstep g'step show ?thesis
    using lockstep_strong_bisimilulation assms(3) by simp
qed


end