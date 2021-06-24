theory
  CanonicalizationProofs
imports
  Canonicalization
begin

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
  obtain tbval where tbval: "[g, m, p] \<turnstile> kind g tb \<mapsto> tbval"
    using negate_condition.prems(3) by blast
  obtain fbval where fbval: "[g, m, p] \<turnstile> kind g fb \<mapsto> fbval"
    using negate_condition.prems(3) by blast
  show ?case proof (cases "condv = 0")
    case True
    have "flipv \<noteq> 0"
      using eval.LogicNegationNode condv flipv
      using True evalDet negate_condition.hyps by fastforce
    then have "fbval = res"
      using eval.ConditionalNode tbval fbval flipv negate_condition
      by (smt (verit, del_insts) ConditionalNodeE True Value.inject(1) condv evalDet)
    then show ?thesis
      by (smt (verit, best) ConditionalNodeE True Value.inject(1) bit.compl_zero evalDet fbval flipv invert negate_condition.prems(4))
  next
    case False
    have flipv_range: "flipv \<in> {0, 1}"
      using assms(2) flipv wf_value_bit_range
      by (metis False insertI1 invert val_to_bool.simps(1))
    have "(NOT flipv) \<noteq> 0"
      using False invert
      by (metis bit.compl_zero val_to_bool.simps(1) zero_neq_neg_one)
    then have "flipv \<noteq> 1"
      using not_eq_complement False invert by force
    then have "flipv = 0"
      using flipv_range by auto
    then have "tbval = res"
      using eval.ConditionalNode tbval fbval flipv negate_condition
      by (smt (verit, del_insts) ConditionalNodeE False Value.inject(1) condv evalDet)
    then show ?thesis
      using \<open>flipv = 0\<close> evalDet flipv negate_condition.prems(4) tbval by fastforce
  qed
next
  case (const_true g cond val tb fb)
  then show ?case
    using eval.RefNode evalDet by force
next
  case (const_false g cond val tb fb)
  then show ?case
    using eval.RefNode evalDet by force
next
  case (eq_branches tb fb g cond)
  then show ?case
    using eval.RefNode evalDet by force
next
  case (cond_eq g cond tb fb)
  then obtain condv where condv: "[g, m, p] \<turnstile> kind g cond \<mapsto> condv"
    by blast
  obtain tbval where tbval: "[g, m, p] \<turnstile> kind g tb \<mapsto> tbval"
    using cond_eq.prems(3) by blast
  obtain fbval where fbval: "[g, m, p] \<turnstile> kind g fb \<mapsto> fbval"
    using cond_eq.prems(3) by blast
  from cond_eq show ?case proof (cases "val_to_bool condv")
    case True
    have "tbval = fbval" using IntegerEqualsNodeE condv cond_eq(1)
      by (smt (z3) True bool_to_val.simps(2) evalDet fbval tbval val_to_bool.simps(1))
    then show ?thesis using cond_eq
      by (smt (verit, ccfv_threshold) ConditionalNodeE eval.RefNode evalDet fbval tbval)
  next
    case False
    then show ?thesis
      by (smt (verit) ConditionalNodeE cond_eq.prems(3) cond_eq.prems(4) condv eval.RefNode evalDet val_to_bool.simps(1))
  qed
next
  case (condition_bounds_x g cond tb fb)
  obtain tbval b where tbval: "[g, m, p] \<turnstile> kind g tb \<mapsto> IntVal b tbval"
    using condition_bounds_x.prems(3) by blast
  obtain fbval b where fbval: "[g, m, p] \<turnstile> kind g fb \<mapsto> IntVal b fbval"
    using condition_bounds_x.prems(3) by blast
  have "tbval \<le> fbval"
    using condition_bounds_x.prems(2) tbval fbval condition_bounds_x.hyps(2) int_valid_range
    unfolding wf_stamps.simps 
    by (smt (verit, best) Stamp.sel(2) Stamp.sel(3) Value.inject(1) eval_in_ids valid_value.elims(2) valid_value.simps(3))
  then have "res = IntVal b tbval"
    using ConditionalNodeE tbval fbval
    by (smt (verit, del_insts) IntegerLessThanNodeE Value.inject(1) bool_to_val.simps(1) condition_bounds_x.hyps(1) condition_bounds_x.prems(3) evalDet)
  then show ?case
    using condition_bounds_x.prems(3) eval.RefNode evalDet tbval
    using ConditionalNodeE Value.sel(1) condition_bounds_x.prems(4) by blast
next
  case (condition_bounds_y g cond fb tb)
  obtain tbval b where tbval: "[g, m, p] \<turnstile> kind g tb \<mapsto> IntVal b tbval"
    using condition_bounds_y.prems(3) by blast
  obtain fbval b where fbval: "[g, m, p] \<turnstile> kind g fb \<mapsto> IntVal b fbval"
    using condition_bounds_y.prems(3) by blast
  have "tbval \<ge> fbval"
    using condition_bounds_y.prems(2) tbval fbval condition_bounds_y.hyps(2) int_valid_range
    unfolding wf_stamps.simps 
    by (smt (verit, ccfv_SIG) Stamp.disc(2) boundsAlwaysOverlap eval_in_ids valid_value.elims(2) valid_value.simps(3))
  then have "res = IntVal b tbval"
    using ConditionalNodeE tbval fbval
    by (smt (verit) IntegerLessThanNodeE Value.inject(1) bool_to_val.simps(1) condition_bounds_y.hyps(1) condition_bounds_y.prems(3) evalDet)
  then show ?case
    using condition_bounds_y.prems(3) eval.RefNode evalDet tbval
    using ConditionalNodeE Value.sel(1) condition_bounds_y.prems(4) by blast
qed

lemma add_zero_32:
  assumes "wf_value (IntVal 32 y)"
  shows "(IntVal 32 0) + (IntVal 32 y) = (IntVal 32 y)"
proof -
  have "-(2^31) \<le> y \<and> y < 2^31"
    using assms unfolding wf_value.simps by simp
  then show ?thesis unfolding plus_Value_def intval_add.simps apply auto
    using \<open>- (2 ^ 31) \<le> y \<and> y < 2 ^ 31\<close> signed_take_bit_int_eq_self by blast
qed

lemma add_zero_64:
  assumes "wf_value (IntVal 64 y)"
  shows "(IntVal 64 0) + (IntVal 64 y) = (IntVal 64 y)"
proof -
  have "-(2^63) \<le> y \<and> y < 2^63"
    using assms unfolding wf_value.simps by simp
  then show ?thesis unfolding plus_Value_def intval_add.simps apply auto
    using \<open>- (2 ^ 63) \<le> y \<and> y < 2 ^ 63\<close> signed_take_bit_int_eq_self by blast
qed

lemma 
  assumes "wf_value (IntVal bc y)"
  assumes "bc \<in> {32,64}"
  shows "(IntVal bc 0) + (IntVal bc y) = (IntVal bc y)"
proof -
  have bounds: "-(2^((nat bc)-1)) \<le> y \<and> y < 2^((nat bc)-1)"
    using assms unfolding wf_value.simps by auto
  then show ?thesis unfolding intval_add.simps apply auto
    using bounds signed_take_bit_int_eq_self assms plus_Value_def
    by auto
qed


(* (-x + y) \<Rightarrow> (y - x) *)
lemma 
  assumes "wf_value (IntVal b x) \<and> wf_value (IntVal b y)"
  shows "((IntVal b 0) - (IntVal b x)) + (IntVal b y) = (IntVal b y) - (IntVal b x)"
  using assms unfolding plus_Value_def minus_Value_def wf_value.simps by simp

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
  shows "\<exists>res. x - y = IntVal32 res = (\<exists>xval yval. x = IntVal32 xval \<and> y = IntVal32 yval)"
  unfolding minus_Value_def
  by (induction rule: intval_add.induct; simp)

lemma add_int64_typesafe:
  fixes x y :: Value
  shows "\<exists>res. x + y = IntVal64 res = (\<exists>xval yval. x = IntVal64 xval \<and> y = IntVal64 yval)"
  unfolding plus_Value_def
  by (induction rule: intval_add.induct; simp)

lemma sub_int64_typesafe:
  fixes x y :: Value
  shows "\<exists>res. x - y = IntVal64 res = (\<exists>xval yval. x = IntVal64 xval \<and> y = IntVal64 yval)"
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
    using sub_int32_typesafe negdef sorry (* should be easy *)
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
    using sub_int32_typesafe negdef sorry (* should be easy *)
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

experiment begin
lemma CanonicalizeSubProof:
  assumes "CanonicalizeSub g before after"
  assumes "wf_stamps g"
  assumes "[g, m, p] \<turnstile> before \<mapsto> IntVal b1 res"
  assumes "[g, m, p] \<turnstile> after \<mapsto> IntVal b2 res'"
  shows "res = res'"
  using assms proof (induct rule: CanonicalizeSub.induct)
case (sub_same x y b l h)
then show ?case sorry
next
  case (sub_both_const x c_1 y c_2 val)
  then show ?case sorry
next
  case (sub_left_add1 left a b)
  then show ?case sorry
next
  case (sub_left_add2 left a b)
  then show ?case sorry
next
  case (sub_left_sub left a b)
  then show ?case sorry
next
  case (sub_right_add1 right a b)
  then show ?case sorry
next
  case (sub_right_add2 right a b)
  then show ?case sorry
next
  case (sub_right_sub right a b)
  then show ?case sorry
next
  case (sub_yzero y uu x)
  then show ?case sorry
next
  case (sub_xzero x uv y)
  then show ?case sorry
next
  case (sub_y_negate nb b a)
  then show ?case sorry
qed
end

lemma CanonicalizeIfProof:
  fixes m::MapState and h::FieldRefHeap
  assumes "kind g nid = before"
  assumes "CanonicalizeIf g before after"
  assumes "g' = replace_node nid (after, s) g"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "nid | g \<sim> g'"
  using assms(2) assms 
proof (induct rule: CanonicalizeIf.induct)
  case (trueConst cond condv tb fb)
  have gstep: "g, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using ConstantNode IfNode trueConst.hyps(1) trueConst.hyps(2) trueConst.prems(1)
    using step.IfNode by presburger
  have g'step: "g', p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using replace_node_lookup
    by (simp add: stepRefNode trueConst.prems(3))
  from gstep g'step show ?case
    using lockstep_strong_bisimilulation assms(3) by simp
next
  case (falseConst cond condv tb fb)
  have gstep: "g, p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    using ConstantNode IfNode falseConst.hyps(1) falseConst.hyps(2) falseConst.prems(1)
    using step.IfNode by presburger
  have g'step: "g', p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    using replace_node_lookup
    by (simp add: falseConst.prems(3) stepRefNode)
  from gstep g'step show ?case
    using lockstep_strong_bisimilulation assms(3) by simp
next
  case (eqBranch cond tb fb)
  have cval: "\<exists>v. ([g, m, p] \<turnstile> kind g cond \<mapsto> v)"
    using IfNodeCond
    by (meson eqBranch.prems(1) eqBranch.prems(4))
  then have gstep: "g, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using eqBranch(2,3) assms(4) IfNodeStepCases by blast
  have g'step: "g', p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    by (simp add: eqBranch.prems(3) stepRefNode)
  from gstep g'step show ?thesis
    using lockstep_strong_bisimilulation assms(3) by simp
next
  case (eqCondition cond x tb fb)
  have cval: "\<exists>v. ([g, m, p] \<turnstile> kind g cond \<mapsto> v)"
    using IfNodeCond
    by (meson eqCondition.prems(1) eqCondition.prems(4))
  have gstep: "g, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using step.IfNode eval.IntegerEqualsNode
    by (smt (z3) IntegerEqualsNodeE bool_to_val.simps(1) cval eqCondition.hyps eqCondition.prems(1) val_to_bool.simps(1))
  have g'step: "g', p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using replace_node_lookup
    using IRNode.simps(2114) eqCondition.prems(3) stepRefNode by presburger
  from gstep g'step show ?thesis
    using lockstep_strong_bisimilulation assms(3) by simp
qed


lemma double_negate: 
 "\<lbrakk>wf_bool x\<rbrakk> 
  \<Longrightarrow> bool_to_val (\<not>(val_to_bool (bool_to_val (\<not>(val_to_bool x))))) = x" 
  using wf_bool.elims(2) by fastforce

lemma logic_negation_bool_inputs:
  assumes "wf_values g"
  assumes "[g, m, p] \<turnstile> kind g inp \<mapsto> inp_val"
  assumes "kind g n = LogicNegationNode inp"
  assumes "[g, m, p] \<turnstile> kind g n \<mapsto> val"
  shows "wf_bool inp_val" 
  using assms
proof - 
  have is_logic_node: "is_LogicNode (kind g n)"
    using is_LogicNode.simps
    by (simp add: assms(3))
  have inp_is_input: "inp \<in> set (inputs_of (kind g n))" 
    by (simp add: assms(3))
  have n_is_id: "n \<in> ids g" 
    by (simp add: assms(3))
  then have wflni: "wf_logic_node_inputs g n" 
    using wf_values.simps assms(1) is_logic_node inp_is_input assms(2) assms(4) by blast
  then show ?thesis 
    using assms(2) inp_is_input wf_logic_node_inputs.simps by blast
qed

lemma CanonicalizeLogicNegationProof:
  assumes "CanonicalizeLogicNegation g before after"
  assumes "wf_stamps g"
  assumes "[g, m, p] \<turnstile> before \<mapsto> IntVal b res"
  assumes "[g, m, p] \<turnstile> after \<mapsto> IntVal b' res'"
  assumes "wf_values g"
  shows "res = res'"
  using assms 
proof (induct rule: CanonicalizeLogicNegation.induct)
  case (logical_not_const nx val neg_val)
  then show ?case 
    by (smt (verit) ConstantNodeE LogicNegationNodeE Value.inject(1) val_to_bool.simps(1))
next
  case (logical_not_not nx x)
  obtain nxval where nxval: "[g, m, p] \<turnstile> kind g nx \<mapsto> nxval"
    using logical_not_not.prems(2) by blast
  obtain xval where xval: "[g, m, p] \<turnstile> kind g x \<mapsto> xval"
    using logical_not_not.prems(3) by blast
  obtain beforeval where beforeval: "[g, m, p] \<turnstile> before \<mapsto> beforeval"
    using assms(3) by auto
  obtain refval where refval: "[g, m, p] \<turnstile> after \<mapsto> refval"
    using assms(4) by auto
  then have "wf_bool xval" 
    using logic_negation_bool_inputs logical_not_not.hyps logical_not_not.prems(4) nxval xval by blast
  then have ref_xval_eq: "refval = xval" 
    by (metis RefNode assms(4) evalDet logical_not_not.prems(3) refval xval)
  then have "nxval = bool_to_val (\<not>(val_to_bool xval))"
    by (smt (verit) LogicNegationNodeE evalDet logical_not_not.hyps nxval val_to_bool.simps(1) xval)
  then have "beforeval = bool_to_val (\<not>(val_to_bool nxval))"
    by (smt (verit) LogicNegationNodeE assms(3) beforeval evalDet logical_not_not.prems(2) nxval val_to_bool.simps(1))
  then have double_negate_xval: "bool_to_val (\<not>(val_to_bool (bool_to_val (\<not>(val_to_bool xval))))) = xval"
    by (simp add: \<open>wf_bool xval\<close> double_negate)
  then have node_eq_eq: "beforeval = xval"
    by (simp add: \<open>beforeval = bool_to_val (\<not> val_to_bool nxval)\<close> \<open>nxval = bool_to_val (\<not> val_to_bool xval)\<close>)
  show ?thesis 
    by (metis Value.inject(1) assms(3) assms(4) beforeval evalDet node_eq_eq ref_xval_eq refval)
qed

end