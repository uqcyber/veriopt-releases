theory
  CanonicalizationProofs
imports
  Canonicalization
begin

lemma CanonicalizeConditionalProof:
  assumes "CanonicalizeConditional g before after"
  assumes "wff_graph g \<and> wff_stamps g \<and> wff_values g"
  assumes "g m \<turnstile> before \<mapsto> res"
  assumes "g m \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms(1) assms 
proof (induct rule: CanonicalizeConditional.induct)
  case (negate_condition g cond flip tb fb)
  obtain condv where condv: "g m \<turnstile> kind g cond \<mapsto> IntVal 1 condv"
    using negate_condition.prems(3) by blast
  then obtain flipv where flipv: "g m \<turnstile> kind g flip \<mapsto> IntVal 1 flipv"
    by (metis LogicNegationNodeE negate_condition.hyps)
  have invert: "condv = 0 \<longleftrightarrow> (NOT flipv) = 0"
    using eval.LogicNegationNode condv flipv
    by (metis Value.inject(1) evalDet negate_condition.hyps)
  obtain tbval where tbval: "g m \<turnstile> kind g tb \<mapsto> tbval"
    using negate_condition.prems(3) by blast
  obtain fbval where fbval: "g m \<turnstile> kind g fb \<mapsto> fbval"
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
      using assms(2) flipv wff_value_bit_range
      by (metis eval_in_ids mem_Collect_eq negate_condition.prems(2) wff_values.elims(2))
    have "(NOT flipv) \<noteq> 0"
      using False invert by fastforce
    then have "flipv \<noteq> 1"
      using not_eq_complement sorry
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
  then obtain condv where condv: "g m \<turnstile> kind g cond \<mapsto> condv"
    by blast
  obtain tbval where tbval: "g m \<turnstile> kind g tb \<mapsto> tbval"
    using cond_eq.prems(3) by blast
  obtain fbval where fbval: "g m \<turnstile> kind g fb \<mapsto> fbval"
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
  obtain tbval b where tbval: "g m \<turnstile> kind g tb \<mapsto> IntVal b tbval"
    using condition_bounds_x.prems(3) by blast
  obtain fbval b where fbval: "g m \<turnstile> kind g fb \<mapsto> IntVal b fbval"
    using condition_bounds_x.prems(3) by blast
  have "tbval \<le> fbval"
    using condition_bounds_x.prems(2) tbval fbval condition_bounds_x.hyps(2) int_valid_range
    unfolding wff_stamps.simps 
    by (smt (verit, best) Stamp.sel(2) Stamp.sel(3) Value.inject(1) eval_in_ids valid_value.elims(2) valid_value.simps(3))
  then have "res = IntVal b tbval"
    using ConditionalNodeE tbval fbval
    by (smt (verit, del_insts) IntegerLessThanNodeE Value.inject(1) bool_to_val.simps(1) condition_bounds_x.hyps(1) condition_bounds_x.prems(3) evalDet)
  then show ?case
    using condition_bounds_x.prems(3) eval.RefNode evalDet tbval
    using ConditionalNodeE Value.sel(1) condition_bounds_x.prems(4) by blast
next
  case (condition_bounds_y g cond fb tb)
  obtain tbval b where tbval: "g m \<turnstile> kind g tb \<mapsto> IntVal b tbval"
    using condition_bounds_y.prems(3) by blast
  obtain fbval b where fbval: "g m \<turnstile> kind g fb \<mapsto> IntVal b fbval"
    using condition_bounds_y.prems(3) by blast
  have "tbval \<ge> fbval"
    using condition_bounds_y.prems(2) tbval fbval condition_bounds_y.hyps(2) int_valid_range
    unfolding wff_stamps.simps 
    by (smt (verit, ccfv_SIG) Stamp.disc(2) boundsAlwaysOverlap eval_in_ids valid_value.elims(2) valid_value.simps(3))
  then have "res = IntVal b tbval"
    using ConditionalNodeE tbval fbval
    by (smt (verit) IntegerLessThanNodeE Value.inject(1) bool_to_val.simps(1) condition_bounds_y.hyps(1) condition_bounds_y.prems(3) evalDet)
  then show ?case
    using condition_bounds_y.prems(3) eval.RefNode evalDet tbval
    using ConditionalNodeE Value.sel(1) condition_bounds_y.prems(4) by blast
qed


lemma CanonicalizeAddProof:
  assumes "CanonicalizeAdd g before after"
  assumes "wff_graph g \<and> wff_stamps g"
  assumes "g m \<turnstile> before \<mapsto> res"
  assumes "g m \<turnstile> after \<mapsto> res'"
  shows "res = res'"
proof -
  obtain x y where addkind: "before = AddNode x y"
    using CanonicalizeAdd.simps assms by auto
  from addkind
  obtain xval where xval: "g m \<turnstile> kind g x \<mapsto> xval"
    using assms(3) by blast
  from addkind
  obtain yval where yval: "g m \<turnstile> kind g y \<mapsto> yval"
    using assms(3) by blast
  have res: "res = intval_add xval yval"
    using assms(3) eval.AddNode
    using addkind evalDet xval yval by presburger
  show ?thesis
    using assms addkind xval yval res
  proof (induct rule: "CanonicalizeAdd.induct")
case (add_both_const x c_1 y c_2 val)
  then show ?case using eval.ConstantNode by auto
next
  case (add_xzero x c_1 y b)
  have xeval: "g m \<turnstile> kind g x \<mapsto> (IntVal b 0)"
    by (simp add: ConstantNode add_xzero.hyps(1) add_xzero.hyps(3))
  have yeval: "g m \<turnstile> kind g y \<mapsto> yval"
    using add_xzero.prems(4) yval by blast
  then have "res = intval_add (IntVal b 0) yval"
    using eval.AddNode eval.ConstantNode add_xzero(1,3,5)
    using evalDet by presburger
  then show ?case using eval.RefNode yval sorry
next
  case (add_yzero x y c_2 b)
  have yeval: "g m \<turnstile> kind g y \<mapsto> (IntVal b 0)"
    by (simp add: ConstantNode add_yzero.hyps(2) add_yzero.hyps(3))
  have yeval: "g m \<turnstile> kind g x \<mapsto> xval"
    using add_yzero.prems(4) xval by fastforce
  then have "res = intval_add xval (IntVal b 0)"
    using eval.AddNode eval.ConstantNode add_yzero(2,3,5)
    using evalDet by presburger
  then show ?case using eval.RefNode xval sorry
next
  case (add_xsub x a y)
  then show ?case sorry
next
  case (add_ysub y a x)
  then show ?case sorry
next
  case (add_xnegate nx x y)
  then show ?case sorry
next
  case (add_ynegate ny y x)
  then show ?case sorry
qed
qed


lemma CanonicalizeSubProof:
  assumes "CanonicalizeSub g before after"
  assumes "wff_stamps g"
  assumes "g m \<turnstile> before \<mapsto> IntVal b1 res"
  assumes "g m \<turnstile> after \<mapsto> IntVal b2 res'"
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


lemma CanonicalizeIfProof:
  fixes m::MapState and h::FieldRefHeap
  assumes "kind g nid = before"
  assumes "CanonicalizeIf g before after"
  assumes "g' = replace_node nid (after, s) g"
  assumes "g \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "nid | g \<sim> g'"
  using assms(2) assms 
proof (induct rule: CanonicalizeIf.induct)
  case (trueConst cond condv tb fb)
  have gstep: "g \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using ConstantNode IfNode trueConst.hyps(1) trueConst.hyps(2) trueConst.prems(1)
    using step.IfNode by presburger
  have g'step: "g' \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using replace_node_lookup
    by (simp add: step.RefNode trueConst.prems(3))
  from gstep g'step show ?case
    using lockstep_strong_bisimilulation assms(3) by simp
next
  case (falseConst cond condv tb fb)
  have gstep: "g \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    using ConstantNode IfNode falseConst.hyps(1) falseConst.hyps(2) falseConst.prems(1)
    using step.IfNode by presburger
  have g'step: "g' \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    using replace_node_lookup
    by (simp add: falseConst.prems(3) step.RefNode)
  from gstep g'step show ?case
    using lockstep_strong_bisimilulation assms(3) by simp
next
  case (eqBranch cond tb fb)
  fix val
  have gstep: "g \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using eqBranch(2,3) step.IfNode assms(4)
    by (smt (verit) IRNode.disc(932) IRNode.distinct(947) IRNode.inject(11) IRNode.simps(938) IRNode.simps(958) IRNode.simps(972) IRNode.simps(974) IRNode.simps(978) Pair_inject isAbstractEndNodeType.simps is_EndNode.simps(12) is_sequential_node.simps(17) step.simps)
  have g'step: "g' \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    by (simp add: eqBranch.prems(3) step.RefNode)
  from gstep g'step show ?thesis
    using lockstep_strong_bisimilulation assms(3) by simp
next
  case (eqCondition cond x tb fb)
  fix val
  have gstep: "g \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using step.IfNode eval.IntegerEqualsNode
    by (smt (z3) IRNode.disc(932) IRNode.distinct(947) IRNode.sel(59) IRNode.simps(938) IRNode.simps(958) IRNode.simps(972) IRNode.simps(974) IRNode.simps(978) IntegerEqualsNodeE Pair_inject bool_to_val.simps(1) eqCondition.hyps eqCondition.prems(1) eqCondition.prems(4) isAbstractEndNodeType.simps is_EndNode.simps(12) is_sequential_node.simps(17) step.simps val_to_bool.simps(1))
  have g'step: "g' \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using replace_node_lookup
    using IRNode.simps(2114) eqCondition.prems(3) step.RefNode by presburger
  from gstep g'step show ?thesis
    using lockstep_strong_bisimilulation assms(3) by simp
qed


(*
lemma add_zero:
  assumes "x < (2 ^ (LENGTH('a) - 1))"
  shows "(sint ((word_of_int 0::('a::len word)) + word_of_int x::('a::len word))) = x"
proof -
  have "sint (word_of_int x::('a word)) = x"
    using assms sorry
  show ?thesis sorry
qed

value "word_of_int (-2)::(32word)"
value "sint (word_of_int (-2)::32word)"
value "sint (word_of_int 0 + word_of_int (-2)::32word)"


(* these are incorrect with the introduction of accurate addition semantics *)
(* most obviously due to the resultant b being either 32 or 64 *)
lemma add_val_xzero:
  shows "intval_add (IntVal b 0) (IntVal b yv) = (IntVal b yv)"
  unfolding intval_add.simps sorry

lemma add_val_yzero:
  shows "intval_add (IntVal b xv) (IntVal b 0) = (IntVal b xv)"
  unfolding intval_add.simps sorry
*)

end