section \<open>Canonicalization Phase\<close>

theory Canonicalization
  imports 
    Proofs.IRGraphFrames
    Proofs.Stuttering
    Proofs.Bisimulation
    Proofs.Form
begin

inductive Canonicalize_ConditionalNode :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" where
  negate_condition: (* ConditionalNode.findSynonym (252) *)
  "\<lbrakk>kind g cond = LogicNegationNode flip\<rbrakk>
  \<Longrightarrow> Canonicalize_ConditionalNode g (ConditionalNode cond tb fb) (ConditionalNode flip fb tb)" |
  
  const_true: (* ConditionalNode.findSynonym (258) *)
  "\<lbrakk>kind g cond = ConstantNode val;
    val_to_bool val\<rbrakk>
  \<Longrightarrow> Canonicalize_ConditionalNode g (ConditionalNode cond tb fb) (RefNode tb)" |

  const_false: (* ConditionalNode.findSynonym (256) *)
  "\<lbrakk>kind g cond = ConstantNode val;
    \<not>(val_to_bool val)\<rbrakk>
  \<Longrightarrow> Canonicalize_ConditionalNode g (ConditionalNode cond tb fb) (RefNode fb)" |

  eq_branches: (* ConditionalNode.canonicalizeConditional (151) *)
  "\<lbrakk>tb = fb\<rbrakk>
  \<Longrightarrow> Canonicalize_ConditionalNode g (ConditionalNode cond tb fb) (RefNode tb)" |

  cond_eq: (* ConditionalNode.canonicalizeConditional (155) *)
  "\<lbrakk>kind g cond = IntegerEqualsNode tb fb\<rbrakk>
  \<Longrightarrow> Canonicalize_ConditionalNode g (ConditionalNode cond tb fb) (RefNode fb)" |

  condition_bounds_x: (* ConditionalNode.canonicalizeConditional (169) *)
  "\<lbrakk>kind g cond = IntegerLessThanNode tb fb;
    stpi_upper (stamp g tb) \<le> stpi_lower (stamp g fb)\<rbrakk>
  \<Longrightarrow> Canonicalize_ConditionalNode g (ConditionalNode cond tb fb) (RefNode tb)" |

  condition_bounds_y: (* ConditionalNode.canonicalizeConditional (174) *)
  "\<lbrakk>kind g cond = IntegerLessThanNode fb tb;
    stpi_upper (stamp g fb) \<le> stpi_lower (stamp g tb)\<rbrakk>
  \<Longrightarrow> Canonicalize_ConditionalNode g (ConditionalNode cond tb fb) (RefNode tb)"

  (* ... and more *)

lemma Canonicalize_ConditionalNode_Proof:
  assumes "Canonicalize_ConditionalNode g before after"
  assumes "wff_stamps g"
  assumes "g m \<turnstile> before \<mapsto> res"
  shows "g m \<turnstile> after \<mapsto> res"
  using assms(1) assms 
proof (induct rule: Canonicalize_ConditionalNode.induct)
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
      by (smt (z3) ConditionalNode ConditionalNodeE \<open>flipv \<noteq> 0\<close> fbval flipv negate_condition.prems(3))
  next
    case False
    have "flipv = 0"
      using invert False sorry
    then have "tbval = res"
      using eval.ConditionalNode tbval fbval flipv negate_condition
      by (smt (verit, del_insts) ConditionalNodeE False Value.inject(1) condv evalDet)
    then show ?thesis
      by (smt (verit, best) ConditionalNode ConditionalNodeE \<open>flipv = 0\<close> flipv negate_condition.prems(3) tbval)
  qed
next
  case (const_true g cond val tb fb)
  then show ?case
    using eval.RefNode by force
next
  case (const_false g cond val tb fb)
  then show ?case
    using eval.RefNode by force
next
  case (eq_branches tb fb g cond)
  then show ?case
    using eval.RefNode by force
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
      by (smt (verit) ConditionalNodeE cond_eq.prems(3) condv eval.RefNode evalDet val_to_bool.simps(1))
  qed
next
  case (condition_bounds_x g cond tb fb)
  obtain tbval b where tbval: "g m \<turnstile> kind g tb \<mapsto> IntVal b tbval"
    using condition_bounds_x.prems(3) by blast
  obtain fbval b where fbval: "g m \<turnstile> kind g fb \<mapsto> IntVal b fbval"
    using condition_bounds_x.prems(3) by blast
  have "tbval \<ge> fbval"
    using condition_bounds_x.prems(2) tbval fbval condition_bounds_x.hyps(2) 
      valid_value.simps
    unfolding wff_stamps.simps sorry
  then have "res = IntVal b tbval"
    using ConditionalNodeE tbval fbval sorry
  then show ?case
    using condition_bounds_x.prems(3) eval.RefNode evalDet tbval by blast
next
  case (condition_bounds_y g cond fb tb)
then show ?case sorry
qed


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

inductive CanonicalizeAdd :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool" 
  for g where
  add_both_const:
  "\<lbrakk>kind g x = ConstantNode c_1;
    kind g y = ConstantNode c_2;
    val = intval_add c_1 c_2\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd g (AddNode x y) (ConstantNode val)" |

  add_xzero:
  "\<lbrakk>kind g x = ConstantNode c_1;
    \<not>(is_ConstantNode (kind g y));
    c_1 = (IntVal b 0)\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd g (AddNode x y) (RefNode y)" |

  add_yzero:
  "\<lbrakk>\<not>(is_ConstantNode (kind g x));
    kind g y = ConstantNode c_2;
    c_2 = (IntVal b 0)\<rbrakk>
    \<Longrightarrow> CanonicalizeAdd g (AddNode x y) (RefNode x)"

lemma canonicalize_add:
  assumes "CanonicalizeAdd g before after"
  assumes "g m \<turnstile> before \<mapsto> res"
  shows "g m \<turnstile> after \<mapsto> res"
proof -
  obtain x y where addkind: "before = AddNode x y"
    using CanonicalizeAdd.simps assms by auto
  from addkind
  obtain xval where xval: "g m \<turnstile> kind g x \<mapsto> xval"
    using assms(2) by blast
  from addkind
  obtain yval where yval: "g m \<turnstile> kind g y \<mapsto> yval"
    using assms(2) by blast
  have res: "res = intval_add xval yval"
    using assms(2) eval.AddNode
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
    using add_xzero.prems(2) yval by fastforce
  then have "res = intval_add (IntVal b 0) yval"
    using eval.AddNode eval.ConstantNode add_xzero(1,3,4)
    using evalDet by presburger
  then show ?case using eval.RefNode yval add_val_xzero 
    apply (cases yval; auto)
    by (metis Value.inject(1) zero_neq_numeral)+
next
  case (add_yzero x y c_2 b)
  have yeval: "g m \<turnstile> kind g y \<mapsto> (IntVal b 0)"
    by (simp add: ConstantNode add_yzero.hyps(2) add_yzero.hyps(3))
  have yeval: "g m \<turnstile> kind g x \<mapsto> xval"
    using add_yzero.prems(2) xval by fastforce
  then have "res = intval_add xval (IntVal b 0)"
    using eval.AddNode eval.ConstantNode add_yzero(2,3,4)
    using evalDet by presburger
  then show ?case using eval.RefNode xval add_val_yzero 
    apply (cases xval; auto)
    by (metis Value.inject(1) zero_neq_numeral)+
qed
qed


inductive CanonicalizeIf :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> bool"
  for g where
  trueConst:
  "\<lbrakk>kind g cond = ConstantNode condv;
    val_to_bool condv\<rbrakk>
   \<Longrightarrow> CanonicalizeIf g (IfNode cond tb fb) (RefNode tb)" |

  falseConst:
  "\<lbrakk>kind g cond = ConstantNode condv;
    \<not>(val_to_bool condv)\<rbrakk>
   \<Longrightarrow> CanonicalizeIf g (IfNode cond tb fb) (RefNode fb)" |
  
  eqBranch:
  "\<lbrakk>\<not>(is_ConstantNode (kind g cond));
    tb = fb\<rbrakk>
   \<Longrightarrow> CanonicalizeIf g (IfNode cond tb fb) (RefNode tb)"

lemma canonicalize_if:
  fixes m::MapState and h::FieldRefHeap
  assumes "kind g nid = before"
  assumes "CanonicalizeIf g before after"
  assumes "g' = replace_node nid (after, s) g"
  shows "nid | g \<sim> g'"
  using assms(2) assms 
proof (induct rule: CanonicalizeIf.induct)
  case (trueConst cond condv tb fb)
  have gstep: "g \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using ConstantNode IfNode trueConst.hyps(1) trueConst.hyps(2) trueConst.prems(1) by presburger
  have g'step: "g' \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using replace_node_lookup
    by (simp add: step.RefNode trueConst.prems(3))
  from gstep g'step show ?case
    using lockstep_strong_bisimilulation assms(3) by simp
next
  case (falseConst cond condv tb fb)
  have gstep: "g \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    using ConstantNode IfNode falseConst.hyps(1) falseConst.hyps(2) falseConst.prems(1) by presburger
  have g'step: "g' \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    using replace_node_lookup
    by (simp add: falseConst.prems(3) step.RefNode)
  from gstep g'step show ?case
    using lockstep_strong_bisimilulation assms(3) by simp
next
  case (eqBranch cond tb fb)
  fix val
  show ?case proof (cases "g m \<turnstile> kind g cond \<mapsto> val")
    case True
    have gstep: "g \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
      using eqBranch(2,3) step.IfNode True by metis
    have g'step: "g' \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
      by (simp add: eqBranch.prems(3) step.RefNode)
    from gstep g'step show ?thesis
      using lockstep_strong_bisimilulation assms(3) by simp
  next
    case False
    then show ?thesis sorry
  qed
qed

end