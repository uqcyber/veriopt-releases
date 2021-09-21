section \<open>Properties of Control-flow Semantics\<close>

theory IRStepThms
  imports
    IRStepObj
    IRTreeEvalThms
begin

text \<open>
We prove that within the same graph, a configuration triple will always
transition to the same subsequent configuration. Therefore, our step semantics
is deterministic.
\<close>

theorem stepDet:
   "(g, p \<turnstile> (nid,m,h) \<rightarrow> next) \<Longrightarrow>
   (\<forall> next'. ((g, p \<turnstile> (nid,m,h) \<rightarrow> next') \<longrightarrow> next = next'))"
proof (induction rule: "step.induct")
  case (SequentialNode nid "next" m h)
  have notif: "\<not>(is_IfNode (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps 
    by (metis is_IfNode_def)
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps 
    by (metis is_AbstractEndNode.simps is_EndNode.elims(2) is_LoopEndNode_def)
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps
    by (metis is_NewInstanceNode_def)
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps
    by (metis is_LoadFieldNode_def)
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps
    by (metis is_StoreFieldNode_def)
  have notdivrem:  "\<not>(is_IntegerDivRemNode (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps is_SignedDivNode_def is_SignedRemNode_def
    by (metis is_IntegerDivRemNode.simps)
  from notif notend notnew notload notstore notdivrem
  show ?case using SequentialNode step.cases
    by (smt (z3) IRNode.disc(2042) IRNode.disc(920) IRNode.discI(30) Pair_inject is_sequential_node.simps(18) is_sequential_node.simps(41) is_sequential_node.simps(42))
next
  case (IfNode nid cond tb fb m val "next" h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps is_AbstractMergeNode.simps
    by (simp add: IfNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using is_AbstractEndNode.simps
    by (simp add: IfNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))" 
    using is_AbstractEndNode.simps
    by (simp add: IfNode.hyps(1))
  from notseq notend notdivrem show ?case using IfNode repDet evalDet IRNode.distinct IRNode.inject(11) Pair_inject step.simps
    by (smt (z3) IRNode.distinct IRNode.inject(11) Pair_inject step.simps)
next
  case (EndNodes nid merge i phis inputs m vs m' h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps is_sequential_node.simps 
    by (metis is_EndNode.elims(2) is_LoopEndNode_def)
  have notif: "\<not>(is_IfNode (kind g nid))"
    using EndNodes.hyps(1) is_IfNode_def is_AbstractEndNode.elims
    by (metis IRNode.distinct_disc(989) is_EndNode.simps(12))
  have notref: "\<not>(is_RefNode (kind g nid))"
    using EndNodes.hyps(1) is_sequential_node.simps
    using IRNode.disc(1899) IRNode.distinct(1473) is_AbstractEndNode.simps is_EndNode.elims(2) is_LoopEndNode_def is_RefNode_def
    by metis
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps
    using IRNode.distinct_disc(1442) is_EndNode.simps(29) is_NewInstanceNode_def
    by (metis IRNode.distinct_disc(1710) is_EndNode.simps(31))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps
    by (metis IRNode.distinct_disc(1526) is_EndNode.simps(20) is_LoadFieldNode_def)
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps
    using IRNode.distinct_disc(1504) is_EndNode.simps(39) is_StoreFieldNode_def 
    by fastforce
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps is_SignedDivNode_def is_SignedRemNode_def
    using IRNode.distinct_disc(1498) IRNode.distinct_disc(1500) is_IntegerDivRemNode.simps is_EndNode.simps(36) is_EndNode.simps(37) 
    by auto
  from notseq notif notref notnew notload notstore notdivrem
  show ?case using EndNodes repAllDet evalAllDet
    by (smt (z3) is_IfNode_def is_LoadFieldNode_def is_NewInstanceNode_def is_RefNode_def is_StoreFieldNode_def is_SignedDivNode_def is_SignedRemNode_def  Pair_inject is_IntegerDivRemNode.elims(3) step.cases)
next
  case (NewInstanceNode nid f obj nxt h' ref h m' m)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps is_AbstractMergeNode.simps
    by (simp add: NewInstanceNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using is_AbstractMergeNode.simps
    by (simp add: NewInstanceNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    using is_AbstractMergeNode.simps
    by (simp add: NewInstanceNode.hyps(1))
  have notref: "\<not>(is_RefNode (kind g nid))"
    using is_AbstractMergeNode.simps
    by (simp add: NewInstanceNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    using is_AbstractMergeNode.simps
    by (simp add: NewInstanceNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    using is_AbstractMergeNode.simps
    by (simp add: NewInstanceNode.hyps(1))
  have notdivrem:  "\<not>(is_IntegerDivRemNode (kind g nid))"
    using is_AbstractMergeNode.simps
    by (simp add: NewInstanceNode.hyps(1))
  from notseq notend notif notref notload notstore notdivrem
  show ?case using NewInstanceNode step.cases
    by (smt (verit) IRNode.distinct(2085) IRNode.distinct(2087) IRNode.inject(30) Pair_inject is_IfNode_def is_LoadFieldNode_def is_StoreFieldNode_def)
next
  case (LoadFieldNode nid f obj nxt m ref h v m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps is_AbstractMergeNode.simps
    by (simp add: LoadFieldNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using is_AbstractEndNode.simps
    by (simp add: LoadFieldNode.hyps(1))
  have notdivrem:  "\<not>(is_IntegerDivRemNode (kind g nid))"
    using is_AbstractEndNode.simps
    by (simp add: LoadFieldNode.hyps(1))
  from notseq notend notdivrem
  show ?case using LoadFieldNode step.cases repDet evalDet
    by (smt (z3) IRNode.distinct(1541) IRNode.distinct(1557) IRNode.distinct(1559) IRNode.distinct(1563) IRNode.distinct(983) IRNode.inject(19) Pair_inject Value.inject(4) option.distinct(1) option.inject)
next
  case (StaticLoadFieldNode nid f nxt h v m' m)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps is_AbstractMergeNode.simps
    by (simp add: StaticLoadFieldNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using is_AbstractEndNode.simps
    by (simp add: StaticLoadFieldNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: StaticLoadFieldNode.hyps(1))
  from notseq notend notdivrem
  show ?case using StaticLoadFieldNode step.cases
    by (smt (z3) IRNode.distinct(1541) IRNode.distinct(1557) IRNode.distinct(1559) IRNode.distinct(1563) IRNode.distinct(983) IRNode.inject(19) Pair_inject option.distinct(1))
next
  case (StoreFieldNode nid f newval uu obj nxt m val ref h' h m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps is_AbstractMergeNode.simps
    by (simp add: StoreFieldNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using is_AbstractEndNode.simps
    by (simp add: StoreFieldNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: StoreFieldNode.hyps(1))
  from notseq notend notdivrem
  show ?case using StoreFieldNode step.cases repDet evalDet
    by (smt (z3) IRNode.distinct(1027) IRNode.distinct(1563) IRNode.distinct(2091) IRNode.distinct(2323) IRNode.distinct(2343) IRNode.inject(41) Pair_inject Value.inject(4) option.distinct(1) option.inject)
next
  case (StaticStoreFieldNode nid f newval uv nxt m val h' h m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps is_AbstractMergeNode.simps
    by (simp add: StaticStoreFieldNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using is_AbstractEndNode.simps
    by (simp add: StaticStoreFieldNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: StaticStoreFieldNode.hyps(1))
  from notseq notend notdivrem
  show ?case using StoreFieldNode step.cases repDet evalDet
    by (smt (z3) IRNode.distinct(1027) IRNode.distinct(1563) IRNode.distinct(2091) IRNode.distinct(2323) IRNode.distinct(2343) IRNode.inject(41) Pair_inject StaticStoreFieldNode.hyps(1) StaticStoreFieldNode.hyps(2) StaticStoreFieldNode.hyps(3) StaticStoreFieldNode.hyps(4) StaticStoreFieldNode.hyps(5) option.distinct(1))
next
  case (SignedDivNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps is_AbstractMergeNode.simps
    by (simp add: SignedDivNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using is_AbstractEndNode.simps
    by (simp add: SignedDivNode.hyps(1))
  from notseq notend
  show ?case using SignedDivNode step.cases repDet evalDet
    by (smt (z3) IRNode.distinct(1021) IRNode.distinct(1557) IRNode.distinct(2085) IRNode.distinct(2319) IRNode.distinct(2323) IRNode.inject(38) Pair_inject)
next
  case (SignedRemNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps is_AbstractMergeNode.simps
    by (simp add: SignedRemNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using is_AbstractEndNode.simps
    by (simp add: SignedRemNode.hyps(1))
  from notseq notend
  show ?case using SignedRemNode step.cases repDet evalDet
    by (smt (z3) IRNode.distinct(1023) IRNode.distinct(1559) IRNode.distinct(2087) IRNode.distinct(2319) IRNode.distinct(2343) IRNode.inject(39) Pair_inject)
qed

lemma stepRefNode:
  "\<lbrakk>kind g nid = RefNode nid'\<rbrakk> \<Longrightarrow> g, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)"
  by (simp add: SequentialNode)

lemma IfNodeStepCases: 
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g \<turnstile> cond \<simeq> condE"
  assumes "[m, p] \<turnstile> condE \<mapsto> v"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "nid' \<in> {tb, fb}"
  using step.IfNode repDet stepDet assms
  by (metis insert_iff old.prod.inject)

lemma IfNodeSeq:
  shows "kind g nid = IfNode cond tb fb \<longrightarrow> \<not>(is_sequential_node (kind g nid))"
  unfolding is_sequential_node.simps by simp
  
lemma IfNodeCond:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "\<exists> condE v. ((g \<turnstile> cond \<simeq> condE) \<and> ([m, p] \<turnstile> condE \<mapsto> v))"
  using assms(2,1) by (induct "(nid,m,h)" "(nid',m,h)" rule: step.induct; auto)


lemma step_in_ids:
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')"
  shows "nid \<in> ids g"
  using assms apply (induct "(nid, m, h)" "(nid', m', h')" rule: step.induct)
  using is_sequential_node.simps(45) not_in_g 
  apply simp
  apply (metis is_sequential_node.simps(50))
  using ids_some
  using IRNode.distinct(1041) apply presburger
  using EndNodes(1) is_AbstractEndNode.simps is_EndNode.simps(45) ids_some
  apply (metis IRNode.disc(1099) is_EndNode.simps(49))
  by simp+

end
