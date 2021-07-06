section \<open>Properties of Control-flow Semantics\<close>

theory IRStepThms
  imports
    IRStepObj
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
    by (smt (verit) IRNode.discI(18) is_IfNode_def is_NewInstanceNode_def is_StoreFieldNode_def is_sequential_node.simps(38) is_sequential_node.simps(39) old.prod.inject)
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
  from notseq notend notdivrem show ?case using IfNode evalDet IRNode.distinct IRNode.inject(11) Pair_inject step.simps
(* TODO: update these cases.  May need a repDet thm as well as evalDet? *)
    
    by (smt (z3) IRNode.distinct IRNode.inject(11) Pair_inject step.simps)
next
  case (EndNodes nid merge i phis inputs m vs m' h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps is_sequential_node.simps 
    by (metis is_EndNode.elims(2) is_LoopEndNode_def)
  have notif: "\<not>(is_IfNode (kind g nid))"
    using EndNodes.hyps(1)
    by (metis is_AbstractEndNode.elims(1) is_EndNode.simps(12) is_IfNode_def IRNode.distinct_disc(900))
  have notref: "\<not>(is_RefNode (kind g nid))"
    using EndNodes.hyps(1) is_sequential_node.simps
    using IRNode.disc(1899) IRNode.distinct(1473) is_AbstractEndNode.simps is_EndNode.elims(2) is_LoopEndNode_def is_RefNode_def
    by (metis IRNode.distinct(737) IRNode.distinct_disc(1518))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps
    using IRNode.distinct_disc(1442) is_EndNode.simps(29) is_NewInstanceNode_def
    by (metis IRNode.distinct_disc(1483))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps
    by (metis IRNode.disc(939) is_EndNode.simps(19) is_LoadFieldNode_def)
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps
    using IRNode.distinct_disc(1504) is_EndNode.simps(39) is_StoreFieldNode_def 
    by fastforce
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps is_SignedDivNode_def is_SignedRemNode_def
    using IRNode.distinct_disc(1498) IRNode.distinct_disc(1500) is_IntegerDivRemNode.simps is_EndNode.simps(36) is_EndNode.simps(37) 
    by auto
  from notseq notif notref notnew notload notstore notdivrem
  show ?case using EndNodes evalAllDet
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
    by (smt (z3) IRNode.discI(11) IRNode.discI(18) IRNode.discI(38) IRNode.distinct(1777) IRNode.distinct(1779) IRNode.distinct(1797) IRNode.inject(28) Pair_inject)
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
  show ?case using LoadFieldNode step.cases
    by (smt (z3) IRNode.distinct(1333) IRNode.distinct(1347) IRNode.distinct(1349) IRNode.distinct(1353) IRNode.distinct(1367) IRNode.distinct(893) IRNode.inject(18) Pair_inject Value.inject(3) evalDet option.distinct(1) option.inject)
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
    by (smt (z3) IRNode.distinct(1333) IRNode.distinct(1347) IRNode.distinct(1349) IRNode.distinct(1353) IRNode.distinct(1367) IRNode.distinct(893) IRNode.distinct(1297) IRNode.distinct(1315) IRNode.distinct(1329) IRNode.distinct(871) IRNode.inject(18) Pair_inject option.discI)
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
  show ?case using StoreFieldNode step.cases
    by (smt (z3) IRNode.distinct(1353) IRNode.distinct(1783) IRNode.distinct(1965) IRNode.distinct(1983) IRNode.distinct(2027) IRNode.distinct(933) IRNode.distinct(1315) IRNode.distinct(1725) IRNode.distinct(1937) IRNode.distinct(909) IRNode.inject(38) Pair_inject Value.inject(3) evalDet option.distinct(1) option.inject)
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
  show ?case using StoreFieldNode step.cases
    by (smt (z3) IRNode.distinct(1315) IRNode.distinct(1353) IRNode.distinct(1783) IRNode.distinct(1965) 
        IRNode.distinct(1983) IRNode.distinct(2027) IRNode.distinct(933) IRNode.inject(38) IRNode.distinct(1725) Pair_inject StaticStoreFieldNode.hyps(1) StaticStoreFieldNode.hyps(2) StaticStoreFieldNode.hyps(3) StaticStoreFieldNode.hyps(4) evalDet option.discI)
next
  case (SignedDivNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps is_AbstractMergeNode.simps
    by (simp add: SignedDivNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using is_AbstractEndNode.simps
    by (simp add: SignedDivNode.hyps(1))
  from notseq notend
  show ?case using SignedDivNode step.cases
    by (smt (z3) IRNode.distinct(1347) IRNode.distinct(1777) IRNode.distinct(1961) IRNode.distinct(1965) IRNode.distinct(1979) IRNode.distinct(927) IRNode.inject(35) Pair_inject evalDet) 
next
  case (SignedRemNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps is_AbstractMergeNode.simps
    by (simp add: SignedRemNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using is_AbstractEndNode.simps
    by (simp add: SignedRemNode.hyps(1))
  from notseq notend
  show ?case using SignedRemNode step.cases
    by (smt (z3) IRNode.distinct(1349) IRNode.distinct(1779) IRNode.distinct(1961) IRNode.distinct(1983) IRNode.distinct(1997) IRNode.distinct(929) IRNode.inject(36) Pair_inject evalDet)
qed

lemma stepRefNode:
  "\<lbrakk>kind g nid = RefNode nid'\<rbrakk> \<Longrightarrow> g, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)"
  by (simp add: SequentialNode)

lemma IfNodeStepCases: 
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g \<turnstile> cond \<triangleright> condE"
  assumes "[m, p] \<turnstile> condE \<mapsto> v"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "nid' \<in> {tb, fb}"
  using step.IfNode
  by (metis assms(1) assms(2) assms(3) insert_iff prod.inject stepDet)

lemma IfNodeSeq:
  shows "kind g nid = IfNode cond tb fb \<longrightarrow> \<not>(is_sequential_node (kind g nid))"
  unfolding is_sequential_node.simps by simp

lemma IfNodeCond:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "\<exists> v. ((g \<turnstile> cond \<triangleright> condE) \<and> ([m, p] \<turnstile> condE \<mapsto> v))"
  using assms(2,1) by (induct "(nid,m,h)" "(nid',m,h)" rule: step.induct; auto)

lemma step_in_ids:
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')"
  shows "nid \<in> ids g"
  using assms apply (induct "(nid, m, h)" "(nid', m', h')" rule: step.induct)
  using is_sequential_node.simps(45) not_in_g 
  apply simp
  apply (metis is_sequential_node.simps(46))
  using ids_some apply (metis IRNode.simps(990))
  using EndNodes(1) is_AbstractEndNode.simps is_EndNode.simps(45) ids_some
  apply (metis IRNode.disc(965))
  by simp+


end