subsection \<open>Control-flow Semantics Theorems\<close>

theory IRStepThms
  imports
    IRStepObj
    TreeToGraphThms
begin

text \<open>
We prove that within the same graph, a configuration triple will always
transition to the same subsequent configuration. Therefore, our step semantics
is deterministic.
\<close>

(*
definition stepping_nodes :: "(IRNode \<Rightarrow> bool) set" where
  "stepping_nodes = {
    is_sequential_node,
    is_IfNode,
    is_AbstractEndNode,
    is_NewInstanceNode,
    is_LoadFieldNode,
    is_SignedDivNode,
    is_SignedRemNode,
    is_LoadFieldNode,
    is_StoreFieldNode
  }"

inductive_cases StepE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g, p \<turnstile> (nid,m,h) \<rightarrow> next"

lemma stepping_nodes_distinct:
  assumes "sel \<in> stepping_nodes \<and> sel node"
  shows "\<forall> oth \<in> stepping_nodes - {sel} . \<not>(oth node)"
  using assms unfolding stepping_nodes_def sorry


proof (induction arbitrary: m h rule: step.induct)
  case (SequentialNode nid nid')
  have "is_sequential_node \<in> stepping_nodes" unfolding stepping_nodes_def by simp
  then have distinct: "\<forall> oth \<in> stepping_nodes - {is_sequential_node} . \<not>(oth (kind g nid))"
    using stepping_nodes_distinct SequentialNode(1) by auto
  obtain next' where "g, p \<turnstile> (nid, m, h) \<rightarrow> next'"
    using SequentialNode.hyps(1) step.SequentialNode
    by blast
  then have "next' = (nid', m, h)"
    apply (induct rule: step.induct) using SequentialNode sorry
  show ?case apply (rule allI) (*using step.cases*) apply (induction rule: step.induct)
    using distinct unfolding stepping_nodes_def
    using is_IfNode_def is_NewInstanceNode_def is_LoadFieldNode_def is_SignedDivNode_def is_SignedRemNode_def
    is_LoadFieldNode_def is_StoreFieldNode_def 
    apply (rule stepping_nodes_distinct [where sel = is_sequential_node, where node = "kind g nid"])
  then show ?case apply (rule stepping_nodes_distinct [where sel = is_sequential_node, where node = "kind g nid"])?
next
  case (IfNode nid cond tb fb condE m val nid' h)
  then show ?case sorry
next
  case (EndNodes nid merge i phis inps inpsE m vs m' h)
  then show ?case sorry
next
  case (NewInstanceNode nid f obj nid' h' ref h m' m)
  then show ?case sorry
next
  case (LoadFieldNode nid f obj nid' objE m ref h v m')
  then show ?case sorry
next
  case (SignedDivNode nid x y zero sb nxt xe ye m v1 v2 v m' h)
  then show ?case sorry
next
  case (SignedRemNode nid x y zero sb nxt xe ye m v1 v2 v m' h)
  then show ?case sorry
next
  case (StaticLoadFieldNode nid f nid' h v m' m)
  then show ?case sorry
next
  case (StoreFieldNode nid f newval uu obj nid' newvalE objE m val ref h' h m')
  then show ?case sorry
next
  case (StaticStoreFieldNode nid f newval uv nid' newvalE m val h' h m')
  then show ?case sorry
qed
*)

subsubsection \<open>Control-flow Step is Deterministic\<close>

theorem stepDet:
   "(g, p \<turnstile> (nid,m,h) \<rightarrow> next) \<Longrightarrow>
   (\<forall> next'. ((g, p \<turnstile> (nid,m,h) \<rightarrow> next') \<longrightarrow> next = next'))"
proof (induction rule: "step.induct")
  case (SequentialNode nid "next" m h)
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (metis is_IfNode_def SequentialNode.hyps(1) is_sequential_node.simps(19))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (metis is_AbstractEndNode.simps SequentialNode.hyps(1) is_sequential_node.simps(15,29)
        is_EndNode.elims(2) is_LoopEndNode_def)
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (metis is_NewInstanceNode_def SequentialNode.hyps(1) is_sequential_node.simps(35))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (metis is_LoadFieldNode_def SequentialNode.hyps(1) is_sequential_node.simps(27))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (metis is_StoreFieldNode_def SequentialNode.hyps(1) is_sequential_node.simps(46))
  have notdivrem:  "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (metis is_IntegerDivRemNode.simps SequentialNode.hyps(1) is_sequential_node.simps(44,45) 
        is_SignedDivNode_def is_SignedRemNode_def)
  from notif notend notnew notload notstore notdivrem
  show ?case 
    by (smt (verit) SequentialNode step.cases IRNode.disc(1102,2367) IRNode.discI(32) Pair_inject
        is_sequential_node.simps(17,19,44,45))
next
  case (FixedGuardNode nid cond before "next" condE m p val h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps by (simp add: FixedGuardNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: FixedGuardNode.hyps(1))
  from notseq notend 
  show ?case 
    by (smt (verit) FixedGuardNode.hyps(1,5) IRNode.distinct(973,991,1013,1031,1033,1037) step.simps
        IRNode.inject(10) Pair_inject)
next
  case (IfNode nid cond tb fb m val "next" h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (simp add: IfNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: IfNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))" 
    by (simp add: IfNode.hyps(1))
  from notseq notend notdivrem show ?case
    by (smt (verit) IRNode.inject(11,12) Pair_inject step.simps IfNode repDet evalDet step.simps
        IRNode.distinct(973,1157,1179,1197,1199,1203))
next
  case (EndNodes nid merge i phis inputs m vs m' h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (metis is_EndNode.elims(2) is_LoopEndNode_def is_sequential_node.simps(15, 29) 
        is_AbstractEndNode.simps EndNodes.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (metis IRNode.distinct_disc(1164) is_AbstractEndNode.elims(2) EndNodes.hyps(1) is_IfNode_def
        is_EndNode.simps(13))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (metis EndNodes.hyps(1) is_AbstractEndNode.simps is_EndNode.elims(2) is_LoopEndNode_def 
        is_RefNode_def is_sequential_node.simps(7,15,29))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (metis IRNode.distinct_disc(2008) is_EndNode.simps(33) is_NewInstanceNode_def 
        is_AbstractEndNode.simps EndNodes.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (metis IRNode.distinct_disc(1812) is_EndNode.simps(22) is_LoadFieldNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (metis IRNode.distinct_disc(2032) is_EndNode.simps(45) is_StoreFieldNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    using EndNodes.hyps(1) is_SignedDivNode_def is_SignedRemNode_def by auto
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (metis IRNode.distinct_disc(997) is_EndNode.simps(11) is_FixedGuardNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  from notseq notif notref notnew notload notstore notdivrem notfixedguard
  show ?case 
    by (smt (verit) repAllDet evalAllDet IRNode.disc(497) is_IfNode_def is_RefNode_def Pair_inject
        is_LoadFieldNode_def is_NewInstanceNode_def is_StoreFieldNode_def step.cases EndNodes
        is_SignedDivNode_def is_SignedRemNode_def is_IntegerDivRemNode.elims(3))
next
  case (NewInstanceNode nid f obj nxt h' ref h m' m)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notdivrem:  "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  from notseq notend notif notref notload notstore notdivrem
  show ?case 
    by (smt (verit) NewInstanceNode step.cases IRNode.disc(1102, 2367) IRNode.discI(12) Pair_inject
        IRNode.distinct(1013,2417,2419) IRNode.inject(32))
next
  case (LoadFieldNode nid f obj nxt m ref h v m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: LoadFieldNode.hyps(1))
  have notdivrem:  "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: LoadFieldNode.hyps(1))
  from notseq notend notdivrem
  show ?case 
    by (smt (verit) LoadFieldNode step.cases repDet evalDet IRNode.inject(21) option.distinct(1)
        IRNode.distinct(991,1157,1827,1845,1847,1851) Pair_inject Value.inject(2) option.inject)
next
  case (StaticLoadFieldNode nid f nxt h v m' m)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: StaticLoadFieldNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: StaticLoadFieldNode.hyps(1))
  from notseq notend notdivrem
  show ?case  
    by (smt (verit) StaticLoadFieldNode step.cases IRNode.inject(21) Pair_inject option.distinct(1)
        IRNode.distinct(991,1157,1827,1845,1847,1851))
next
  case (StoreFieldNode nid f newval uu obj nxt m val ref h' h m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: StoreFieldNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: StoreFieldNode.hyps(1))
  from notseq notend notdivrem
  show ?case 
    by (smt (verit) StoreFieldNode step.cases repDet evalDet IRNode.inject(44) option.distinct(1)
        IRNode.distinct(1037,1203,1851,2423,2711,2733) Value.inject(2) Pair_inject option.inject)
next
  case (StaticStoreFieldNode nid f newval uv nxt m val h' h m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: StaticStoreFieldNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: StaticStoreFieldNode.hyps(1))
  from notseq notend notdivrem
  show ?case  
    by (smt (verit) StoreFieldNode repDet evalDet StaticStoreFieldNode.hyps(1,2,3,4,5) Pair_inject
        IRNode.distinct(1037,1203,1851,2423,2711,2733) IRNode.inject(44) option.distinct(1)
        step.cases)
next
  case (SignedDivNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: SignedDivNode.hyps(1))
  from notseq notend
  show ?case  
    by (smt (verit) SignedDivNode IRNode.distinct(1031,1197,1845,2417,2707,2711) IRNode.inject(41)
        step.cases repDet evalDet Pair_inject)
next
  case (SignedRemNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  from notseq notend
  show ?case 
    by (smt (verit) SignedRemNode IRNode.distinct(1033,1199,1847,2419,2707,2733) IRNode.inject(42)
        step.cases repDet evalDet Pair_inject)
qed

lemma stepRefNode:
  "\<lbrakk>kind g nid = RefNode nid'\<rbrakk> \<Longrightarrow> g, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)"
  by (metis IRNodes.successors_of_RefNode is_sequential_node.simps(7) nth_Cons_0 SequentialNode)

lemma IfNodeStepCases: 
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g \<turnstile> cond \<simeq> condE"
  assumes "[m, p] \<turnstile> condE \<mapsto> v"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "nid' \<in> {tb, fb}"
  by (metis insert_iff old.prod.inject step.IfNode stepDet assms)

lemma IfNodeSeq:
  shows "kind g nid = IfNode cond tb fb \<longrightarrow> \<not>(is_sequential_node (kind g nid))"
  using is_sequential_node.simps(18,19) by simp
  
lemma IfNodeCond:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "\<exists> condE v. ((g \<turnstile> cond \<simeq> condE) \<and> ([m, p] \<turnstile> condE \<mapsto> v))"
  using assms(2,1) by (induct "(nid,m,h)" "(nid',m,h)" rule: step.induct; auto)

lemma step_in_ids:
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')"
  shows "nid \<in> ids g"
  using assms apply (induct "(nid, m, h)" "(nid', m', h')" rule: step.induct) apply fastforce
  apply (smt (z3) IRNode.distinct(1053,1219) IRNode.distinct_disc(2047) is_EndNode.simps(53)
         is_AbstractEndNode.simps ids_some)+
  by auto

end
