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
    by (smt (verit) IRNode.disc(1102) IRNode.disc(2367) IRNode.discI(32) Pair_inject is_sequential_node.simps(17) is_sequential_node.simps(19) is_sequential_node.simps(44) is_sequential_node.simps(45))
next
  case (FixedGuardNode nid cond before "next" condE m p val h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps is_AbstractMergeNode.simps
    by presburger
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    using is_AbstractEndNode.simps
    by (simp add: FixedGuardNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))" 
    using is_AbstractEndNode.simps is_SignedDivNode_def is_SignedRemNode_def
    using FixedGuardNode.hyps(1) IRNode.disc(2171) IRNode.disc(2225) is_IntegerDivRemNode.simps by presburger
  from notseq notend notdivrem
  show ?case
    by (smt (verit) FixedGuardNode.hyps(1) FixedGuardNode.hyps(5) IRNode.distinct(1013) IRNode.distinct(1031) IRNode.distinct(1033) IRNode.distinct(1037) IRNode.distinct(973) IRNode.distinct(991) IRNode.inject(10) Pair_inject step.simps) 
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
  from notseq notend notdivrem show ?case
    by (smt (z3) IRNode.distinct IRNode.inject(12) Pair_inject step.simps IfNode repDet evalDet IRNode.distinct IRNode.inject(11) Pair_inject step.simps)
next
  case (EndNodes nid merge i phis inputs m vs m' h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps is_sequential_node.simps 
    by (metis is_EndNode.elims(2) is_LoopEndNode_def)
  have notif: "\<not>(is_IfNode (kind g nid))"
    using EndNodes.hyps(1) is_IfNode_def is_AbstractEndNode.elims
    by (metis IRNode.distinct_disc(1164) is_EndNode.simps(13))
  have notref: "\<not>(is_RefNode (kind g nid))"
    using EndNodes.hyps(1) is_sequential_node.simps
    using IRNode.disc(1899) IRNode.distinct(1473) is_AbstractEndNode.simps is_EndNode.elims(2) is_LoopEndNode_def is_RefNode_def
    by metis
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps
    using IRNode.distinct_disc(1442) is_EndNode.simps(29) is_NewInstanceNode_def
    by (metis IRNode.distinct_disc(2008) is_EndNode.simps(33))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps
    using is_LoadFieldNode_def
    by (metis IRNode.distinct_disc(1812) is_EndNode.simps(22))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps is_StoreFieldNode_def
    by (metis IRNode.distinct_disc(2032) is_EndNode.simps(45))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps is_SignedDivNode_def is_SignedRemNode_def
    using IRNode.distinct_disc(1498) IRNode.distinct_disc(1500) is_IntegerDivRemNode.simps is_EndNode.simps(36) is_EndNode.simps(37) 
    by auto
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    using EndNodes.hyps(1) is_AbstractEndNode.simps is_FixedGuardNode_def
    by (metis IRNode.distinct_disc(997) is_EndNode.simps(11))
  from notseq notif notref notnew notload notstore notdivrem notfixedguard
  show ?case 
    by (smt (verit) EndNodes repAllDet evalAllDet IRNode.disc(497) is_IfNode_def is_LoadFieldNode_def is_NewInstanceNode_def is_RefNode_def is_StoreFieldNode_def is_SignedDivNode_def is_SignedRemNode_def  Pair_inject is_IntegerDivRemNode.elims(3) step.cases)
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
    by (smt (verit) IRNode.disc(1102) IRNode.disc(2367) IRNode.discI(12) IRNode.distinct(1013) IRNode.distinct(2417) IRNode.distinct(2419) IRNode.inject(32) Pair_inject)
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
    by (smt (verit) IRNode.distinct(1157) IRNode.distinct(1827) IRNode.distinct(1845) IRNode.distinct(1847) IRNode.distinct(1851) IRNode.distinct(991) IRNode.inject(21) Pair_inject Value.inject(2) option.distinct(1) option.inject)
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
    by (smt (verit) IRNode.distinct(1157) IRNode.distinct(1827) IRNode.distinct(1845) IRNode.distinct(1847) IRNode.distinct(1851) IRNode.distinct(991) IRNode.inject(21) Pair_inject option.distinct(1))
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
    by (smt (verit) IRNode.distinct(1037) IRNode.distinct(1203) IRNode.distinct(1851) IRNode.distinct(2423) IRNode.distinct(2711) IRNode.distinct(2733) IRNode.inject(44) Pair_inject Value.inject(2) option.distinct(1) option.inject)
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
    by (smt (verit) IRNode.distinct(1037) IRNode.distinct(1203) IRNode.distinct(1851) IRNode.distinct(2423) IRNode.distinct(2711) IRNode.distinct(2733) IRNode.inject(44) Pair_inject StaticStoreFieldNode.hyps(1) StaticStoreFieldNode.hyps(2) StaticStoreFieldNode.hyps(3) StaticStoreFieldNode.hyps(4) StaticStoreFieldNode.hyps(5) option.distinct(1))
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
    by (smt (verit) IRNode.distinct(1031) IRNode.distinct(1197) IRNode.distinct(1845) IRNode.distinct(2417) IRNode.distinct(2707) IRNode.distinct(2711) IRNode.inject(41) Pair_inject)
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
    by (smt (verit) IRNode.distinct(1033) IRNode.distinct(1199) IRNode.distinct(1847) IRNode.distinct(2419) IRNode.distinct(2707) IRNode.distinct(2733) IRNode.inject(42) Pair_inject)
qed

lemma stepRefNode:
  "\<lbrakk>kind g nid = RefNode nid'\<rbrakk> \<Longrightarrow> g, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)"
  using SequentialNode
  by (metis IRNodes.successors_of_RefNode is_sequential_node.simps(7) nth_Cons_0)

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
  unfolding is_sequential_node.simps
  using is_sequential_node.simps(18)
  using is_sequential_node.simps(19) by presburger
  
lemma IfNodeCond:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "\<exists> condE v. ((g \<turnstile> cond \<simeq> condE) \<and> ([m, p] \<turnstile> condE \<mapsto> v))"
  using assms(2,1) by (induct "(nid,m,h)" "(nid',m,h)" rule: step.induct; auto)

lemma step_in_ids:
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')"
  shows "nid \<in> ids g"
  using assms apply (induct "(nid, m, h)" "(nid', m', h')" rule: step.induct)
  apply fastforce
  using IRNode.distinct(1053) IRNode.distinct(1219) ids_some apply presburger+
  apply (metis IRNode.distinct_disc(2047) is_EndNode.simps(53) ids_some is_AbstractEndNode.simps)
  by simp+

end
