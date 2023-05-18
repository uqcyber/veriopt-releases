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
    by (metis is_IfNode_def SequentialNode.hyps(1) is_sequential_node.simps(20))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (metis is_AbstractEndNode.simps SequentialNode.hyps(1) is_sequential_node.simps(16,31)
        is_EndNode.elims(2) is_LoopEndNode_def)
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (metis is_NewInstanceNode_def SequentialNode.hyps(1) is_sequential_node.simps(37))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (metis is_LoadFieldNode_def SequentialNode.hyps(1) is_sequential_node.simps(29))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (metis is_StoreFieldNode_def SequentialNode.hyps(1) is_sequential_node.simps(48))
  have notdivrem:  "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (metis is_IntegerDivRemNode.simps SequentialNode.hyps(1) is_sequential_node.simps(46,47)
        is_SignedDivNode_def is_SignedRemNode_def)
  from notif notend notnew notload notstore notdivrem
  show ?case
    by (smt (verit) SequentialNode step.cases is_sequential_node.simps(12,18,46,47) Pair_inject
        IRNode.discI(34) IRNode.disc(686,1256,2567))
next
  case (FixedGuardNode nid cond before "next" condE m p val h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps by (simp add: FixedGuardNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: FixedGuardNode.hyps(1))
  from notseq notend 
  show ?case
    by (smt (verit) FixedGuardNode.hyps(1,5) IRNode.distinct(441,1103,1123,1145,1163,1165,1169)
        step.cases Pair_inject IRNode.inject(11))
next
  case (IfNode nid cond tb fb m val "next" h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (simp add: IfNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: IfNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))" 
    by (simp add: IfNode.hyps(1))
  from notseq notend notdivrem
  show ?case
    by (smt (verit) IRNode.inject(13) Pair_inject repDet evalDet IfNode.hyps(1,2,3,4) step.cases
        IRNode.distinct(445,1103,1293,1315,1333,1335,1339))
next
  case (BytecodeExceptionNode nid args st n' ex h' ref h m' m)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (metis notseq is_RefNode_def is_sequential_node.simps(7))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  from notseq notif notref notnew notload notstore notdivrem notfixedguard notend
  show ?case
    by (smt (verit) BytecodeExceptionNode.hyps(1,2,3,4) IRNode.disc(572,1256,2567) IRNode.inject(5)
        IRNode.discI(13,34) IRNode.distinct(505,507) Pair_inject step.cases repDet)
next
  case (EndNodes nid merge i phis inputs m vs m' h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (metis is_EndNode.elims(2) is_LoopEndNode_def is_sequential_node.simps(16,31)
        is_AbstractEndNode.simps EndNodes.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (metis IRNode.distinct_disc(1300) is_AbstractEndNode.elims(2) EndNodes.hyps(1) is_IfNode_def
        is_EndNode.simps(14))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (metis notseq is_RefNode_def is_sequential_node.simps(7))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (metis IRNode.distinct_disc(2226) is_EndNode.simps(35) is_NewInstanceNode_def
        is_AbstractEndNode.simps EndNodes.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (metis IRNode.distinct_disc(2029) is_EndNode.simps(24) is_LoadFieldNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (metis IRNode.distinct_disc(2250) is_EndNode.simps(47) is_StoreFieldNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    using EndNodes.hyps(1) is_SignedDivNode_def is_SignedRemNode_def by auto
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (metis IRNode.distinct_disc(1130) is_EndNode.simps(12) is_FixedGuardNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notbytecodeexception: "\<not>(is_BytecodeExceptionNode (kind g nid))"
    by (metis IRNode.distinct_disc(472) is_BytecodeExceptionNode_def is_AbstractEndNode.simps
        is_EndNode.simps(6) EndNodes.hyps(1))
  from notseq notif notref notnew notload notstore notdivrem notfixedguard notbytecodeexception
  show ?case
    by (smt (verit) IRNode.disc(497,572) repAllDet evalAllDet is_IfNode_def EndNodes step.cases
        is_RefNode_def Pair_inject is_LoadFieldNode_def is_NewInstanceNode_def is_StoreFieldNode_def
        is_SignedDivNode_def is_SignedRemNode_def is_IntegerDivRemNode.elims(3)
        is_BytecodeExceptionNode_def)
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
    by (smt (verit) NewInstanceNode step.cases IRNode.disc(1102,1013,1256,2367,2417,2419,2466)
        IRNode.discI(13,46) Pair_inject IRNode.distinct(487,1145,2635,2637) IRNode.inject(33,34))
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
    by (smt (verit) LoadFieldNode step.cases repDet evalDet IRNode.inject(23) option.discI
        IRNode.distinct(465,1123,1293,2045,2063,2065,2069) Pair_inject Value.inject(2) 
        option.inject)
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
    by (smt (verit) IRNode.distinct(465,1123,1293,2045,2063,2065,2069) IRNode.inject(23) step.cases
        StaticLoadFieldNode Pair_inject option.distinct(1))
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
    by (smt (verit) IRNode.distinct(511,1169,1339,2069,2641,2929,2951) IRNode.inject(46) step.cases
        StoreFieldNode repDet evalDet option.discI Pair_inject Value.inject(2) option.inject)
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
    by (smt (verit) IRNode.distinct(511,1169,1339,2069,2641,2929,2951) IRNode.inject(46) step.cases
        StoreFieldNode repDet StaticStoreFieldNode.hyps(1,2,3,4,5) option.distinct(1) Pair_inject
        evalDet)
next
  case (SignedDivNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: SignedDivNode.hyps(1))
  from notseq notend
  show ?case
    by (smt (verit) IRNode.distinct(505,1163,1333,2063,2635,2925,2929) IRNode.inject(43) step.cases
        SignedDivNode repDet evalDet Pair_inject)
next
  case (SignedRemNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  from notseq notend
  show ?case
    by (smt (verit) IRNode.distinct(507,1165,1335,2065,2637,2925,2951) IRNode.inject(44) step.cases
        SignedRemNode repDet evalDet Pair_inject)
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
  by (metis IRNode.distinct(527,1185,1355,2085,2657,2945,2967,3005) IRNode.disc(1455) ids_some
      is_EndNode.simps(55) is_AbstractEndNode.simps not_in_g)+

end
