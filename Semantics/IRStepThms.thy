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
    by (metis is_IfNode_def SequentialNode.hyps(1) is_sequential_node.simps(22))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (metis is_AbstractEndNode.simps SequentialNode.hyps(1) is_sequential_node.simps(18,35)
        is_EndNode.elims(2) is_LoopEndNode_def)
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (metis is_NewInstanceNode_def SequentialNode.hyps(1) is_sequential_node.simps(41))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (metis is_LoadFieldNode_def SequentialNode.hyps(1) is_sequential_node.simps(33))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (metis is_StoreFieldNode_def SequentialNode.hyps(1) is_sequential_node.simps(53))
  have notdivrem:  "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (metis is_IntegerDivRemNode.simps SequentialNode.hyps(1) is_sequential_node.simps(51,52)
        is_SignedDivNode_def is_SignedRemNode_def)
  from notif notend notnew notload notstore notdivrem
  show ?case
    by (smt (verit) SequentialNode Pair_inject IRNode.disc(870,1614,3102) IRNode.discI(38)
        step.cases is_sequential_node.simps(12,14,20,40,51,52))
next
  case (FixedGuardNode nid cond before "next" condE m p val h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps by (simp add: FixedGuardNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: FixedGuardNode.hyps(1))
  from notseq notend 
  show ?case
    by (smt (verit) IRNode.distinct(373,703,1407,1431,1451,1453,1473,1475,1479) IRNode.inject(13)
        step.cases Pair_inject FixedGuardNode.hyps(1,5))
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
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  from notseq notif notref notnew notload notstore notdivrem notfixedguard notend notnewarray
  show ?case
    by (smt (verit) BytecodeExceptionNode.hyps IRNode.disc(1614,3102) IRNode.inject(7) repDet
        IRNode.discI(13,15,38) IRNode.distinct(359,751,773,775) Pair_inject step.cases)
next
  case (IfNode nid cond tb fb m val "next" h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (simp add: IfNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: IfNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: IfNode.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: IfNode.hyps(1))
  from notseq notend notdivrem notnewarray
  show ?case
    by (smt (verit) IRNode.inject(15) Pair_inject repDet evalDet IfNode.hyps step.cases
        IRNode.distinct(377,707,1407,1613,1633,1635,1655,1657,1661))
next
  case (EndNodes nid merge i phis inputs m vs m' h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (metis is_EndNode.elims(2) is_LoopEndNode_def is_sequential_node.simps(18,35)
        is_AbstractEndNode.simps EndNodes.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (metis IRNode.distinct_disc(1620) is_AbstractEndNode.elims(2) EndNodes.hyps(1) is_IfNode_def
        is_EndNode.simps(16))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (metis notseq is_RefNode_def is_sequential_node.simps(7))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (metis IRNode.distinct_disc(2746) is_EndNode.simps(39) is_NewInstanceNode_def
        is_AbstractEndNode.simps EndNodes.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (metis IRNode.distinct_disc(2544) is_EndNode.simps(28) is_LoadFieldNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (metis IRNode.distinct_disc(2772) is_EndNode.simps(52) is_StoreFieldNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    using EndNodes.hyps(1) is_SignedDivNode_def is_SignedRemNode_def by auto
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (metis IRNode.distinct_disc(1437) is_EndNode.simps(14) is_FixedGuardNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notbytecodeexception: "\<not>(is_BytecodeExceptionNode (kind g nid))"
    by (metis IRNode.distinct_disc(738) is_BytecodeExceptionNode_def is_AbstractEndNode.simps
        is_EndNode.simps(8) EndNodes.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (metis IRNode.distinct_disc(2743) is_EndNode.simps(38) is_NewArrayNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    by (metis IRNode.distinct_disc(407) is_EndNode.simps(5) is_ArrayLengthNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  from notseq notif notref notnew notload notstore notdivrem notfixedguard notbytecodeexception
       notnewarray notarraylength
  show ?case
    by (smt (verit) is_FixedGuardNode_def repAllDet evalAllDet is_IfNode_def EndNodes step.cases
        is_RefNode_def Pair_inject is_LoadFieldNode_def is_NewInstanceNode_def is_StoreFieldNode_def
        is_SignedDivNode_def is_SignedRemNode_def is_IntegerDivRemNode.elims(3) is_NewArrayNode_def
        is_BytecodeExceptionNode_def is_ArrayLengthNode_def)
next
  case (NewArrayNode nid len st n' lenE m length' arrayType h' ref h refNo h'')
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notbytecodeexception: "\<not>(is_BytecodeExceptionNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  from notseq notend notif notload notstore notfixedguard notbytecodeexception notarraylength notnew
  show ?case
    by (smt (verit) IRNode.discI(27) repDet evalDet Value.inject(2) IRNode.distinct(3131,3129)
        is_FixedGuardNode_def is_NewInstanceNode_def is_ArrayLengthNode_def is_IfNode_def
        is_BytecodeExceptionNode_def is_StoreFieldNode_def IRNode.inject EndNodes evalAllDet
        Pair_inject step.cases NewArrayNode)
next
  case (ArrayLengthNode nid x nid' xE m ref h arrayVal length' m')
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notbytecodeexception: "\<not>(is_BytecodeExceptionNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  from notseq notend notif  notstore notfixedguard notbytecodeexception notnew notnewarray
  show ?case
    by (smt (verit) IRNode.disc(211,221,232,233) Value.inject(2) ArrayLengthNode step.cases evalDet
        Pair_inject IRNode.inject is_StoreFieldNode_def is_BytecodeExceptionNode_def is_IfNode_def
        is_ArrayLengthNode_def is_NewInstanceNode_def is_FixedGuardNode_def is_NewArrayNode_def
        repDet)
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
  have notnewarray:  "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notarraylength:  "\<not>(is_ArrayLengthNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  from notseq notend notif notref notload notstore notdivrem notnewarray notarraylength
  show ?case
    by (smt (verit) NewInstanceNode step.cases IRNode.disc(1614,2234,3102) IRNode.discI(4,15)
        Pair_inject IRNode.distinct(753,1453,3173,3175) IRNode.inject(38))
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
    by (smt (verit) LoadFieldNode step.cases evalDet IRNode.inject(27) option.discI option.inject
        IRNode.distinct(401,731,1431,1613,2557,2559,2579,2581,2585) Pair_inject Value.inject(2)
        repDet)
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
    by (smt (verit) IRNode.distinct(401,731,1431,1613,2557,2559,2579,2581,2585) IRNode.inject(27)
        step.cases StaticLoadFieldNode Pair_inject option.distinct(1))
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
    by (smt (verit) IRNode.distinct(449,779,1479,1661,2585,3135,3179,3509,3531) IRNode.inject(51)
        step.cases StoreFieldNode evalDet option.discI Pair_inject Value.inject(2) option.inject
        repDet)
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
    by (smt (verit) IRNode.distinct(449,779,1479,1661,2585,3135,3179,3509,3531) IRNode.inject(51)
        step.cases StoreFieldNode StaticStoreFieldNode.hyps option.distinct(1) Pair_inject evalDet
        repDet)
next
  case (SignedDivNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: SignedDivNode.hyps(1))
  from notseq notend
  show ?case
    by (smt (verit) IRNode.distinct(443,773,1473,1655,2579,3129,3173,3505,3509) IRNode.inject(48)
        step.cases SignedDivNode repDet evalDet Pair_inject)
next
  case (SignedRemNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  from notseq notend
  show ?case
    by (smt (verit) IRNode.distinct(445,775,1475,1657,2581,3131,3175,3505,3531) IRNode.inject(49)
        step.cases SignedRemNode repDet evalDet Pair_inject)
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
  by (metis IRNode.distinct(465,795,1495,1677,2601,3151,3195,3547,3525,3585) IRNode.disc(1829)
      is_EndNode.simps(60) is_AbstractEndNode.simps not_in_g)+

end
