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

inductive_cases StepE[elim]:\<^marker>\<open>tag invisible\<close>
  "g, p \<turnstile> state \<rightarrow> val"

(*
definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "[+]" 60)
  where "A [+] B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"

lemma xor_false [simp]:
  "A [+] False = A"
  by (simp add: xor_def)

(*lemma xor_true [simp]:
  "(A [+] B [+] True) = ((A [+] True) \<and> (\<not>B))"
  by (simp add: xor_def)*)

lemma xor_resolve_true [simp]:
  "False [+] True = True"
  by (simp add: xor_def)

lemma xor_unfold [simp]:
  "A [+] (B [+] C) = A [+] B [+] C"
  using xor_def by force

definition control_nodes :: "(IRNode \<Rightarrow> bool) list" where
  "control_nodes = 
    [is_sequential_node,
    is_FixedGuardNode,
    is_BytecodeExceptionNode,
    is_IfNode,
    is_AbstractEndNode,
    is_NewArrayNode,
    is_ArrayLengthNode,
    is_LoadIndexedNode,
    is_StoreIndexedNode,
    is_NewInstanceNode,
    is_SignedDivNode,
    is_SignedRemNode,
    is_LoadFieldNode,
    is_StoreFieldNode]"

definition is_control_flow :: "IRNode \<Rightarrow> bool" where
  "is_control_flow node = fold (\<or>) (map (\<lambda>f. f node) control_nodes) False"

definition control_flow_exclusive :: "IRNode \<Rightarrow> bool" where
  "control_flow_exclusive node = fold ([+]) (map (\<lambda>f. f node) control_nodes) False"


lemma exclusive_control:
  "is_control_flow n \<Longrightarrow> control_flow_exclusive n"
  unfolding is_control_flow_def control_flow_exclusive_def
  control_nodes_def apply simp
  by (cases n; simp)
*)

theorem stepDet':
   "(g, p \<turnstile> state \<rightarrow> next) \<Longrightarrow>
    (g, p \<turnstile> state \<rightarrow> next') \<Longrightarrow> next = next'"
proof (induction arbitrary: next' rule: "step.induct")
  case (SequentialNode nid nid' m h)
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (metis SequentialNode.hyps(1) is_AbstractEndNode.simps is_EndNode.elims(2) is_LoopEndNode_def is_sequential_node.simps(18) is_sequential_node.simps(36))
  from SequentialNode show ?case apply (elim StepE) using is_sequential_node.simps
                   apply blast
                  apply force apply force apply force
    using notend
    apply (metis (no_types, lifting) Pair_inject is_AbstractEndNode.simps)
    by force+
next
  case (FixedGuardNode nid cond before "next" condE m val nid' h)
  then show ?case apply (elim StepE)
    by force+
next
  case (BytecodeExceptionNode nid args st nid' exceptionType h' ref h m' m)
  then show ?case apply (elim StepE)
    by force+
next
  case (IfNode nid cond tb fb condE m val nid' h)
  then show ?case apply (elim StepE)
    apply force+
    \<comment> \<open>IfNode rule uses expression evaluation\<close>
    using evalDet repDet apply fastforce
    by force+
next
  case (EndNodes nid merge i phis inps inpsE m vs m' h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    using EndNodes
    by (metis is_AbstractEndNode.simps is_EndNode.elims(2) is_LoopEndNode_def is_sequential_node.simps(18) is_sequential_node.simps(36))
  from EndNodes show ?case apply (elim StepE)
    using notseq apply force
                  apply force apply force apply force
    using indexof_det 
    unfolding is_AbstractEndNode.simps
    is_AbstractMergeNode.simps any_usage.simps usages.simps inputs.simps ids_def
    sorry
next
  case (NewArrayNode nid len st nid' lenE m length' arrayType h' ref h refNo h'' m')
  then show ?case apply (elim StepE) apply force+
  \<comment> \<open>NewArrayNode rule uses expression evaluation\<close>
  using evalDet repDet apply fastforce
  by force+
next
  case (ArrayLengthNode nid x nid' xE m ref h arrayVal length' m')
  then show ?case apply (elim StepE) apply force+
  \<comment> \<open>ArrayLengthNode rule uses expression evaluation\<close>
  using evalDet repDet apply fastforce
  by force+
next             
  case (LoadIndexedNode nid index guard array nid' indexE m indexVal arrayE ref h arrayVal loaded m')
  then show ?case apply (elim StepE) apply force+
  \<comment> \<open>LoadIndexedNode rule uses expression evaluation\<close>
  using evalDet repDet
  apply (metis IRNode.inject(28) Pair_inject Value.inject(2))
  by force+
next
  case (StoreIndexedNode nid check val st index guard array nid' indexE m indexVal arrayE ref valE "value" h arrayVal updated h' m')
  then show ?case apply (elim StepE) apply force+
  \<comment> \<open>StoreIndexedNode rule uses expression evaluation\<close>
    using evalDet repDet
    apply (metis IRNode.inject(55) Pair_inject Value.inject(2))
  by force+
next
  case (NewInstanceNode nid cname obj nid' h' ref h m' m)
  then show ?case apply (elim StepE) by force+
next
  case (LoadFieldNode nid f obj nid' objE m ref h v m')
  then show ?case apply (elim StepE) apply force+
  \<comment> \<open>LoadFieldNode rule uses expression evaluation\<close>
    using evalDet repDet apply fastforce
  by force+
next
  case (SignedDivNode nid x y zero sb nxt xe ye m v1 v2 v m' h)
  then show ?case apply (elim StepE) apply force+
  \<comment> \<open>SignedDivNode rule uses expression evaluation\<close>
    using evalDet repDet
    apply (metis IRNode.inject(49) Pair_inject)
  by force+
next
  case (SignedRemNode nid x y zero sb nxt xe ye m v1 v2 v m' h)
  then show ?case apply (elim StepE) apply force+
  \<comment> \<open>SignedRemNode rule uses expression evaluation\<close>
    using evalDet repDet
    apply (metis IRNode.inject(52) Pair_inject)
  by force+
next
  case (StaticLoadFieldNode nid f nid' h v m' m)
  then show ?case apply (elim StepE) by force+
next
  case (StoreFieldNode nid f newval uu obj nid' newvalE objE m val ref h' h m')
  then show ?case apply (elim StepE) apply force+
  \<comment> \<open>StoreFieldNode rule uses expression evaluation\<close>
    using evalDet repDet
    apply (metis IRNode.inject(54) Pair_inject Value.inject(2) option.inject)
  by force+
next
  case (StaticStoreFieldNode nid f newval uv nid' newvalE m val h' h m')
  then show ?case apply (elim StepE) apply force+
  \<comment> \<open>StaticStoreFieldNode rule uses expression evaluation\<close>
    using evalDet repDet by fastforce
qed

theorem stepDet:
   "(g, p \<turnstile> (nid,m,h) \<rightarrow> next) \<Longrightarrow>
   (\<forall> next'. ((g, p \<turnstile> (nid,m,h) \<rightarrow> next') \<longrightarrow> next = next'))"
  using stepDet' by simp

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
                prefer 4 prefer 14 defer defer
  using IRNode.distinct(1607) ids_some apply presburger
  using IRNode.distinct(851) ids_some apply presburger
  
  using IRNode.distinct(1805) ids_some apply presburger
             apply (metis IRNode.distinct(3507) not_in_g)
  apply (metis IRNode.distinct(497) not_in_g)
  apply (metis IRNode.distinct(2897) not_in_g)

  apply (metis IRNode.distinct(4085) not_in_g)
  using IRNode.distinct(3557) ids_some apply presburger
  apply (metis IRNode.distinct(2825) not_in_g)
  apply (metis IRNode.distinct(3947) not_in_g)
      apply (metis IRNode.distinct(4025) not_in_g)
  using IRNode.distinct(2825) ids_some apply presburger
  apply (metis IRNode.distinct(4067) not_in_g)
   apply (metis IRNode.distinct(4067) not_in_g)
  using IRNode.disc(1952) is_EndNode.simps(62) is_AbstractEndNode.simps not_in_g
  by (metis IRNode.disc(2014) is_EndNode.simps(64))

end
