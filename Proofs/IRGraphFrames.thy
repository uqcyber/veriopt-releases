subsection \<open>Dynamic Frames\<close>

text \<open>
This theory defines two operators, 'unchanged' and 'changeonly',
that are useful for specifying which nodes in an IRGraph can change.
The dynamic framing idea originates from 'Dynamic Frames' in software verification,
started by Ioannis T. Kassios in "Dynamic frames: Support for framing, 
dependencies and sharing without restrictions", In FM 2006.
\<close>

theory IRGraphFrames
  imports
    Form
    Semantics.IRTreeEval
begin

fun unchanged :: "ID set \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "unchanged ns g1 g2 = (\<forall> n . n \<in> ns \<longrightarrow> 
    (n \<in> ids g1 \<and> n \<in> ids g2 \<and> kind g1 n = kind g2 n \<and> stamp g1 n = stamp g2 n))"

(* This allows new nodes to be added to g2, but only ns can change. *)
fun changeonly :: "ID set \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "changeonly ns g1 g2 = (\<forall> n . n \<in> ids g1 \<and> n \<notin> ns \<longrightarrow> 
    (n \<in> ids g1 \<and> n \<in> ids g2 \<and> kind g1 n = kind g2 n \<and> stamp g1 n = stamp g2 n))"

lemma node_unchanged:
  assumes "unchanged ns g1 g2"
  assumes "nid \<in> ns"
  shows "kind g1 nid = kind g2 nid"
  using assms by auto

lemma other_node_unchanged:
  assumes "changeonly ns g1 g2"
  assumes "nid \<in> ids g1"
  assumes "nid \<notin> ns"
  shows "kind g1 nid = kind g2 nid"
  using assms
  using changeonly.simps by blast


text \<open>Some notation for input nodes used\<close>

(* Relates all the nodes used in an 'eval', including the node itself. *)
inductive eval_uses:: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool"
  for g where

  use0: "nid \<in> ids g
    \<Longrightarrow> eval_uses g nid nid" |

  use_inp: "nid' \<in> inputs g n
    \<Longrightarrow> eval_uses g nid nid'" |

  use_trans: "\<lbrakk>eval_uses g nid nid';
    eval_uses g nid' nid''\<rbrakk>
    \<Longrightarrow> eval_uses g nid nid''"


fun eval_usages :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "eval_usages g nid = {n \<in> ids g . eval_uses g nid n}"

lemma eval_usages_self:
  assumes "nid \<in> ids g"
  shows "nid \<in> eval_usages g nid"
  using assms eval_usages.simps eval_uses.intros(1)
  by (simp add: ids.rep_eq)

lemma not_in_g_inputs: 
  assumes "nid \<notin> ids g"
  shows "inputs g nid = {}"
proof -
  have k: "kind g nid = NoNode" using assms not_in_g by blast
  then show ?thesis by (simp add: k)
qed

lemma child_member:
  assumes "n = kind g nid"
  assumes "n \<noteq> NoNode"
  assumes "List.member (inputs_of n) child"
  shows "child \<in> inputs g nid"
  unfolding inputs.simps using assms
  by (metis in_set_member) 

lemma child_member_in:
  assumes "nid \<in> ids g"
  assumes "List.member (inputs_of (kind g nid)) child"
  shows "child \<in> inputs g nid"
  unfolding inputs.simps using assms
  by (metis child_member ids_some inputs.elims)


(* Node inputs are not necessarily in ids g (unless wf_graph g).
   But this is true because 'inp' is defined using 'kind'. *)
lemma inp_in_g: 
  assumes "n \<in> inputs g nid"
  shows "nid \<in> ids g"
proof -
  have "inputs g nid \<noteq> {}"
    using assms
    by (metis empty_iff empty_set)
  then have "kind g nid \<noteq> NoNode"
    using not_in_g_inputs
    using ids_some by blast
  then show ?thesis
    using not_in_g
    by metis
qed

lemma inp_in_g_wf:
  assumes "wf_graph g"
  assumes "n \<in> inputs g nid"
  shows "n \<in> ids g"
  using assms unfolding wf_folds
  using inp_in_g by blast


lemma kind_unchanged:
  assumes "nid \<in> ids g1"
  assumes "unchanged (eval_usages g1 nid) g1 g2"
  shows "kind g1 nid = kind g2 nid"
proof -
  show ?thesis
    using assms eval_usages_self
    using unchanged.simps by blast
qed

lemma stamp_unchanged:
  assumes "nid \<in> ids g1"
  assumes "unchanged (eval_usages g1 nid) g1 g2"
  shows "stamp g1 nid = stamp g2 nid"
  by (meson assms(1) assms(2) eval_usages_self unchanged.elims(2))
  

lemma child_unchanged:
  assumes "child \<in> inputs g1 nid"
  assumes "unchanged (eval_usages g1 nid) g1 g2"
  shows "unchanged (eval_usages g1 child) g1 g2"
  by (smt assms(1) assms(2) eval_usages.simps mem_Collect_eq
      unchanged.simps use_inp use_trans)

lemma eval_usages:
  assumes "us = eval_usages g nid"
  assumes "nid' \<in> ids g"
  shows "eval_uses g nid nid' \<longleftrightarrow> nid' \<in> us" (is "?P \<longleftrightarrow> ?Q")
  using assms eval_usages.simps
  by (simp add: ids.rep_eq)

lemma inputs_are_uses:
  assumes "nid' \<in> inputs g nid"
  shows "eval_uses g nid nid'"
  by (metis assms use_inp)

lemma inputs_are_usages:
  assumes "nid' \<in> inputs g nid"
  assumes "nid' \<in> ids g"
  shows "nid' \<in> eval_usages g nid"
  using assms(1) assms(2) eval_usages inputs_are_uses by blast

lemma inputs_of_are_usages:
  assumes "List.member (inputs_of (kind g nid)) nid'"
  assumes "nid' \<in> ids g"
  shows "nid' \<in> eval_usages g nid"
  by (metis assms(1) assms(2) in_set_member inputs.elims inputs_are_usages)

lemma usage_includes_inputs:
  assumes "us = eval_usages g nid"
  assumes "ls = inputs g nid"
  assumes "ls \<subseteq> ids g"
  shows "ls \<subseteq> us"
  using inputs_are_usages eval_usages
  using assms(1) assms(2) assms(3) by blast

lemma elim_inp_set:
  assumes "k = kind g nid"
  assumes "k \<noteq> NoNode"
  assumes "child \<in> set (inputs_of k)"
  shows "child \<in> inputs g nid"
  using assms by auto

lemma encode_in_ids:
  assumes "g \<turnstile> nid \<triangleright> e"
  shows "nid \<in> ids g"
  using assms
  apply (induction rule: rep.induct)
  apply simp+
  by fastforce

lemma eval_in_ids:
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  shows "nid \<in> ids g"
  using assms using encodeeval_def encode_in_ids
  by auto

lemma transitive_kind_same:
  assumes "unchanged (eval_usages g1 nid) g1 g2"
  shows "\<forall> nid' \<in> (eval_usages g1 nid) . kind g1 nid' = kind g2 nid'"
  using assms
  by (meson unchanged.elims(1))

theorem stay_same_encoding:
  assumes nc: "unchanged (eval_usages g1 nid) g1 g2"
  assumes g1: "g1 \<turnstile> nid \<triangleright> e"
  assumes wf: "wf_graph g1"
  shows "g2 \<turnstile> nid \<triangleright> e"
proof -
  have dom: "nid \<in> ids g1"
    using g1 encode_in_ids by simp
  show ?thesis 
using g1 nc wf dom proof (induction e rule: rep.induct)
  case (ConstantNode n c)
  then have "kind g2 n = ConstantNode c"
    using dom nc kind_unchanged
    by metis
  then show ?case using rep.ConstantNode
    by presburger
next
  case (ParameterNode n i s)
  then have "kind g2 n = ParameterNode i"
    by (metis kind_unchanged)
  then show ?case
    by (metis ParameterNode.hyps(2) ParameterNode.prems(1) ParameterNode.prems(3) rep.ParameterNode stamp_unchanged)
next
  case (ConditionalNode n c t f ce te fe)
  then have "kind g2 n = ConditionalNode c t f"
    by (metis kind_unchanged)
  have "c \<in> eval_usages g1 n \<and> t \<in> eval_usages g1 n \<and> f \<in> eval_usages g1 n"
    using inputs_of_ConditionalNode
    by (metis ConditionalNode.hyps(1) ConditionalNode.hyps(2) ConditionalNode.hyps(3) ConditionalNode.hyps(4) encode_in_ids inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons subset_code(1))
  then show ?case using transitive_kind_same
    by (metis ConditionalNode.hyps(1) ConditionalNode.prems(1) IRNodes.inputs_of_ConditionalNode \<open>kind g2 n = ConditionalNode c t f\<close> child_unchanged inputs.simps list.set_intros(1) local.ConditionalNode(5) local.ConditionalNode(6) local.ConditionalNode(7) local.ConditionalNode(9) rep.ConditionalNode set_subset_Cons subset_code(1) unchanged.elims(2))
next
  case (AbsNode n x xe)
  then have "kind g2 n = AbsNode x"
    using kind_unchanged
    by metis
  then have "x \<in> eval_usages g1 n"
    using inputs_of_AbsNode
    by (metis AbsNode.hyps(1) AbsNode.hyps(2) encode_in_ids inputs.simps inputs_are_usages list.set_intros(1))
  then show ?case
    by (metis AbsNode.IH AbsNode.hyps(1) AbsNode.prems(1) AbsNode.prems(3) IRNodes.inputs_of_AbsNode \<open>kind g2 n = AbsNode x\<close> child_member_in child_unchanged local.wf member_rec(1) rep.AbsNode unchanged.simps)
next
  case (NotNode n x xe)
  then have "kind g2 n = NotNode x"
    using kind_unchanged
    by metis
  then have "x \<in> eval_usages g1 n"
    using inputs_of_NotNode
    by (metis NotNode.hyps(1) NotNode.hyps(2) encode_in_ids inputs.simps inputs_are_usages list.set_intros(1))
  then show ?case
    by (metis NotNode.IH NotNode.hyps(1) NotNode.prems(1) NotNode.prems(3) IRNodes.inputs_of_NotNode \<open>kind g2 n = NotNode x\<close> child_member_in child_unchanged local.wf member_rec(1) rep.NotNode unchanged.simps)
next
  case (NegateNode n x xe)
  then have "kind g2 n = NegateNode x"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n"
    using inputs_of_NegateNode
    by (metis NegateNode.hyps(1) NegateNode.hyps(2) encode_in_ids inputs.simps inputs_are_usages list.set_intros(1))
  then show ?case
    by (metis IRNodes.inputs_of_NegateNode NegateNode.IH NegateNode.hyps(1) NegateNode.prems(1) NegateNode.prems(3) \<open>kind g2 n = NegateNode x\<close> child_member_in child_unchanged local.wf member_rec(1) rep.NegateNode unchanged.elims(1))
next
  case (LogicNegationNode n x xe)
  then have "kind g2 n = LogicNegationNode x"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n"
    using inputs_of_LogicNegationNode inputs_of_are_usages
    by (metis LogicNegationNode.hyps(1) LogicNegationNode.hyps(2) encode_in_ids member_rec(1))
  then show ?case
    by (metis IRNodes.inputs_of_LogicNegationNode LogicNegationNode.IH LogicNegationNode.hyps(1) LogicNegationNode.hyps(2) LogicNegationNode.prems(1) \<open>kind g2 n = LogicNegationNode x\<close> child_unchanged encode_in_ids inputs.simps list.set_intros(1) local.wf rep.LogicNegationNode)
next
  case (AddNode n x y xe ye)
  then have "kind g2 n = AddNode x y"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    using inputs_of_LogicNegationNode inputs_of_are_usages
    by (metis AddNode.hyps(1) AddNode.hyps(2) AddNode.hyps(3) IRNodes.inputs_of_AddNode encode_in_ids in_mono inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case
    by (metis AddNode.IH(1) AddNode.IH(2) AddNode.hyps(1) AddNode.hyps(2) AddNode.hyps(3) AddNode.prems(1) IRNodes.inputs_of_AddNode \<open>kind g2 n = AddNode x y\<close> child_unchanged encode_in_ids in_set_member inputs.simps local.wf member_rec(1) rep.AddNode)
next
  case (MulNode n x y xe ye)
  then have "kind g2 n = MulNode x y"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    using inputs_of_LogicNegationNode inputs_of_are_usages
    by (metis MulNode.hyps(1) MulNode.hyps(2) MulNode.hyps(3) IRNodes.inputs_of_MulNode encode_in_ids in_mono inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case using MulNode inputs_of_MulNode
    by (metis \<open>kind g2 n = MulNode x y\<close> child_unchanged inputs.simps list.set_intros(1) rep.MulNode set_subset_Cons subset_iff unchanged.elims(2))
next
  case (SubNode n x y xe ye)
  then have "kind g2 n = SubNode x y"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    using inputs_of_LogicNegationNode inputs_of_are_usages
    by (metis SubNode.hyps(1) SubNode.hyps(2) SubNode.hyps(3) IRNodes.inputs_of_SubNode encode_in_ids in_mono inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case using SubNode inputs_of_SubNode
    by (metis \<open>kind g2 n = SubNode x y\<close> child_member child_unchanged encode_in_ids ids_some member_rec(1) rep.SubNode)
next
  case (AndNode n x y xe ye)
  then have "kind g2 n = AndNode x y"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    using inputs_of_LogicNegationNode inputs_of_are_usages
    by (metis AndNode.hyps(1) AndNode.hyps(2) AndNode.hyps(3) IRNodes.inputs_of_AndNode encode_in_ids in_mono inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case using AndNode inputs_of_AndNode
    by (metis \<open>kind g2 n = AndNode x y\<close> child_unchanged inputs.simps list.set_intros(1) rep.AndNode set_subset_Cons subset_iff unchanged.elims(2))
next
  case (OrNode n x y xe ye)
  then have "kind g2 n = OrNode x y"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    using inputs_of_OrNode inputs_of_are_usages
    by (metis OrNode.hyps(1) OrNode.hyps(2) OrNode.hyps(3) IRNodes.inputs_of_OrNode encode_in_ids in_mono inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case using OrNode inputs_of_OrNode
    by (metis \<open>kind g2 n = OrNode x y\<close> child_member child_unchanged encode_in_ids ids_some member_rec(1) rep.OrNode)
next
  case (XorNode n x y xe ye)
  then have "kind g2 n = XorNode x y"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    using inputs_of_XorNode inputs_of_are_usages
    by (metis XorNode.hyps(1) XorNode.hyps(2) XorNode.hyps(3) IRNodes.inputs_of_XorNode encode_in_ids in_mono inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case using XorNode inputs_of_XorNode
    by (metis \<open>kind g2 n = XorNode x y\<close> child_member child_unchanged encode_in_ids ids_some member_rec(1) rep.XorNode)
next
  case (IntegerBelowNode n x y xe ye)
  then have "kind g2 n = IntegerBelowNode x y"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    using inputs_of_IntegerBelowNode inputs_of_are_usages
    by (metis IntegerBelowNode.hyps(1) IntegerBelowNode.hyps(2) IntegerBelowNode.hyps(3) IRNodes.inputs_of_IntegerBelowNode encode_in_ids in_mono inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case using IntegerBelowNode inputs_of_IntegerBelowNode
    by (metis \<open>kind g2 n = IntegerBelowNode x y\<close> child_member child_unchanged encode_in_ids ids_some member_rec(1) rep.IntegerBelowNode)
next
  case (IntegerEqualsNode n x y xe ye)
  then have "kind g2 n = IntegerEqualsNode x y"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    using inputs_of_IntegerEqualsNode inputs_of_are_usages
    by (metis IntegerEqualsNode.hyps(1) IntegerEqualsNode.hyps(2) IntegerEqualsNode.hyps(3) IRNodes.inputs_of_IntegerEqualsNode encode_in_ids in_mono inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case using IntegerEqualsNode inputs_of_IntegerEqualsNode
    by (metis \<open>kind g2 n = IntegerEqualsNode x y\<close> child_member child_unchanged encode_in_ids ids_some member_rec(1) rep.IntegerEqualsNode)
next
  case (IntegerLessThanNode n x y xe ye)
  then have "kind g2 n = IntegerLessThanNode x y"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    using inputs_of_IntegerLessThanNode inputs_of_are_usages
    by (metis IntegerLessThanNode.hyps(1) IntegerLessThanNode.hyps(2) IntegerLessThanNode.hyps(3) IRNodes.inputs_of_IntegerLessThanNode encode_in_ids in_mono inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case using IntegerLessThanNode inputs_of_IntegerLessThanNode
    by (metis \<open>kind g2 n = IntegerLessThanNode x y\<close> child_member child_unchanged encode_in_ids ids_some member_rec(1) rep.IntegerLessThanNode)
next
  case (NarrowNode n x xe)
  then have "kind g2 n = NarrowNode x"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n"
    using inputs_of_NarrowNode inputs_of_are_usages
    by (metis NarrowNode.hyps(1) NarrowNode.hyps(2) IRNodes.inputs_of_NarrowNode encode_in_ids inputs.simps inputs_are_usages list.set_intros(1))
  then show ?case using NarrowNode inputs_of_NarrowNode
    by (metis \<open>kind g2 n = NarrowNode x\<close> child_unchanged inputs.elims list.set_intros(1) rep.NarrowNode unchanged.simps)
next
  case (SignExtendNode n x xe)
  then have "kind g2 n = SignExtendNode x"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n"
    using inputs_of_SignExtendNode inputs_of_are_usages
    by (metis SignExtendNode.hyps(1) SignExtendNode.hyps(2) IRNodes.inputs_of_NarrowNode encode_in_ids inputs.simps inputs_are_usages list.set_intros(1))
  then show ?case using SignExtendNode inputs_of_SignExtendNode
    by (metis \<open>kind g2 n = SignExtendNode x\<close> child_member_in child_unchanged in_set_member list.set_intros(1) rep.SignExtendNode unchanged.elims(2))
next
  case (ZeroExtendNode n x xe)
  then have "kind g2 n = ZeroExtendNode x"
    using kind_unchanged by metis
  then have "x \<in> eval_usages g1 n"
    using inputs_of_ZeroExtendNode inputs_of_are_usages
    by (metis ZeroExtendNode.hyps(1) ZeroExtendNode.hyps(2) IRNodes.inputs_of_ZeroExtendNode encode_in_ids inputs.simps inputs_are_usages list.set_intros(1))
  then show ?case using ZeroExtendNode inputs_of_ZeroExtendNode
    by (metis \<open>kind g2 n = ZeroExtendNode x\<close> child_member_in child_unchanged member_rec(1) rep.ZeroExtendNode unchanged.simps)
next
  case (LeafNode n s)
  then show ?case
    by (metis kind_unchanged rep.LeafNode stamp_unchanged)
qed
qed


(* Main theorem that we want. *)
theorem stay_same:
  assumes nc: "unchanged (eval_usages g1 nid) g1 g2"
  assumes g1: "[g1, m, p] \<turnstile> nid \<mapsto> v1"
  assumes wf: "wf_graph g1"
  shows "[g2, m, p] \<turnstile> nid \<mapsto> v1"
proof -
  have nid: "nid \<in> ids g1"
    using g1 eval_in_ids by simp
  then have "nid \<in> eval_usages g1 nid" 
    using eval_usages_self by blast
  then have kind_same: "kind g1 nid = kind g2 nid"
    using nc node_unchanged by blast
  obtain e where e: "(g1 \<turnstile> nid \<triangleright> e) \<and> ([m,p] \<turnstile> e \<mapsto> v1)"
    using encodeeval_def g1
    by auto
  then have val: "[m,p] \<turnstile> e \<mapsto> v1"
    using g1 encodeeval_def
    by simp
  then show ?thesis using e nid nc (* kind_same *)
    unfolding encodeeval_def
  proof (induct e v1 arbitrary: nid rule: "evaltree.induct")
    case (ConstantExpr c)
    then show ?case
      by (metis ConstantNode ConstantNodeE kind_unchanged)
  next
    case (ParameterExpr s i)
    have "g2 \<turnstile> nid \<triangleright> ParameterExpr i s"
      using stay_same_encoding ParameterExpr
      by (meson local.wf)
    then show ?case using evaltree.ParameterExpr
      by (meson ParameterExpr.hyps)
  next
    case (ConditionalExpr ce cond branch te fe v)
    then have "g2 \<turnstile> nid \<triangleright> ConditionalExpr ce te fe"
      using ConditionalExpr.prems(1) ConditionalExpr.prems(3) local.wf stay_same_encoding by presburger
    then show ?case
      by (metis ConditionalExpr.hyps(1) ConditionalExpr.hyps(3) ConditionalExpr.hyps(4) evaltree.ConditionalExpr)
  next
    case (UnaryExpr xe v op)
    then have "g2 \<turnstile> nid \<triangleright> UnaryExpr op xe"
      using stay_same_encoding
      using local.wf by presburger
    then show ?case
      using UnaryExpr.hyps(1) by blast
  next
    case (ConvertExpr xe v op)
    then have "g2 \<turnstile> nid \<triangleright> ConvertExpr op xe"
      using stay_same_encoding
      using local.wf by presburger
    then show ?case
      using ConvertExpr.hyps(1) by blast
  next
    case (BinaryExpr xe x ye y op)
    then have "g2 \<turnstile> nid \<triangleright> BinaryExpr op xe ye"
      using stay_same_encoding
      using local.wf by presburger
    then show ?case
      using BinaryExpr.hyps(1,3) by blast
  next
    case (LeafExpr val nid s)
    then show ?case
      by (metis local.wf stay_same_encoding)
  qed
qed


lemma add_changed:
  assumes "gup = add_node new k g"
  shows "changeonly {new} g gup"
  using assms unfolding add_node_def changeonly.simps
  using add_node.rep_eq add_node_def kind.rep_eq stamp.rep_eq by simp

lemma disjoint_change:
  assumes "changeonly change g gup"
  assumes "nochange = ids g - change"
  shows "unchanged nochange g gup"
  using assms unfolding changeonly.simps unchanged.simps
  by blast

lemma add_node_unchanged:
  assumes "new \<notin> ids g"
  assumes "nid \<in> ids g"
  assumes "gup = add_node new k g"
  assumes "wf_graph g"
  shows "unchanged (eval_usages g nid) g gup"
proof -
  have "new \<notin> (eval_usages g nid)" using assms
    using eval_usages.simps by blast
  then have "changeonly {new} g gup"
    using assms add_changed by blast
  then show ?thesis using assms add_node_def disjoint_change
    using Diff_insert_absorb by auto
qed

lemma eval_uses_imp:
  "((nid' \<in> ids g \<and> nid = nid')
    \<or> nid' \<in> inputs g nid
    \<or> (\<exists>nid'' . eval_uses g nid nid'' \<and> eval_uses g nid'' nid'))
    \<longleftrightarrow> eval_uses g nid nid'"
  using use0 use_inp use_trans
  by (meson eval_uses.simps)

lemma wf_use_ids:
  assumes "wf_graph g"
  assumes "nid \<in> ids g"
  assumes "eval_uses g nid nid'"
  shows "nid' \<in> ids g"
  using assms(3)
proof (induction rule: eval_uses.induct)
  case use0
  then show ?case by simp
next
  case use_inp
  then show ?case
    using assms(1) inp_in_g_wf by blast
next
  case use_trans
  then show ?case by blast
qed

lemma no_external_use:
  assumes "wf_graph g"
  assumes "nid' \<notin> ids g"
  assumes "nid \<in> ids g"
  shows "\<not>(eval_uses g nid nid')"
proof -
  have 0: "nid \<noteq> nid'"
    using assms by blast
  have inp: "nid' \<notin> inputs g nid"
    using assms
    using inp_in_g_wf by blast
  have rec_0: "\<nexists>n . n \<in> ids g \<and> n = nid'"
    using assms by blast
  have rec_inp: "\<nexists>n . n \<in> ids g \<and> n \<in> inputs g nid'"
    using assms(2) inp_in_g by blast
  have rec: "\<nexists>nid'' . eval_uses g nid nid'' \<and> eval_uses g nid'' nid'"
    using wf_use_ids assms(1) assms(2) assms(3) by blast
  from inp 0 rec show ?thesis 
    using eval_uses_imp by blast
qed

end
