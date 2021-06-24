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
    Semantics.IREval
begin

fun unchanged :: "ID set \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "unchanged ns g1 g2 = (\<forall> n . n \<in> ns \<longrightarrow> 
    (n \<in> ids g1 \<and> n \<in> ids g2 \<and> kind g1 n = kind g2 n))"

(* This allows new nodes to be added to g2, but only ns can change. *)
fun changeonly :: "ID set \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "changeonly ns g1 g2 = (\<forall> n . n \<in> ids g1 \<and> n \<notin> ns \<longrightarrow> 
    (n \<in> ids g1 \<and> n \<in> ids g2 \<and> kind g1 n = kind g2 n))"

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

lemma eval_in_ids:
  assumes "[g, m, p] \<turnstile> (kind g nid) \<mapsto> v"
  shows "nid \<in> ids g"
  using assms by (cases "kind g nid = NoNode"; auto)

(* Main theorem that we want. *)
theorem stay_same:
  assumes nc: "unchanged (eval_usages g1 nid) g1 g2"
  assumes g1: "[g1, m, p] \<turnstile> (kind g1 nid) \<mapsto> v1"
  assumes wf: "wf_graph g1"
  shows "[g2, m, p] \<turnstile> (kind g2 nid) \<mapsto> v1"
proof -
  have nid: "nid \<in> ids g1"
    using g1 eval_in_ids by simp
  then have "nid \<in> eval_usages g1 nid" 
    using eval_usages_self by blast
  then have kind_same: "kind g1 nid = kind g2 nid"
    using nc node_unchanged by blast 
  show ?thesis using g1 nid nc (* kind_same *)
  proof (induct "(kind g1 nid)" v1 arbitrary: nid rule: "eval.induct")
    print_cases
    case const: (ConstantNode c)
    then have "(kind g2 nid) = ConstantNode c"
      using kind_unchanged by metis
    then show ?case using eval.ConstantNode const.hyps(1) by metis
  next
    case param: (ParameterNode val i)
    show ?case
      by (metis eval.ParameterNode kind_unchanged param.hyps(1) param.prems(1) param.prems(2))
  next
    case (ValuePhiNode nida vals merges)
    then have kind: "(kind g2 nid) = ValuePhiNode nida vals merges"
      using kind_unchanged by metis
    then show ?case
      using eval.ValuePhiNode kind ValuePhiNode.hyps(1) by metis 
  next
    case (ValueProxyNode child val _ nid)
    from ValueProxyNode.prems(1) ValueProxyNode.hyps(3)
    have inp_in: "child \<in> inputs g1 nid"
      using child_member_in inputs_of_ValueProxyNode
      by (metis member_rec(1))
    then have cin: "child \<in> ids g1" 
      using wf inp_in_g_wf by blast
    from inp_in have unc: "unchanged (eval_usages g1 child) g1 g2"
      using child_unchanged ValueProxyNode.prems(2) by metis
    then have "[g2, m, p] \<turnstile> (kind g2 child) \<mapsto> val"
      using ValueProxyNode.hyps(2) cin
      by blast
    then show ?case
      by (metis ValueProxyNode.hyps(3) ValueProxyNode.prems(1) ValueProxyNode.prems(2) eval.ValueProxyNode kind_unchanged)
  next
    case (AbsNode x v _)
    then have "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_unchanged elim_inp_set ids_some inputs_of.simps(1) list.set_intros(1))
    then have "[g2, m, p] \<turnstile> (kind g2 x) \<mapsto> IntVal32 v"
      using AbsNode.hyps(1) AbsNode.hyps(2) not_in_g
      by (metis AbsNode.hyps(3) AbsNode.prems(1) elim_inp_set ids_some inp_in_g_wf inputs_of.simps(1) list.set_intros(1) wf)
    then show ?case
      by (metis AbsNode.hyps(3) AbsNode.prems(1) AbsNode.prems(2) eval.AbsNode kind_unchanged)
  next
    case Node: (NegateNode x v _)
    from inputs_of_NegateNode Node.hyps(3) Node.prems(1) 
    have xinp: "x \<in> inputs g1 nid" 
      using child_member_in by (metis member_rec(1))
    then have xin: "x \<in> ids g1" 
      using wf inp_in_g_wf by blast
    from xinp child_unchanged Node.prems(2)
      have ux: "unchanged (eval_usages g1 x) g1 g2" by blast
    have x1:"[g1, m, p] \<turnstile> (kind g1 x) \<mapsto> v"
      using Node.hyps(1) Node.hyps(2)
      by blast
    have x2: "[g2, m, p] \<turnstile> (kind g2 x) \<mapsto> v"
      using kind_unchanged ux xin Node.hyps
      by blast
    then show ?case
      using kind_same Node.hyps(1,3) eval.NegateNode
      by (metis Node.prems(1) Node.prems(2) kind_unchanged ux xin)
  next
    case node:(AddNode x v1 y v2)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_unchanged inputs.simps inputs_of_AddNode list.set_intros(1))
    then have x: "[g1, m, p] \<turnstile> (kind g1 x) \<mapsto> v1"
      using node.hyps(1) by blast
    have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis IRNodes.inputs_of_AddNode child_member_in child_unchanged member_rec(1) node.hyps(5) node.prems(1) node.prems(2))
    have y: "[g1, m, p] \<turnstile> (kind g1 y) \<mapsto> v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis AddNode inputs.simps inp_in_g_wf inputs_of_AddNode kind_unchanged list.set_intros(1) set_subset_Cons subset_iff wf)
  next
    case node:(SubNode x v1 y v2)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_SubNode member_rec(1))
    then have x: "[g1, m, p] \<turnstile> (kind g1 x) \<mapsto> v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_SubNode member_rec(1))
    have y: "[g1, m, p] \<turnstile> (kind g1 y) \<mapsto> v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis SubNode inputs.simps inputs_of_SubNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wf wf_folds(1,3))
  next
    case node:(MulNode x v1 y v2)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_MulNode member_rec(1))
    then have x: "[g1, m, p] \<turnstile> (kind g1 x) \<mapsto> v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_MulNode member_rec(1))
    have y: "[g1, m, p] \<turnstile> (kind g1 y) \<mapsto> v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis MulNode inputs.simps inputs_of_MulNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wf wf_folds(1,3))
  next
    case node:(AndNode x v1 y v2)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_AndNode member_rec(1))
    then have x: "[g1, m, p] \<turnstile> (kind g1 x) \<mapsto> v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_AndNode member_rec(1))
    have y: "[g1, m, p] \<turnstile> (kind g1 y) \<mapsto> v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis AndNode inputs.simps inputs_of_AndNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wf wf_folds(1,3))
  next
    case node: (OrNode x v1 y v2)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_OrNode member_rec(1))
    then have x: "[g1, m, p] \<turnstile> (kind g1 x) \<mapsto> v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_OrNode member_rec(1))
    have y: "[g1, m, p] \<turnstile> (kind g1 y) \<mapsto> v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis OrNode inputs.simps inputs_of_OrNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wf wf_folds(1,3))
  next
    case node: (XorNode x v1 y v2)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_XorNode member_rec(1))
    then have x: "[g1, m, p] \<turnstile> (kind g1 x) \<mapsto> v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_XorNode member_rec(1))
    have y: "[g1, m, p] \<turnstile> (kind g1 y) \<mapsto> v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis XorNode inputs.simps inputs_of_XorNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wf wf_folds(1,3))
  next
    case node: (IntegerEqualsNode x v1 y v2 val)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_IntegerEqualsNode member_rec(1))
    then have x: "[g1, m, p] \<turnstile> (kind g1 x) \<mapsto> IntVal32 v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_IntegerEqualsNode member_rec(1))
    have y: "[g1, m, p] \<turnstile> (kind g1 y) \<mapsto> IntVal32 v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis (full_types) IntegerEqualsNode child_member_in in_set_member inputs_of_IntegerEqualsNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wf wf_folds(1,3))
  next
    case node: (IntegerLessThanNode x v1 y v2 val)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_IntegerLessThanNode member_rec(1))
    then have x: "[g1, m, p] \<turnstile> (kind g1 x) \<mapsto> IntVal32 v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_IntegerLessThanNode member_rec(1))
    have y: "[g1, m, p] \<turnstile> (kind g1 y) \<mapsto> IntVal32 v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis (full_types) IntegerLessThanNode child_member_in in_set_member inputs_of_IntegerLessThanNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wf wf_folds(1,3))
  next
    case node: (ShortCircuitOrNode x v1 y v2 val)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_ShortCircuitOrNode member_rec(1))
    then have x: "[g1, m, p] \<turnstile> (kind g1 x) \<mapsto> IntVal32 v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_ShortCircuitOrNode member_rec(1))
    have y: "[g1, m, p] \<turnstile> (kind g1 y) \<mapsto> IntVal32 v2"
      using node.hyps(3) by blast
    have x2: "[g2, m, p] \<turnstile> (kind g2 x) \<mapsto> IntVal32 v1"
      by (metis inputs.simps inputs_of_ShortCircuitOrNode list.set_intros(1) node.hyps(2) node.hyps(6) node.prems(1) subsetD ux wf wf_folds(1,3))
    have y2: "[g2, m, p] \<turnstile> (kind g2 y) \<mapsto> IntVal32 v2"
      by (metis basic_trans_rules(31) inputs.simps inputs_of_ShortCircuitOrNode list.set_intros(1) node.hyps(4) node.hyps(6) node.prems(1) set_subset_Cons uy wf wf_folds(1,3))
    show ?case
      using node.hyps node.prems ux x uy y x2 y2
      by (metis ShortCircuitOrNode kind_unchanged)
  next
    case node: (LogicNegationNode x v1 val nida)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_LogicNegationNode member_rec(1))
    then have x:"[g2, m, p] \<turnstile> (kind g2 x) \<mapsto> IntVal32 v1"
      using eval_in_ids node.hyps(1) node.hyps(2) by blast
    then show ?case
      by (metis LogicNegationNode kind_unchanged node.hyps(3) node.hyps(4) node.hyps(5) node.prems(1) node.prems(2))
  next
    case node:(ConditionalNode condition cond trueExp trueVal falseExp falseVal val)
    have c: "condition \<in> inputs g1 nid"
      by (metis IRNodes.inputs_of_ConditionalNode child_member_in member_rec(1) node.hyps(8) node.prems(1))
    then have "unchanged (eval_usages g1 condition) g1 g2"
      using child_unchanged node.prems(2) by blast
    then have cond: "[g2, m, p] \<turnstile> (kind g2 condition) \<mapsto> IntVal32 cond"
      using node c inp_in_g_wf wf by blast

    have t: "trueExp \<in> inputs g1 nid"
      by (metis IRNodes.inputs_of_ConditionalNode child_member_in member_rec(1) node.hyps(8) node.prems(1))
    then have utrue: "unchanged (eval_usages g1 trueExp) g1 g2"
      using node.prems(2) child_unchanged by blast
    then have trueVal: "[g2, m, p] \<turnstile> (kind g2 trueExp) \<mapsto> IntVal32 (trueVal)"
      using node.hyps node t inp_in_g_wf wf by blast

    have f: "falseExp \<in> inputs g1 nid"
      by (metis IRNodes.inputs_of_ConditionalNode child_member_in member_rec(1) node.hyps(8) node.prems(1))
    then have ufalse: "unchanged (eval_usages g1 falseExp) g1 g2"
      using node.prems(2) child_unchanged by blast
    then have falseVal: "[g2, m, p] \<turnstile> (kind g2 falseExp) \<mapsto> IntVal32 (falseVal)"
      using node.hyps node f inp_in_g_wf wf by blast

    have "[g2, m, p] \<turnstile> (kind g2 nid) \<mapsto> val"
      using kind_same trueVal falseVal cond
      by (metis ConditionalNode kind_unchanged node.hyps(7) node.hyps(8) node.prems(1) node.prems(2))
    then show ?case
      by blast

  next
    case (RefNode x val nid)
    have x: "x \<in> inputs g1 nid"
      by (metis IRNodes.inputs_of_RefNode RefNode.hyps(3) RefNode.prems(1) child_member_in member_rec(1))
    then have ref: "[g2, m, p] \<turnstile> (kind g2 x) \<mapsto> val"
      using RefNode.hyps(2) RefNode.prems(2) child_unchanged inp_in_g_wf wf by blast
    then show ?case
      by (metis RefNode.hyps(3) RefNode.prems(1) RefNode.prems(2) eval.RefNode kind_unchanged)
  next
    case (InvokeNodeEval val _ callTarget classInit stateDuring stateAfter nex)
    then show ?case
      by (metis eval.InvokeNodeEval kind_unchanged)
  next
    case (SignedDivNode x v1 y v2 zeroCheck frameState nex)
      then show ?case
        by (metis eval.SignedDivNode kind_unchanged)
  next
    case (SignedRemNode x v1 y v2 zeroCheck frameState nex)
      then show ?case
        by (metis eval.SignedRemNode kind_unchanged)
  next
    case (InvokeWithExceptionNodeEval val _ callTarget classInit stateDuring stateAfter nex exceptionEdge)
    then show ?case
      by (metis eval.InvokeWithExceptionNodeEval kind_unchanged)
  next
    case (NewInstanceNode nid clazz stateBefore nex)
    then show ?case
      by (metis eval.NewInstanceNode kind_unchanged)
  next
    case (IsNullNode obj ref val)
    have obj: "obj \<in> inputs g1 nid"
      by (metis IRNodes.inputs_of_IsNullNode IsNullNode.hyps(4) inputs.simps list.set_intros(1))
    then have ref: "[g2, m, p] \<turnstile> (kind g2 obj) \<mapsto> ObjRef ref"
      using IsNullNode.hyps(1) IsNullNode.hyps(2) IsNullNode.prems(2) child_unchanged eval_in_ids by blast
    then show ?case
      by (metis (full_types) IsNullNode.hyps(3) IsNullNode.hyps(4) IsNullNode.prems(1) IsNullNode.prems(2) eval.IsNullNode kind_unchanged)
  next
    case (LoadFieldNode)
    then show ?case
      by (metis eval.LoadFieldNode kind_unchanged)
  next
    case (PiNode object val)
    have object: "object \<in> inputs g1 nid"
      using inputs_of_PiNode inputs.simps
      by (metis PiNode.hyps(3) list.set_intros(1))
    then have ref: "[g2, m, p] \<turnstile> (kind g2 object) \<mapsto> val"
      using PiNode.hyps(1) PiNode.hyps(2) PiNode.prems(2) child_unchanged eval_in_ids by blast
    then show ?case
      by (metis PiNode.hyps(3) PiNode.prems(1) PiNode.prems(2) eval.PiNode kind_unchanged)
  next
    case (NotNode x val not_val)
    have object: "x \<in> inputs g1 nid"
      using inputs_of_NotNode inputs.simps
      by (metis NotNode.hyps(4) list.set_intros(1))
    then have ref: "[g2, m, p] \<turnstile> (kind g2 x) \<mapsto> val"
      using NotNode.hyps(1) NotNode.hyps(2) NotNode.prems(2) child_unchanged eval_in_ids by blast
    then show ?case
      by (metis NotNode.hyps(3) NotNode.hyps(4) NotNode.prems(1) NotNode.prems(2) eval.NotNode kind_unchanged)
  qed
qed


lemma add_changed:
  assumes "gup = add_node new k g"
  shows "changeonly {new} g gup"
  using assms unfolding add_node_def changeonly.simps
  using add_node.rep_eq add_node_def kind.rep_eq by auto

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
