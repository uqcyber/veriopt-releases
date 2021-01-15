section \<open>Dynamic Frames for GraalVM graphs\<close>

(* This theory defines two operators, 'unchanged' and 'changeonly',
   that are useful for specifying which nodes in an IRGraph can change.
   The dynamic framing idea originates from 'Dynamic Frames' in software verification,
   started by Ioannis T. Kassios in "Dynamic frames: Support for framing, 
   dependencies and sharing without restrictions", In FM 2006.
*)

theory IRGraphFrames
  imports 
    IREval
    "HOL-Library.FSet"
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


subsection \<open>Some notation for input nodes used\<close>

(* Relates all the nodes used in an 'eval', including the node itself. *)
inductive eval_uses:: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool"
  for g where

  use0: "nid \<in> ids g
    \<Longrightarrow> eval_uses g nid nid" |

  use_inp: "nid' \<in> set(inp g n)
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

lemma not_in_g: 
  assumes "nid \<notin> ids g"
  shows "kind g nid = NoNode"
  using assms ids_some by blast

lemma not_in_g_inp: 
  assumes "nid \<notin> ids g"
  shows "inp g nid = []"
proof -
  have k: "kind g nid = NoNode" using assms not_in_g by blast
  then show ?thesis by (simp add: k)
qed

lemma child_member:
  assumes "n = kind g nid"
  assumes "n \<noteq> NoNode"
  assumes "List.member (inputs_of n) child"
  shows "child \<in> set (inp g nid)"
  unfolding inp.simps using assms
  by (metis in_set_member) 

lemma child_member_in:
  assumes "nid \<in> ids g"
  assumes "List.member (inputs_of (kind g nid)) child"
  shows "child \<in> set (inp g nid)"
  unfolding inp.simps using assms
  by (metis child_member ids_some inp.elims)


(* Node inputs are not necessarily in ids g (unless wff_graph g).
   But this is true because 'inp' is defined using 'kind'. *)
lemma inp_in_g: 
  assumes "n \<in> set (inp g nid)"
  shows "nid \<in> ids g"
proof -
  have "inp g nid \<noteq> []"
    using assms
    by (metis empty_iff empty_set)
  then have "kind g nid \<noteq> NoNode"
    using not_in_g_inp
    using ids_some by blast
  then show ?thesis
    using not_in_g
    by metis
qed

lemma inp_in_g_wff:
  assumes "wff_graph g"
  assumes "n \<in> set (inp g nid)"
  shows "n \<in> ids g"
  using assms unfolding wff_graph.simps
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
  assumes "child \<in> set(inp g1 nid)"
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
  assumes "nid' \<in> set (inp g nid)"
  shows "eval_uses g nid nid'"
  by (metis assms use_inp)

lemma inputs_are_usages:
  assumes "nid' \<in> set (inp g nid)"
  assumes "nid' \<in> ids g"
  shows "nid' \<in> eval_usages g nid"
  using assms(1) assms(2) eval_usages inputs_are_uses by blast

lemma usage_includes_inputs:
  assumes "us = eval_usages g nid"
  assumes "ls = set (inp g nid)"
  assumes "ls \<subseteq> ids g"
  shows "ls \<subseteq> us"
  using inputs_are_usages eval_usages
  using assms(1) assms(2) assms(3) by blast

lemma elim_inp_set:
  assumes "k = kind g nid"
  assumes "k \<noteq> NoNode"
  assumes "child \<in> set (inputs_of k)"
  shows "child \<in> set (inp g nid)"
  using assms by auto

lemma eval_in_ids:
  assumes "g m \<turnstile> nid (kind g nid) \<mapsto> v"
  shows "nid \<in> ids g"
  using assms by (cases "kind g nid = NoNode"; auto)

(* Main theorem that we want. *)
theorem stay_same:
  assumes nc: "unchanged (eval_usages g1 nid) g1 g2"
  assumes g1: "g1 m \<turnstile> nid (kind g1 nid) \<mapsto> v1"
  assumes wff: "wff_graph g1"
  shows "g2 m \<turnstile> nid (kind g2 nid) \<mapsto> v1"
proof -
  have nid: "nid \<in> ids g1"
    using g1 eval_in_ids by simp
  then have "nid \<in> eval_usages g1 nid" 
    using eval_usages_self by blast
  then have kind_same: "kind g1 nid = kind g2 nid"
    using nc node_unchanged by blast 
  show ?thesis using g1 nid nc (* kind_same *)
  proof (induct m nid "(kind g1 nid)" v1 arbitrary: nid rule: "eval.induct")
    print_cases
    case const: (ConstantNode m nid c)
    then have "(kind g2 nid) = ConstantNode c"
      using kind_unchanged by metis
    then show ?case using eval.ConstantNode const.hyps(1) by metis
  next
    case param: (ParameterNode val m i nid)
    show ?case
      by (metis eval.ParameterNode kind_unchanged param.hyps(1) param.hyps(2) param.prems(1) param.prems(2))
  next
    case (PhiNode val m nida uv uu nid)
    then have kind: "(kind g2 nid) = (PhiNode nida uu)"
      using kind_unchanged
      by metis
    then show ?case
      using eval.PhiNode PhiNode.hyps(1)
      by metis
  next
    case (ValuePhiNode val m nida uw ux uy nid)
    then have kind: "(kind g2 nid) = ValuePhiNode nida ux uy"
      using kind_unchanged by metis
    then show ?case
      using eval.ValuePhiNode kind ValuePhiNode.hyps(1) by metis 
  next
    case (ValueProxyNode m child val _ uz nid)
    from ValueProxyNode.prems(1) ValueProxyNode.hyps(3)
    have inp_in: "child \<in> set (inp g1 nid)"
      using child_member_in inputs_of_ValueProxyNode
      by (metis member_rec(1))
    then have cin: "child \<in> ids g1" 
      using wff inp_in_g_wff by blast
    from inp_in have unc: "unchanged (eval_usages g1 child) g1 g2"
      using child_unchanged ValueProxyNode.prems(2) by metis
    then have "g2 m \<turnstile> child (kind g2 child) \<mapsto> val"
      using ValueProxyNode.hyps(2) cin
      by blast
    then show ?case
      by (metis ValueProxyNode.hyps(3) ValueProxyNode.prems(1) ValueProxyNode.prems(2) eval.ValueProxyNode kind_unchanged)
  next
    case (AbsNode m x b v _ nid)
    then have "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_unchanged elim_inp_set ids_some inputs_of.simps(1) list.set_intros(1))
    then have "g2 m \<turnstile> x (kind g2 x) \<mapsto> IntVal b v"
      using AbsNode.hyps(1) AbsNode.hyps(2) not_in_g
      by (metis AbsNode.hyps(3) AbsNode.prems(1) elim_inp_set ids_some inp_in_g_wff inputs_of.simps(1) list.set_intros(1) wff)
    then show ?case
      by (metis AbsNode.hyps(3) AbsNode.prems(1) AbsNode.prems(2) eval.AbsNode kind_unchanged)
  next
    case Node: (NegateNode m x b v _ nid)
    from inputs_of_NegateNode Node.hyps(3) Node.prems(1) 
    have xinp: "x \<in> set (inp g1 nid)" 
      using child_member_in by (metis member_rec(1))
    then have xin: "x \<in> ids g1" 
      using wff inp_in_g_wff by blast
    from xinp child_unchanged Node.prems(2)
      have ux: "unchanged (eval_usages g1 x) g1 g2" by blast
    have x1:"g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal b v"
      using Node.hyps(1) Node.hyps(2)
      by blast
    have x2: "g2 m \<turnstile> x (kind g2 x) \<mapsto> IntVal b v"
      using kind_unchanged ux xin Node.hyps
      by blast
    then show ?case
      using kind_same Node.hyps(1,3) eval.NegateNode
      by (metis Node.prems(1) Node.prems(2) kind_unchanged ux xin)
  next
    case node:(AddNode m x b v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_unchanged inp.simps inputs_of.simps(9) list.set_intros(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal b v1"
      using node.hyps(1) by blast
    have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis IRNodes.inputs_of_AddNode child_member_in child_unchanged member_rec(1) node.hyps(5) node.prems(1) node.prems(2))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal b v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis AddNode inp.simps inp_in_g_wff inputs_of_AddNode kind_unchanged list.set_intros(1) set_subset_Cons subset_iff wff)
  next
    case node:(SubNode m x b v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_SubNode member_rec(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal b v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_SubNode member_rec(1))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal b v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis SubNode inp.simps inputs_of_SubNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wff wff_graph.elims(2))
  next
    case node:(MulNode m x b v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_MulNode member_rec(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal b v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_MulNode member_rec(1))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal b v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis MulNode inp.simps inputs_of_MulNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wff wff_graph.elims(2))
  next
    case node:(AndNode m x b v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_AndNode member_rec(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal b v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_AndNode member_rec(1))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal b v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis AndNode inp.simps inputs_of_AndNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wff wff_graph.elims(2))
  next
    case node: (OrNode m x b v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_OrNode member_rec(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal b v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_OrNode member_rec(1))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal b v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis OrNode inp.simps inputs_of_OrNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wff wff_graph.elims(2))
  next
    case node: (XorNode m x b v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_XorNode member_rec(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal b v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_XorNode member_rec(1))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal b v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis XorNode inp.simps inputs_of_XorNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wff wff_graph.elims(2))
  next
    case node: (IntegerEqualsNode m x b v1 y v2 val nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_IntegerEqualsNode member_rec(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal b v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_IntegerEqualsNode member_rec(1))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal b v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis (full_types) IntegerEqualsNode child_member_in in_set_member inputs_of_IntegerEqualsNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wff wff_graph.elims(2))
  next
    case node: (IntegerLessThanNode m x b v1 y v2 val nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_IntegerLessThanNode member_rec(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal b v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_IntegerLessThanNode member_rec(1))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal b v2"
      using node.hyps(3) by blast
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis (full_types) IntegerLessThanNode child_member_in in_set_member inputs_of_IntegerLessThanNode kind_unchanged list.set_intros(1) set_subset_Cons subsetD wff wff_graph.elims(2))
  next
    case node: (ShortCircuitOrNode m x b v1 y v2 val nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_ShortCircuitOrNode member_rec(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal b v1"
      using node.hyps(1) by blast
    from node have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_ShortCircuitOrNode member_rec(1))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal b v2"
      using node.hyps(3) by blast
    have x2: "g2 m \<turnstile> x (kind g2 x) \<mapsto> IntVal b v1"
      by (metis inp.simps inputs_of_ShortCircuitOrNode list.set_intros(1) node.hyps(2) node.hyps(6) node.prems(1) subsetD ux wff wff_graph.elims(2))
    have y2: "g2 m \<turnstile> y (kind g2 y) \<mapsto> IntVal b v2"
      by (metis basic_trans_rules(31) inp.simps inputs_of.simps(50) list.set_intros(1) node.hyps(4) node.hyps(6) node.prems(1) set_subset_Cons uy wff wff_graph.elims(2))
    show ?case
      using node.hyps node.prems ux x uy y x2 y2
      by (metis ShortCircuitOrNode kind_unchanged)
  next
    case node: (LogicNegationNode m x b v1 val nida nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis child_member_in child_unchanged inputs_of_LogicNegationNode member_rec(1))
    then have x:"g2 m \<turnstile> x (kind g2 x) \<mapsto> IntVal b v1"
      by (metis inp.simps inp_in_g_wff inputs_of.simps(34) list.set_intros(1) node.hyps(2) node.hyps(4) wff)
    then show ?case
      by (metis LogicNegationNode kind_unchanged node.hyps(3) node.hyps(4) node.prems(1) node.prems(2))
  next
    case node:(ConditionalNode m condition cond trueExp b trueVal falseExp falseVal val nid)
    have c: "condition \<in> set(inp g1 nid)"
      by (metis IRNodes.inputs_of_ConditionalNode child_member_in member_rec(1) node.hyps(8) node.prems(1))
    then have "unchanged (eval_usages g1 condition) g1 g2"
      using child_unchanged node.prems(2) by blast
    then have cond: "g2 m \<turnstile> condition (kind g2 condition) \<mapsto> IntVal 1 cond"
      using node c inp_in_g_wff wff by blast

    have t: "trueExp \<in> set(inp g1 nid)"
      by (metis IRNodes.inputs_of_ConditionalNode child_member_in member_rec(1) node.hyps(8) node.prems(1))
    then have utrue: "unchanged (eval_usages g1 trueExp) g1 g2"
      using node.prems(2) child_unchanged by blast
    then have trueVal: "g2 m \<turnstile> trueExp (kind g2 trueExp) \<mapsto> IntVal b (trueVal)"
      using node.hyps node t inp_in_g_wff wff by blast

    have f: "falseExp \<in> set(inp g1 nid)"
      by (metis IRNodes.inputs_of_ConditionalNode child_member_in member_rec(1) node.hyps(8) node.prems(1))
    then have ufalse: "unchanged (eval_usages g1 falseExp) g1 g2"
      using node.prems(2) child_unchanged by blast
    then have falseVal: "g2 m \<turnstile> falseExp (kind g2 falseExp) \<mapsto> IntVal b (falseVal)"
      using node.hyps node f inp_in_g_wff wff by blast

    have "g2 m \<turnstile> nid (kind g2 nid) \<mapsto> val"
      using kind_same trueVal falseVal cond
      by (metis ConditionalNode kind_unchanged node.hyps(7) node.hyps(8) node.prems(1) node.prems(2))
    then show ?case
      by blast

  next
    case (RefNode m x val nid)
    have x: "x \<in> set(inp g1 nid)"
      by (metis IRNodes.inputs_of_RefNode RefNode.hyps(3) RefNode.prems(1) child_member_in member_rec(1))
    then have ref: "g2 m \<turnstile> x (kind g2 x) \<mapsto> val"
      using RefNode.hyps(2) RefNode.prems(2) child_unchanged inp_in_g_wff wff by blast
    then show ?case
      by (metis RefNode.hyps(3) RefNode.prems(1) RefNode.prems(2) eval.RefNode kind_unchanged)
  next
    case (InvokeNodeEval val m nida _ callTarget classInit stateDuring stateAfter nex)
    then show ?case
      by (metis eval.InvokeNodeEval kind_unchanged)
  next
    case (SignedDivNode m x b v1 y v2 nid zeroCheck frameState nex)
    have xinp: "x \<in> set(inp g1 nid)"
      by (metis IRNodes.inputs_of_SignedDivNode SignedDivNode.hyps(5) SignedDivNode.prems(1) append_Cons child_member_in member_rec(1))
    from xinp have x: "g2 m \<turnstile> x (kind g2 x) \<mapsto> IntVal b v1"
      using SignedDivNode child_unchanged inp_in_g_wff wff by blast
    have yinp: "y \<in> set(inp g1 nid)"
      by (metis IRNodes.inputs_of_SignedDivNode SignedDivNode.hyps(5) SignedDivNode.prems(1) append_Cons child_member_in member_rec(1))
    from yinp have y: "g2 m \<turnstile> y (kind g2 y) \<mapsto> IntVal b v2"
      using SignedDivNode child_unchanged inp_in_g_wff wff by blast
    from x y show ?case
      by (metis SignedDivNode.hyps(5) SignedDivNode.prems(1) SignedDivNode.prems(2) eval.SignedDivNode kind_unchanged)
  next
    case (InvokeWithExceptionNodeEval val m nida _ callTarget classInit stateDuring stateAfter nex exceptionEdge)
    then show ?case
      by (metis eval.InvokeWithExceptionNodeEval kind_unchanged)
  next
    case (NewInstanceNode m nid clazz stateBefore nex)
    then show ?case
      by (metis eval.NewInstanceNode kind_unchanged)
  qed
qed

end
