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
    (n \<in> ids g1 \<and> n \<in> ids g2 \<and> snd g1 n = snd g2 n))"

(* This allows new nodes to be added to g2, but only ns can change. *)
fun changeonly :: "ID set \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "changeonly ns g1 g2 = (\<forall> n . n \<in> ids g1 \<and> n \<notin> ns \<longrightarrow> 
    (n \<in> ids g1 \<and> n \<in> ids g2 \<and> snd g1 n = snd g2 n))"

lemma node_unchanged [simp]:
  assumes "unchanged ns g1 g2"
  assumes "nid \<in> ns"
  shows "kind g1 nid = kind g2 nid"
  using assms by auto

lemma other_node_unchanged [simp]:
  assumes "changeonly ns g1 g2"
  assumes "nid \<in> ids g1"
  assumes "nid \<notin> ns"
  shows "kind g1 nid = kind g2 nid"
  using assms by auto


subsection \<open>Some notation for input nodes used\<close>

(* Relates all the nodes used in an 'eval', including the node itself. *)
inductive eval_uses:: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool"
  for g where

  use0: "nid \<in> ids g
    \<Longrightarrow> eval_uses g nid nid" |
(* WAS:
  "\<lbrakk>kind g nid = n;
    inputs_of n = ls;
    nid' \<in> set ls\<rbrakk>
    \<Longrightarrow> eval_uses g nid nid'" |
*)
  use_inp: "nid' \<in> set(inp g n)
    \<Longrightarrow> eval_uses g nid nid'" |

  use_trans: "\<lbrakk>eval_uses g nid nid';
    eval_uses g nid' nid''\<rbrakk>
    \<Longrightarrow> eval_uses g nid nid''"

fun eval_usages :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "eval_usages g nid = set (filter (eval_uses g nid) (sorted_list_of_set (ids g)))"

lemma eval_usages_self [simp]:
  assumes "nid \<in> ids g"
  shows "nid \<in> eval_usages g nid"
  using assms eval_usages.simps eval_uses.intros(1) by auto 

lemma not_in_g [simp]: 
  assumes "nid \<notin> ids g"
  shows "kind g nid = NoNode"
proof -
  have "nid \<notin> dom (snd g)"
    using assms irgraph_dom_inv by auto
  then have "snd g nid = None"
    by auto
  then show ?thesis
    by auto
qed

lemma not_in_g_inp [simp]: 
  assumes "nid \<notin> ids g"
  shows "inp g nid = []"
proof -
  have "kind g nid = NoNode" using assms not_in_g by auto
  then show ?thesis by auto
qed

(* Node inputs are not necessarily in ids g (unless wff_graph g).
   But this is true because 'inp' is defined using 'kind'. *)
lemma inp_in_g [simp]: 
  assumes "n \<in> set (inp g nid)"
  shows "nid \<in> ids g"
proof -
  have "inp g nid \<noteq> []"
    using assms by auto 
  then have "kind g nid \<noteq> NoNode"
    by fastforce
  then show ?thesis
    using not_in_g by auto
qed


lemma kind_unchanged:
  assumes "nid \<in> ids g1"
  assumes "unchanged (eval_usages g1 nid) g1 g2"
  shows "kind g1 nid = kind g2 nid"
proof -
  show ?thesis
    using assms eval_usages_self by auto
qed

lemma child_unchanged:
  assumes "child \<in> set(inp g1 nid)"
  assumes "unchanged (eval_usages g1 nid) g1 g2"
  shows "unchanged (eval_usages g1 child) g1 g2"
  by (smt assms(1) assms(2) eval_usages.simps filter_set 
      member_filter unchanged.simps use_inp use_trans)


(* Not true for all inputs?
lemma eval_usages_empty:
  shows "eval_uses g nid nid \<Longrightarrow> nid \<in> ids g"
proof (induction rule: "eval_uses.induct")
  print_cases
  case use0
  show ?case by (rule "use0")
next
  case use_inp
  show ?case using inp_in_g by auto
next
  case use_trans
  show ?case by auto
qed
*)


(*
lemma eval_usages_refl [simp]:
  assumes "nid \<in> eval_usages g nid"
  shows "nid \<in> ids g"
proof -
  have evnid: "eval_uses g nid nid"
    using assms by auto
  show ?thesis
    using evnid 
*)

lemma eval_usages[simp]:
  assumes "us = eval_usages g nid"
  assumes "nid' \<in> ids g"
  shows "eval_uses g nid nid' \<longleftrightarrow> nid' \<in> us" (is "?P \<longleftrightarrow> ?Q")
  using assms eval_usages.simps by simp

lemma inputs_are_uses:
  assumes "nid' \<in> set (inputs_of (kind g nid))"
  shows "eval_uses g nid nid'"
  by (metis assms inp.elims use_inp)

lemma inputs_are_usages:
  assumes "nid' \<in> set (inputs_of (kind g nid))"
  assumes "nid' \<in> ids g"
  shows "nid' \<in> eval_usages g nid"
  using assms(1) assms(2) eval_usages inputs_are_uses by blast

lemma usage_includes_inputs:
  assumes "us = eval_usages g nid"
  assumes "ls = set (inputs_of (kind g nid))"
  assumes "ls \<subseteq> ids g"
  shows "ls \<subseteq> us"
  using inputs_are_usages eval_usages
  using assms(1) assms(2) assms(3) by blast

lemma kind_floats:
  assumes "g1 m \<turnstile> nid (kind g1 nid) \<mapsto> v1"
  shows "is_floating_node (kind g1 nid)"
  using assms evalFloating by blast


(* Main theorem that we want. *)
lemma stay_same:
  assumes nc: "unchanged (eval_usages g1 nid) g1 g2"
  assumes g1: "g1 m \<turnstile> nid (kind g1 nid) \<mapsto> v1"
  (*assumes "unchanged (eval_usages g1 nid) g1 g2"*)
  shows (* "g1 m \<turnstile> nid (kind g1 nid) \<mapsto> v1
   \<Longrightarrow> unchanged (eval_usages g1 nid) g1 g2
   \<Longrightarrow> *) "g2 m \<turnstile> nid (kind g2 nid) \<mapsto> v1"
(* proof (induct rule: "eval.induct") *)

proof -
  have nid: "nid \<in> ids g1"
    using not_in_g g1 by fastforce
  then have "nid \<in> eval_usages g1 nid" 
    using eval_usages_self by blast
  then have kind_same: "kind g1 nid = kind g2 nid"
    using nc node_unchanged by blast 
  show ?thesis using g1 nid nc (* kind_same *)
  proof (induct m nid "kind g1 nid" v1 arbitrary: nid rule: "eval.induct")
    print_cases
    case const: (ConstantNode val c m nid)
    then have "kind g2 nid = (ConstantNode c)"
      using kind_unchanged by presburger
    then show ?case
      by (simp add: const.hyps(1) eval.ConstantNode)
  next
    case param: (ParameterNode val m i nid)
    show ?case
      by (metis eval.ParameterNode kind_unchanged param.hyps(1) param.hyps(2) param.prems(1) param.prems(2))
  next
    case (PhiNode val m nida uv uu nid)
(*
PhiNode:
    fix val_ m_ nid_ uv_ uu_ nid
    let "?case" = " g2 m_ \<turnstile> nid kind g2 nid \<mapsto> val_"
    assume hyps : "val_ = m_val m_ nid_"
                  "PhiNode uu_ nid_ = kind g1 nid"
      and
      prems : "nid \<in> ids g1" 
              "unchanged (eval_usages g1 nid) g1 g2"
              "kind g1 nid = kind g2 nid"
*)
    then have kind: "kind g2 nid = (PhiNode nida uu)"
      using kind_unchanged by presburger
    then show ?case
      using eval.PhiNode kind PhiNode.hyps(1) by simp
  next
    case (ValuePhiNode val m nida uw ux uy nid)
(*
  ValuePhiNode:
    fix val_ m_ nid_ uw_ ux_ uy_ nid
    let "?case" = " g2 m_ \<turnstile> nid kind g2 nid \<mapsto> val_"
    assume
      hyps : "val_ = m_val m_ nid_"
        "ValuePhiNode ux_ uy_ nid_ = kind g1 nid"
      and
      prems : "nid \<in> ids g1" "unchanged (eval_usages g1 nid) g1 g2"
        "kind g1 nid = kind g2 nid"

Was: (with 'nid' repeated in inductive rule)
    fix val_ m_ nid_ uw_ ux_ nid
    let "?case" = " g2 m_ \<turnstile> nid kind g2 nid \<mapsto> val_"
    assume
      hyps : "val_ = m_val m_ nid_"
        "ValuePhiNode uw_ ux_ nid_ = kind g1 nid"
      and
      prems : "nid \<in> ids g1" 
        "unchanged (eval_usages g1 nid) g1 g2"
        "kind g1 nid = kind g2 nid"
*)
    then have kind: "kind g2 nid = (ValuePhiNode nida ux uy)"
      using kind_unchanged by presburger
    then show ?case
      using eval.ValuePhiNode kind ValuePhiNode.hyps(1) by simp 
  next
    case (ValueProxyNode m child val nida uz nid)
(*
  ValueProxyNode:
    fix m_ c_ val_ nid_ uz_ nid
    let "?case" = " g2 m_ \<turnstile> nid kind g2 nid \<mapsto> val_"
    assume
      hyps : " g1 m_ \<turnstile> c_ kind g1 c_ \<mapsto> val_"
        "\<And>nid. kind g1 c_ = kind g1 nid \<Longrightarrow>
                nid \<in> ids g1 \<Longrightarrow>
                unchanged (eval_usages g1 nid) g1 g2 \<Longrightarrow>
                 g2 m_ \<turnstile> nid kind g2 nid \<mapsto> val_"
        "ValueProxyNode c_ uz_ = kind g1 nid"
      and prems : 
        "nid \<in> ids g1"
        "unchanged (eval_usages g1 nid) g1 g2"
*)
    then have "unchanged (eval_usages g1 child) g1 g2"
      by (metis child_unchanged IRNodes.inputs_of_ValueProxyNode ValueProxyNode.prems(2) inp.simps list.set_intros(1))
    then have "g2 m \<turnstile> child (kind g2 child) \<mapsto> val"
      using ValueProxyNode.hyps(2)
      using ValueProxyNode.hyps(1) good_kind not_in_g by blast  
    then show ?case
      by (metis ValueProxyNode.hyps(3) ValueProxyNode.prems(1) ValueProxyNode.prems(2) eval.ValueProxyNode kind_unchanged)
  next
    case (AbsNode m x v nid)
    then have "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_AbsNode child_unchanged inp.simps list.set_intros(1))
    then have "g2 m \<turnstile> x (kind g2 x) \<mapsto> IntVal v"
      using AbsNode.hyps(1) AbsNode.hyps(2) good_kind not_in_g by blast
    then show ?case
      by (metis AbsNode.hyps(3) AbsNode.prems(1) AbsNode.prems(2) eval.AbsNode kind_unchanged)
  next
    case (NegateNode m x v nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_NegateNode child_unchanged inp.simps list.set_intros(1))
    then have x:"g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal v"
      using NegateNode.hyps(1) by blast
    then show ?case
      by (metis NegateNode.hyps(2) NegateNode.hyps(3) NegateNode.prems(2) NoNodeE ux eval.NegateNode kind_unchanged not_in_g)
  next
    case node:(AddNode m x v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_AddNode child_unchanged inp.simps list.set_intros(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal v1"
      using node.hyps(1) by blast
    have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis node.hyps(5) node.prems(2) IRNodes.inputs_of_AddNode child_unchanged inp.simps list.set_intros(1) list.set_intros(2))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal v2"
      using node.hyps(3) by simp
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis NoNodeE eval.AddNode kind_unchanged not_in_g) 
  next
    case node:(SubNode m x v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_SubNode child_unchanged inp.simps list.set_intros(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal v1"
      using node.hyps(1) by blast
    have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis node.hyps(5) node.prems(2) IRNodes.inputs_of_SubNode child_unchanged inp.simps list.set_intros(1) list.set_intros(2))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal v2"
      using node.hyps(3) by simp
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis SubNode good_kind kind_unchanged not_in_g)
  next
    case node:(MulNode m x v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_MulNode child_unchanged inp.simps list.set_intros(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal v1"
      using node.hyps(1) by blast
    have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis node.hyps(5) node.prems(2) IRNodes.inputs_of_MulNode child_unchanged inp.simps list.set_intros(1) list.set_intros(2))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal v2"
      using node.hyps(3) by simp
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis MulNode good_kind kind_unchanged not_in_g)
  next
    case node:(AndNode m x v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_AndNode child_unchanged inp.simps list.set_intros(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal v1"
      using node.hyps(1) by blast
    have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis node.hyps(5) node.prems(2) IRNodes.inputs_of_AndNode child_unchanged inp.simps list.set_intros(1) list.set_intros(2))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal v2"
      using node.hyps(3) by simp
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis AndNode NoNodeE kind_unchanged not_in_g)
  next
    case node: (OrNode m x v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_OrNode child_unchanged inp.simps list.set_intros(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal v1"
      using node.hyps(1) by blast
    have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis node.hyps(5) node.prems(2) IRNodes.inputs_of_OrNode child_unchanged inp.simps list.set_intros(1) list.set_intros(2))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal v2"
      using node.hyps(3) by simp
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis NoNodeE OrNode kind_unchanged not_in_g)
  next
    case node: (XorNode m x v1 y v2 nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_XorNode child_unchanged inp.simps list.set_intros(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal v1"
      using node.hyps(1) by blast
    have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis node.hyps(5) node.prems(2) IRNodes.inputs_of_XorNode child_unchanged inp.simps list.set_intros(1) list.set_intros(2))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal v2"
      using node.hyps(3) by simp
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis XorNode good_kind kind_unchanged not_in_g)
  next
    case node: (IntegerEqualsNode m x v1 y v2 val nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_IntegerEqualsNode child_unchanged inp.simps list.set_intros(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal v1"
      using node.hyps(1) by blast
    have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis IRNodes.inputs_of_IntegerEqualsNode child_unchanged inp.simps list.set_intros(1)
          node.hyps(6) node.prems(2) set_subset_Cons subset_code(1))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal v2"
      using node.hyps(3) by simp
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis IntegerEqualsNode good_kind kind_unchanged not_in_g)
  next
    case node: (IntegerLessThanNode m x v1 y v2 val nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_IntegerLessThanNode child_unchanged inp.simps list.set_intros(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal v1"
      using node.hyps(1) by blast
    have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis IRNodes.inputs_of_IntegerLessThanNode child_unchanged inp.simps list.set_intros(1)
          node.hyps(6) node.prems(2) set_subset_Cons subset_code(1))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal v2"
      using node.hyps(3) by simp
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis IntegerLessThanNode good_kind kind_unchanged not_in_g)
  next
    case node: (ShortCircuitOrNode m x v1 y v2 val nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_ShortCircuitOrNode child_unchanged inp.simps list.set_intros(1))
    then have x: "g1 m \<turnstile> x (kind g1 x) \<mapsto> IntVal v1"
      using node.hyps(1) by blast
    have uy: "unchanged (eval_usages g1 y) g1 g2"
      by (metis IRNodes.inputs_of_ShortCircuitOrNode child_unchanged inp.simps list.set_intros(1)
          node.hyps(6) node.prems(2) set_subset_Cons subset_code(1))
    have y: "g1 m \<turnstile> y (kind g1 y) \<mapsto> IntVal v2"
      using node.hyps(3) by simp
    show ?case
      using node.hyps node.prems ux x uy y
      by (metis eval.ShortCircuitOrNode good_kind kind_unchanged not_in_g)
  next
    case node: (LogicNegationNode m x v1 val nida nid)
    then have ux: "unchanged (eval_usages g1 x) g1 g2"
      by (metis IRNodes.inputs_of_LogicNegationNode child_unchanged inp.simps list.set_intros(1))
    then have x:"g2 m \<turnstile> x (kind g2 x) \<mapsto> IntVal v1"
      using node.hyps good_kind not_in_g by blast 
    then show ?case
      by (metis LogicNegationNode kind_unchanged node.hyps(3) node.hyps(4) node.prems(1) node.prems(2))


(* updated up to here! 
   Nb. CallNodeEval still needs callee nid added inside *)


  next
    case node:(ConditionalNode m condition cond trueExp trueVal falseExp falseVal val nid)
(*
  ConditionalNode:
    fix m_ condition_ cond_ trueExp_ trueVal_ falseExp_ falseVal_ val_ nid_
      nid
    let "?case" = " g2 m_ \<turnstile> nid kind g2 nid \<mapsto> val_"
    assume
      hyps : " g1 m_ \<turnstile> condition_ kind g1 condition_ \<mapsto> IntVal cond_"
        "\<And>nid. kind g1 condition_ = kind g1 nid \<Longrightarrow>
                nid \<in> ids g1 \<Longrightarrow>
                unchanged (eval_usages g1 nid) g1 g2 \<Longrightarrow>
                 g2 m_ \<turnstile> nid kind g2 nid \<mapsto> IntVal cond_"
        " g1 m_ \<turnstile> trueExp_ kind g1 trueExp_ \<mapsto> IntVal trueVal_"
        "\<And>nid. kind g1 trueExp_ = kind g1 nid \<Longrightarrow>
                nid \<in> ids g1 \<Longrightarrow>
                unchanged (eval_usages g1 nid) g1 g2 \<Longrightarrow>
                 g2 m_ \<turnstile> nid kind g2 nid \<mapsto> IntVal trueVal_"
        " g1 m_ \<turnstile> falseExp_ kind g1 falseExp_ \<mapsto> IntVal falseVal_"
        "\<And>nid. kind g1 falseExp_ = kind g1 nid \<Longrightarrow>
                nid \<in> ids g1 \<Longrightarrow>
                unchanged (eval_usages g1 nid) g1 g2 \<Longrightarrow>
                 g2 m_ \<turnstile> nid kind g2 nid \<mapsto> IntVal falseVal_"
        "val_ = IntVal (if cond_ \<noteq> 0 then trueVal_ else falseVal_)"
        "ConditionalNode condition_ trueExp_ falseExp_ = kind g1 nid"
      and prems : "nid \<in> ids g1" "unchanged (eval_usages g1 nid) g1 g2"
*)
    (* condition first *)
    have c: "condition \<in> set(inp g1 nid)"
      by (metis (full_types) IRNodes.inputs_of_ConditionalNode inp.simps list.set_intros(1) node.hyps(8))
    then have "unchanged (eval_usages g1 condition) g1 g2"
      using child_unchanged node.prems(2) by blast
    (* TODO: first prove that  "condition \<in> ids g1" ? *)
    then have cond: "g2 m \<turnstile> condition (kind g2 condition) \<mapsto> IntVal cond"
      using node
      by (metis good_kind not_in_g)

    (* then the true branch *)
    have "trueExp \<in> set(inp g1 nid)"
      by (metis node.hyps(8) IRNodes.inputs_of_ConditionalNode inp.simps list.set_intros(1) list.set_intros(2))
    then have utrue: "unchanged (eval_usages g1 trueExp) g1 g2"
      using node.prems(2) child_unchanged by blast


    then have trueVal: "g2 m \<turnstile> trueExp (kind g2 trueExp) \<mapsto> IntVal(trueVal)"
      using node.hyps
      by (metis good_kind not_in_g)

    then have ufalse: "unchanged (eval_usages g1 falseExp) g1 g2"
      using node.prems(2) child_unchanged
      by (metis in_mono inp.simps inputs_of.simps(16) list.set_intros(1) node.hyps(8) set_subset_Cons)
    then have falseVal: "g2 m \<turnstile> falseExp (kind g2 falseExp) \<mapsto> IntVal(falseVal)"
      using node.hyps by (metis good_kind not_in_g)

    have "g2 m \<turnstile> nid (kind g2 nid) \<mapsto> val"
      using kind_same trueVal falseVal cond
      by (metis ConditionalNode kind_unchanged node.hyps(7) node.hyps(8) node.prems(1) node.prems(2))
    then show ?case
      by blast

  next
    case (CallNodeEval val m nid start args children)
    then show ?case sorry
  next
    case (RefNode m x val nid)
    then show ?case
      by (metis IRNodes.inputs_of_RefNode child_unchanged eval.RefNode good_kind inp.simps kind_unchanged list.set_intros(1) not_in_g)
  next
    case (InvokeNodeEval val m nid callTarget classInit stateDuring stateAfter nex)
    then show ?case sorry
  next
    case (SignedDivNode m x v1 y v2 nid zeroCheck frameState nex)
    then show ?case sorry
  next
    case (InvokeWithExceptionNodeEval val m nid callTarget classInit stateDuring stateAfter nex exceptionEdge)
    then show ?case sorry
  next
    case (NewInstanceNode m nid clazz stateBefore nex)
    then show ?case
      by (metis eval.NewInstanceNode kind_unchanged)
  qed
qed

lemma eval_uses_to_changes:
  assumes "nid \<noteq> nid'"
  assumes "\<not>(eval_uses g1 nid nid')"
  assumes "g2 = add_node nid' n g1"
  shows "\<not>(changes nid g1 g2) \<and> (\<forall> nid' \<in> (eval_usages g1 nid) . \<not>(changes nid' g1 g2))" (is "?P \<and> ?Q")
proof
  show ?P
    using assms(1) assms(3) changes.simps kind_uneffected_uneq by blast
next
  show ?Q 
    by (metis assms(2) assms(3) changes.elims(2) eval_usages.simps filter_set kind_uneffected_uneq member_filter)
qed

(*
lemma eval_independent:
  assumes indep: "\<not>(eval_uses g1 nid nid') \<and> nid \<noteq> nid'"
  assumes g2: "g2 = add_node nid' n g1"
  assumes v1: "g1 m \<turnstile> nid (kind g1 nid) \<mapsto> v1"
  shows "g2 m \<turnstile> nid (kind g2 nid) \<mapsto> v1"
proof -
  have nid_in: "nid \<in> ids g1"
    using not_in_no_val v1 by blast
  then have k: "(kind g1 nid) = (kind g2 nid)"
    using g2 indep kind_uneffected_uneq by blast
  show ?thesis
  proof (cases "is_floating_node (kind g2 nid)")
    case True
    then show ?thesis
      using eval_uses_to_changes indep g2 v1 stay_same
      by meson
  next
    case False
    then show ?thesis
      using evalFloating k v1 by fastforce
  qed
qed
*)

