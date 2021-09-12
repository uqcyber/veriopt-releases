theory TreeSnippets
  imports 
    Semantics.IRTreeEvalThms
    HOL.Relation
begin

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

notation (latex)
  TreeToGraph.ord_IRExpr_inst.less_eq_IRExpr ("_ \<longmapsto> _")

text_raw \<open>\Snip{abstract-syntax-tree}%
@{datatype[display,margin=45] IRExpr}
\EndSnip\<close>

text_raw \<open>\Snip{tree-semantics}%
\induct{@{thm[mode=Rule] evaltree.ConstantExpr [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] evaltree.ParameterExpr [no_vars]}}{semantics:parameter}
\induct{@{thm[mode=Rule] evaltree.ConditionalExpr [no_vars]}}{semantics:conditional}
\induct{@{thm[mode=Rule] evaltree.UnaryExpr [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] evaltree.BinaryExpr [no_vars]}}{semantics:binary}
\induct{@{thm[mode=Rule] evaltree.LeafExpr [no_vars]}}{semantics:leaf}
\EndSnip\<close>
(*\induct{@{thm[mode=Rule] evaltree.ConvertExpr [no_vars]}}{semantics:convert}*)

text_raw \<open>\Snip{tree-evaluation-deterministic}%
@{thm[display] evalDet [no_vars]}
\EndSnip\<close>

text_raw \<open>\Snip{expression-refinement}%
\begin{center}
@{thm le_expr_def [no_vars]}
\end{center}
\EndSnip\<close>

(* skipping add node optimisations as they are currently very ugly *)

(* definition 5 (semantics-preserving) is there a distinction in Isabelle? *)

text_raw \<open>\Snip{graph-representation}
@{bold \<open>typedef\<close>} @{term[source] \<open>IRGraph = {g :: ID \<rightharpoonup> IRNode . finite (dom g)}\<close>}
\EndSnip\<close>

text_raw \<open>\Snip{graph2tree}
\induct{@{thm[mode=Rule] rep.ConstantNode [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] rep.ParameterNode [no_vars]}}{semantics:parameter}
\induct{@{thm[mode=Rule] rep.ConditionalNode [no_vars]}}{semantics:conditional}
\induct{@{thm[mode=Rule] rep.AbsNode [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] rep.SignExtendNode [no_vars]}}{semantics:convert}
\induct{@{thm[mode=Rule] rep.AddNode [no_vars]}}{semantics:binary}
\induct{@{thm[mode=Rule] rep.LeafNode [no_vars]}}{semantics:leaf}
\EndSnip\<close>

text_raw \<open>\Snip{preeval}
@{thm is_preevaluated.simps}
\EndSnip\<close>

text_raw \<open>\Snip{deterministic-representation}
\begin{center}
@{thm repDet [no_vars]}
\end{center}
\EndSnip\<close>

(* definition 9 (well-formed graph) no? *)

text_raw \<open>\Snip{graph-semantics}
\begin{center}
@{thm encodeeval_def}
\end{center}
\EndSnip\<close>

text_raw \<open>\Snip{graph-semantics-deterministic}
\begin{center}
@{thm graphDet [no_vars]}
\end{center}
\EndSnip\<close>

definition graph_refinement :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "graph_refinement g1 g2 = 
        (\<forall> n . n \<in> ids g1 \<longrightarrow> (\<forall>e1. (g1 \<turnstile> n \<triangleright> e1) \<longrightarrow> (\<exists>e2. (g2 \<turnstile> n \<triangleright> e2) \<and> e1 \<le> e2)))"

lemma graph_refinement:
  "graph_refinement g1 g2 \<Longrightarrow> (\<forall>n m p v. n \<in> ids g1 \<longrightarrow> ([g1, m, p] \<turnstile> n \<mapsto> v) \<longrightarrow> ([g2, m, p] \<turnstile> n \<mapsto> v))"
  by (meson encodeeval_def graph_refinement_def le_expr_def)


lemma mono_abs:
  assumes "kind g1 n = AbsNode x \<and> kind g2 n = AbsNode x"
  assumes "(g1 \<turnstile> x \<triangleright> xe1) \<and> (g2 \<turnstile> x \<triangleright> xe2)"
  assumes "xe1 \<le> xe2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  by (metis AbsNode assms(1) assms(2) assms(3) assms(4) mono_unary repDet)

lemma mono_not:
  assumes "kind g1 n = NotNode x \<and> kind g2 n = NotNode x"
  assumes "(g1 \<turnstile> x \<triangleright> xe1) \<and> (g2 \<turnstile> x \<triangleright> xe2)"
  assumes "xe1 \<le> xe2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  by (metis NotNode assms(1) assms(2) assms(3) assms(4) mono_unary repDet)

lemma mono_negate:
  assumes "kind g1 n = NegateNode x \<and> kind g2 n = NegateNode x"
  assumes "(g1 \<turnstile> x \<triangleright> xe1) \<and> (g2 \<turnstile> x \<triangleright> xe2)"
  assumes "xe1 \<le> xe2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  by (metis NegateNode assms(1) assms(2) assms(3) assms(4) mono_unary repDet)

lemma mono_logic_negation:
  assumes "kind g1 n = LogicNegationNode x \<and> kind g2 n = LogicNegationNode x"
  assumes "(g1 \<turnstile> x \<triangleright> xe1) \<and> (g2 \<turnstile> x \<triangleright> xe2)"
  assumes "xe1 \<le> xe2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  by (metis LogicNegationNode assms(1) assms(2) assms(3) assms(4) mono_unary repDet)

lemma mono_narrow:
  assumes "kind g1 n = NarrowNode x \<and> kind g2 n = NarrowNode x"
  assumes "stamp g1 n = stamp g2 n \<and> stamp g1 x = stamp g2 x"
  assumes "(g1 \<turnstile> x \<triangleright> xe1) \<and> (g2 \<turnstile> x \<triangleright> xe2)"
  assumes "xe1 \<le> xe2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  using assms mono_unary repDet NarrowNode
  by metis

lemma mono_sign_extend:
  assumes "kind g1 n = SignExtendNode x \<and> kind g2 n = SignExtendNode x"
  assumes "stamp g1 n = stamp g2 n \<and> stamp g1 x = stamp g2 x"
  assumes "(g1 \<turnstile> x \<triangleright> xe1) \<and> (g2 \<turnstile> x \<triangleright> xe2)"
  assumes "xe1 \<le> xe2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  by (metis SignExtendNode assms(1) assms(2) assms(3) assms(4) assms(5) mono_unary repDet)

lemma mono_zero_extend:
  assumes "kind g1 n = ZeroExtendNode x \<and> kind g2 n = ZeroExtendNode x"
  assumes "stamp g1 n = stamp g2 n \<and> stamp g1 x = stamp g2 x"
  assumes "(g1 \<turnstile> x \<triangleright> xe1) \<and> (g2 \<turnstile> x \<triangleright> xe2)"
  assumes "xe1 \<le> xe2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  using assms mono_unary repDet ZeroExtendNode
  by metis

lemma mono_conditional:
  assumes "kind g1 n = ConditionalNode c t f \<and> kind g2 n = ConditionalNode c t f"
  assumes "(g1 \<turnstile> c \<triangleright> ce1) \<and> (g2 \<turnstile> c \<triangleright> ce2)"
  assumes "(g1 \<turnstile> t \<triangleright> te1) \<and> (g2 \<turnstile> t \<triangleright> te2)"
  assumes "(g1 \<turnstile> f \<triangleright> fe1) \<and> (g2 \<turnstile> f \<triangleright> fe2)"
  assumes "ce1 \<le> ce2 \<and> te1 \<le> te2 \<and> fe1 \<le> fe2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  by (metis ConditionalNodeE IRNode.inject(6) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) mono_conditional repDet rep_conditional)

lemma mono_add:
  assumes "kind g1 n = AddNode x y \<and> kind g2 n = AddNode x y"
  assumes "(g1 \<turnstile> x \<triangleright> xe1) \<and> (g2 \<turnstile> x \<triangleright> xe2)"
  assumes "(g1 \<turnstile> y \<triangleright> ye1) \<and> (g2 \<turnstile> y \<triangleright> ye2)"
  assumes "xe1 \<le> xe2 \<and> ye1 \<le> ye2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  using mono_binary assms
  by (metis AddNodeE IRNode.inject(2) repDet rep_add)

lemma mono_mul:
  assumes "kind g1 n = MulNode x y \<and> kind g2 n = MulNode x y"
  assumes "(g1 \<turnstile> x \<triangleright> xe1) \<and> (g2 \<turnstile> x \<triangleright> xe2)"
  assumes "(g1 \<turnstile> y \<triangleright> ye1) \<and> (g2 \<turnstile> y \<triangleright> ye2)"
  assumes "xe1 \<le> xe2 \<and> ye1 \<le> ye2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  using mono_binary assms
  by (metis IRNode.inject(26) MulNodeE repDet rep_mul)

text_raw \<open>\Snip{graph-refinement}
\begin{center}
@{thm[display, margin=60] graph_refinement_def [no_vars]}
\end{center}
\EndSnip\<close>

definition as_set :: "IRGraph \<Rightarrow> (ID \<times> (IRNode \<times> Stamp)) set" where
  "as_set g = {(n, kind g n, stamp g n) | n . n \<in> ids g}"

(* hide as_set, should treat IRGraph as a set of pairs in paper *)
translations
  "n" <= "CONST as_set n"

definition domain_subtraction :: "'a set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set"
  (infix "\<unlhd>" 30) where
  "domain_subtraction s r = {(x, y) . (x, y) \<in> r \<and> x \<notin> s}"

notation (latex)
  domain_subtraction ("_ \<^latex>\<open>$\\ndres$\<close> _")


lemma this_is_true:
  assumes "n \<notin> ids g"
  shows "\<not>(g \<turnstile> n \<triangleright> e)"
proof -
  have "kind g n = NoNode"
    using assms ids_some by simp
  show ?thesis
  apply (rule notI)
    apply (induct n e rule: rep.induct) apply auto
    sorry
qed

lemma encodes_contains:
  assumes "g \<turnstile> n \<triangleright> e"
  shows "kind g n \<noteq> NoNode"
  using assms apply (induction rule: rep.induct)
  apply (metis IRNode.disc(349) is_ConstantNode_def)
  using IRNode.distinct(2207) apply presburger
  using IRNode.distinct(555) apply presburger
  using IRNode.distinct(95) apply presburger
  using IRNode.distinct(2141) apply presburger
  using IRNode.distinct(2027) apply presburger
  using IRNode.distinct(1635) apply presburger
  using IRNode.distinct(191) apply presburger
  using IRNode.distinct(1941) apply presburger
  using IRNode.distinct(2405) apply presburger
  using IRNode.distinct(285) apply presburger
  using IRNode.distinct(2175) apply presburger
  using IRNode.distinct(2441) apply presburger
  using IRNode.distinct(1115) apply presburger
  using IRNode.distinct(1187) apply presburger
  using IRNode.distinct(1257) apply presburger
  using IRNode.distinct(1985) apply presburger
  using IRNode.distinct(2315) apply presburger
  using IRNode.distinct(2445) apply presburger
  by (metis is_preevaluated.simps(49))
(*
  using assms 
proof -
  fix n
  assume "n \<notin> ids g"
  then have "kind g n = NoNode"
    using ids_some by simp
  show "\<not>(g \<turnstile> n \<triangleright> e)"
    apply (rule notI) apply (induct arbitrary: n e rule: rep.induct)
  apply (rule notI)
  apply (induct arbitrary: n e rule: rep.induct) apply auto
proof -
  fix n
  show "kind g n = NoNode"
qed
  using ids_some assms sorry

lemma unchanged_encoding:
  assumes "\<forall>n \<in> (ids g1 - {n}). ([g1,m,p] \<turnstile> n \<mapsto> v) \<and> ([g2,m,p] \<turnstile> n \<mapsto> v)"
  assumes "kind g1 n = kind g2 n"
  assumes "stamp g1 n = stamp g2 n"
  assumes "[g1,m,p] \<turnstile> n \<mapsto> v"
  shows "[g2,m,p] \<turnstile> n \<mapsto> v"
  using assms(4) unfolding encodeeval_def
  using assms(1,2,3) sorry
*)

datatype ExprIRNode =
  ExprUnaryNode IRUnaryOp ID |
  ExprBinaryNode IRBinaryOp ID ID |
  ExprConditionalNode ID ID ID |
  ExprConstantNode Value |
  ExprParameterNode nat |
  ExprLeafNode ID |
  NotExpr

fun embed_expr :: "IRNode \<Rightarrow> ExprIRNode" where
  "embed_expr (ConstantNode v) = ExprConstantNode v" |
  "embed_expr (ParameterNode i) = ExprParameterNode i" |
  "embed_expr (ConditionalNode c t f) = ExprConditionalNode c t f" |
  "embed_expr (AbsNode x) = ExprUnaryNode UnaryAbs x" |
  "embed_expr (NotNode x) = ExprUnaryNode UnaryNot x" |
  "embed_expr (NegateNode x) = ExprUnaryNode UnaryNeg x" |
  "embed_expr (LogicNegationNode x) = ExprUnaryNode UnaryLogicNegation x" |
  "embed_expr (AddNode x y) = ExprBinaryNode BinAdd x y" |
  "embed_expr (MulNode x y) = ExprBinaryNode BinMul x y" |
  "embed_expr (SubNode x y) = ExprBinaryNode BinSub x y" |
  "embed_expr (AndNode x y) = ExprBinaryNode BinAnd x y" |
  "embed_expr (OrNode x y) = ExprBinaryNode BinOr x y" |
  "embed_expr (XorNode x y) = ExprBinaryNode BinXor x y" |
  "embed_expr (IntegerBelowNode x y) = ExprBinaryNode BinIntegerBelow x y" |
  "embed_expr (IntegerEqualsNode x y) = ExprBinaryNode BinIntegerEquals x y" |
  "embed_expr (IntegerLessThanNode x y) = ExprBinaryNode BinIntegerLessThan x y" |
(*
  "embed_expr (NarrowNode x) = ExprUnaryNode (UnaryNarrow 0 0) x" |
  "embed_expr (SignExtendNode x) = ExprUnaryNode (UnarySignExtend 0 0) x" |
  "embed_expr (ZeroExtendNode x) = ExprUnaryNode (UnaryZeroExtend 0 0) x" |
*)
  "embed_expr _ = NotExpr"

definition is_convert_node :: "IRNode \<Rightarrow> bool" where
  "is_convert_node n = ((is_NarrowNode n) \<or> (is_SignExtendNode n) \<or> (is_ZeroExtendNode n))"

lemmas reps =
  rep_constant
  rep_parameter
  rep_conditional
  rep_abs
  rep_not
  rep_negate
  rep_logicnegation
  rep_add
  rep_sub
  rep_mul
  rep_and
  rep_or
  rep_xor
  rep_integer_below
  rep_integer_equals
  rep_integer_less_than
  rep_narrow
  rep_sign_extend
  rep_zero_extend
  rep_load_field

lemma unary_embed:
  assumes "g \<turnstile> n \<triangleright> UnaryExpr op x"
  assumes "\<not>(is_convert_node (kind g n))"
  shows "\<exists> x' . embed_expr (kind g n) = ExprUnaryNode op x'"
  using assms apply (induction "UnaryExpr op x" rule: rep.induct; simp)
  unfolding is_convert_node_def
  using is_NarrowNode_def is_SignExtendNode_def is_ZeroExtendNode_def by blast+

lemma equal_embedded_x:
  assumes "g \<turnstile> n \<triangleright> UnaryExpr op xe"
  assumes "embed_expr (kind g n) = ExprUnaryNode op' x"
  shows "g \<turnstile> x \<triangleright> xe"
  using assms by (induction "UnaryExpr op xe" rule: rep.induct; simp)

lemma blah:
  assumes "embed_expr (kind g n) = ExprUnaryNode op n'"
  assumes "g \<turnstile> n' \<triangleright> e"
  shows "(g \<turnstile> n \<triangleright> UnaryExpr op e)"
  using assms(2,1) apply (cases "kind g n"; auto)
  using rep.AbsNode apply blast
  using rep.LogicNegationNode apply blast
  using rep.NegateNode apply blast
  using rep.NotNode by blast

lemma not_excluded_keep_type:
  assumes "n \<in> ids g1"
  assumes "n \<notin> excluded"
  assumes "(excluded \<unlhd> as_set g1) \<subseteq> as_set g2"
  shows "kind g1 n = kind g2 n \<and> stamp g1 n = stamp g2 n"
  using assms unfolding as_set_def domain_subtraction_def by blast

lemma graph_semantics_preservation:
  assumes a: "e1' \<le> e2'"
  assumes b: "({n'} \<unlhd> as_set g1) \<subseteq> as_set g2"
  assumes c: "g1 \<turnstile> n' \<triangleright> e1'"
  assumes d: "g2 \<turnstile> n' \<triangleright> e2'"
  assumes hack: "(\<forall> n. n \<in> ids g1 \<longrightarrow> \<not>(is_convert_node (kind g1 n)))"
  shows "graph_refinement g1 g2"
  unfolding graph_refinement_def 
  apply (rule allI) apply (rule impI) apply (rule allI) apply (rule impI)
proof -
  fix n e1
  assume e: "n \<in> ids g1"
  assume f: "(g1 \<turnstile> n \<triangleright> e1)"

  show "\<exists> e2. (g2 \<turnstile> n \<triangleright> e2) \<and> e1 \<le> e2"
  proof (cases "n = n'")
    case True
    have g: "e1 = e1'" using c f True repDet by simp
    have h: "(g2 \<turnstile> n \<triangleright> e2') \<and> e1' \<le> e2'"
      using True a d by blast
    then show ?thesis 
      using g by blast
  next
    case False
    have "n \<notin> {n'}"
      using False by simp
    then have i: "kind g1 n = kind g2 n \<and> stamp g1 n = stamp g2 n"
      using not_excluded_keep_type
      using b e by presburger
    show ?thesis using f
      proof (cases e1)
        case (UnaryExpr op xe1)
        from UnaryExpr have k: "g1 \<turnstile> n \<triangleright> UnaryExpr op xe1" using f by blast
        have "\<not>(is_convert_node (kind g1 n))"
          using hack encodes_contains ids_some
          using e by blast
        then obtain xn where l: "embed_expr (kind g1 n) = ExprUnaryNode op xn"
          using k using unary_embed
          by blast
        then have kk: "g1 \<turnstile> xn \<triangleright> xe1"
          using repDet k equal_embedded_x by blast
        then show ?thesis
        proof (cases "xn = n'")
          case True
          then have n: "xe1 = e1'" using c UnaryExpr repDet l
            using kk by presburger
          have r: "UnaryExpr op e1' \<le> UnaryExpr op e2'"
            using a mono_unary by simp
          have "g2 \<turnstile> n \<triangleright> UnaryExpr op e2'" using i k UnaryExpr n d True
            using blah
            using l by presburger
          then show ?thesis
            using r UnaryExpr n by blast 
        next
          case False
          then have "g1 \<turnstile> xn \<triangleright> xe1" using UnaryExpr
            by (simp add: kk)
          then have "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2" sorry
          then have "\<exists> xe2. (g2 \<turnstile> n \<triangleright> UnaryExpr op xe2) \<and> UnaryExpr op xe1 \<le> UnaryExpr op xe2"
            by (metis blah i l mono_unary)
          then show ?thesis
            using UnaryExpr by blast
        qed
      next
        case (BinaryExpr x1 e11 e12)
        then show ?thesis sorry
      next
        case (ConditionalExpr e11 e12 e13)
        then show ?thesis sorry
      next
        case (ConstantExpr x)
        then show ?thesis sorry
      next
        case (ParameterExpr x1 x2)
        then show ?thesis sorry
      next
        case (LeafExpr x1 x2)
        then show ?thesis sorry
      qed
  qed
qed

(*
lemma graph_semantics_preservation:
  "e1 \<le> e2 \<and> (g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2) \<and> (({n} \<unlhd> as_set g1) \<subseteq> as_set g2) \<Longrightarrow>
     graph_refinement g1 g2" (is "?asm \<Longrightarrow> ?con")
proof (cases "n \<in> ids g1")
  case True
  assume a: ?asm
  show ?thesis
    unfolding graph_refinement_def
  proof ((rule allI)+; (rule impI)+)
    fix n1 m p v
    assume a0: "n1 \<in> ids g1"
    assume a1: "([g1,m,p] \<turnstile> n1 \<mapsto> v)"
    obtain e1 where "g1 \<turnstile> n1 \<triangleright> e1"
      using a1 encodeeval_def by auto
    have same: "n1 \<notin> {n} \<Longrightarrow> kind g1 n1 = kind g2 n1 \<and> stamp g1 n1 = stamp g2 n1"
      using a a0 unfolding as_set_def domain_subtraction_def
      by blast
    show "([g2,m,p] \<turnstile> n1 \<mapsto> v)" using a0 a1 a unfolding encodeeval_def
      apply (cases "n = n1")
      using a1 encodeeval_def le_expr_def repDet apply blast
      using same unchanged_encoding sorry
  qed
next
  case False
  assume a: ?asm
  show ?thesis (* using False unfolding graph_refinement_def as_set_def domain_subtraction_def *)
    unfolding graph_refinement_def
  proof ((rule allI)+; (rule impI)+)
    fix n m p v
    assume a0: "n \<in> ids g1"
    assume a1: "([g1,m,p] \<turnstile> n \<mapsto> v)"
    have "\<not>(\<exists>e. (g1 \<turnstile> n \<triangleright> e))"
      using this_is_true
      by (meson False a)
    then show "([g2,m,p] \<turnstile> n \<mapsto> v)" using a0 a1 a unfolding encodeeval_def
      by blast
  qed
qed
*)


text_raw \<open>\Snip{graph-semantics-preservation}
\begin{center}
@{thm[display, margin=30] graph_semantics_preservation [no_vars]}
\end{center}
\EndSnip\<close>

definition maximal_sharing:
  "maximal_sharing g = (\<forall> n1 n2 . n1 \<in> ids g \<and> n2 \<in> ids g \<longrightarrow> 
      (\<forall> e. (g \<turnstile> n1 \<triangleright> e) \<and> (g \<turnstile> n2 \<triangleright> e) \<longrightarrow> n1 = n2))"

text_raw \<open>\Snip{maximal-sharing}
@{thm[display, margin=50] maximal_sharing [no_vars]}
\EndSnip\<close>

lemma tree_to_graph_rewriting:
  "e1 \<le> e2 
  \<and> (g1 \<turnstile> n \<triangleright> e1) \<and> maximal_sharing g1
  \<and> ({n} \<unlhd> as_set g1) \<subseteq> as_set g2 
  \<and> (g2 \<turnstile> n \<triangleright> e2) \<and> maximal_sharing g2
  \<Longrightarrow> graph_refinement g1 g2"
  using graph_semantics_preservation by blast

text_raw \<open>\Snip{tree-to-graph-rewriting}
\begin{center}
@{thm[display, margin=40] tree_to_graph_rewriting [no_vars]}
\end{center}
\EndSnip\<close>

lemma graph_construction:
  "e1 \<le> e2
  \<and> as_set g1 \<subseteq> as_set g2
  \<and> maximal_sharing g1
  \<and> (g2 \<turnstile> n \<triangleright> e2)
  \<and> maximal_sharing g2
  \<Longrightarrow> graph_refinement g1 g2"
  by (smt (z3) IRExpr.simps(13) graph_refinement_def repDet)

text_raw \<open>\Snip{graph-construction}
\begin{center}
@{thm[display, margin=40] graph_construction [no_vars]}
\end{center}
\EndSnip\<close>

end