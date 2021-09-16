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

text_raw \<open>\Snip{expression-refinement-monotone}%
\begin{center}
@{thm mono_unary [no_vars]} \\
@{thm mono_binary [no_vars]} \\
@{thm mono_conditional [no_vars]}
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
  assumes "kind g1 n = NarrowNode ib rb x \<and> kind g2 n = NarrowNode ib rb x"
  assumes "(g1 \<turnstile> x \<triangleright> xe1) \<and> (g2 \<turnstile> x \<triangleright> xe2)"
  assumes "xe1 \<le> xe2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  using assms mono_unary repDet NarrowNode
  by metis

lemma mono_sign_extend:
  assumes "kind g1 n = SignExtendNode ib rb x \<and> kind g2 n = SignExtendNode ib rb x"
  assumes "(g1 \<turnstile> x \<triangleright> xe1) \<and> (g2 \<turnstile> x \<triangleright> xe2)"
  assumes "xe1 \<le> xe2"
  assumes "(g1 \<turnstile> n \<triangleright> e1) \<and> (g2 \<turnstile> n \<triangleright> e2)"
  shows "e1 \<le> e2"
  by (metis SignExtendNode assms(1) assms(2) assms(3) assms(4) mono_unary repDet)

lemma mono_zero_extend:
  assumes "kind g1 n = ZeroExtendNode ib rb x \<and> kind g2 n = ZeroExtendNode ib rb x"
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

definition is_convert_node :: "IRNode \<Rightarrow> bool" where
  "is_convert_node n = ((is_NarrowNode n) \<or> (is_SignExtendNode n) \<or> (is_ZeroExtendNode n))"

experiment begin
text \<open>Experimental embedding into a simplier but usable form for expression nodes in a graph\<close>

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
  "embed_expr (NarrowNode ib rb x) = ExprUnaryNode (UnaryNarrow ib rb) x" |
  "embed_expr (SignExtendNode ib rb x) = ExprUnaryNode (UnarySignExtend ib rb) x" |
  "embed_expr (ZeroExtendNode ib rb x) = ExprUnaryNode (UnaryZeroExtend ib rb) x" |
  "embed_expr _ = NotExpr"

lemma unary_embed:
  assumes "g \<turnstile> n \<triangleright> UnaryExpr op x"
  shows "\<exists> x' . embed_expr (kind g n) = ExprUnaryNode op x'"
  using assms by (induction "UnaryExpr op x" rule: rep.induct; simp)

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
  using NarrowNode apply presburger
  using rep.NegateNode apply blast
  using rep.NotNode apply blast
  using rep.SignExtendNode apply blast
  using rep.ZeroExtendNode by blast
end


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


lemma no_encoding:
  assumes "n \<notin> ids g"
  shows "\<not>(g \<turnstile> n \<triangleright> e)"
  using assms apply simp apply (rule notI) by (induction e; simp add: encodes_contains)

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
    show ?thesis using f i
    proof (induction e1)
      case (ConstantNode n c)
      then show ?case
        by (metis eq_refl rep.ConstantNode)
    next
      case (ParameterNode n i s)
      then show ?case
        by (metis eq_refl rep.ParameterNode)
    next
      case (ConditionalNode n c t f ce1 te1 fe1)
      have k: "g1 \<turnstile> n \<triangleright> ConditionalExpr ce1 te1 fe1" using f ConditionalNode
        by (simp add: ConditionalNode.hyps(2) rep.ConditionalNode)
      obtain cn tn fn where l: "kind g1 n = ConditionalNode cn tn fn"
        using ConditionalNode.hyps(1) by blast
      then have mc: "g1 \<turnstile> cn \<triangleright> ce1"
        using ConditionalNode.hyps(1) ConditionalNode.hyps(2) by fastforce
      from l have mt: "g1 \<turnstile> tn \<triangleright> te1"
        using ConditionalNode.hyps(1) ConditionalNode.hyps(3) by fastforce
      from l have mf: "g1 \<turnstile> fn \<triangleright> fe1"
        using ConditionalNode.hyps(1) ConditionalNode.hyps(4) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> cn \<triangleright> ce1" using mc by simp
        have "g1 \<turnstile> tn \<triangleright> te1" using mt by simp
        have "g1 \<turnstile> fn \<triangleright> fe1" using mf by simp
        have cer: "\<exists> ce2. (g2 \<turnstile> cn \<triangleright> ce2) \<and> ce1 \<le> ce2"
          using ConditionalNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(6))
        have ter: "\<exists> te2. (g2 \<turnstile> tn \<triangleright> te2) \<and> te1 \<le> te2"
          using ConditionalNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(6))
        have "\<exists> fe2. (g2 \<turnstile> fn \<triangleright> fe2) \<and> fe1 \<le> fe2"
          using ConditionalNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(6))
        then have "\<exists> ce2 te2 fe2. (g2 \<turnstile> n \<triangleright> ConditionalExpr ce2 te2 fe2) \<and> ConditionalExpr ce1 te1 fe1 \<le> ConditionalExpr ce2 te2 fe2"
          using ConditionalNode.prems l mono_conditional rep.ConditionalNode cer ter
          by (smt (verit) IRTreeEvalThms.mono_conditional)
        then show ?thesis
          by meson
      qed
    next
      case (AbsNode n x xe1)
      have k: "g1 \<turnstile> n \<triangleright> UnaryExpr UnaryAbs xe1" using f AbsNode
        by (simp add: AbsNode.hyps(2) rep.AbsNode)
      obtain xn where l: "kind g1 n = AbsNode xn"
        using AbsNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<triangleright> xe1"
        using AbsNode.hyps(1) AbsNode.hyps(2) by fastforce
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<triangleright> UnaryExpr UnaryAbs e2'" using AbsNode.hyps(1) l m n
          using AbsNode.prems True d rep.AbsNode by simp
        then have r: "UnaryExpr UnaryAbs e1' \<le> UnaryExpr UnaryAbs e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<triangleright> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using AbsNode
          by (metis False IRNode.inject(1) b encodes_contains l not_excluded_keep_type not_in_g singleton_iff)
        then have "\<exists> xe2. (g2 \<turnstile> n \<triangleright> UnaryExpr UnaryAbs xe2) \<and> UnaryExpr UnaryAbs xe1 \<le> UnaryExpr UnaryAbs xe2"
          by (metis AbsNode.prems l mono_unary rep.AbsNode)
        then show ?thesis
          by meson
      qed
    next
      case (NotNode n x xe1)
      have k: "g1 \<turnstile> n \<triangleright> UnaryExpr UnaryNot xe1" using f NotNode
        by (simp add: NotNode.hyps(2) rep.NotNode)
      obtain xn where l: "kind g1 n = NotNode xn"
        using NotNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<triangleright> xe1"
        using NotNode.hyps(1) NotNode.hyps(2) by fastforce
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<triangleright> UnaryExpr UnaryNot e2'" using NotNode.hyps(1) l m n
          using NotNode.prems True d rep.NotNode by simp
        then have r: "UnaryExpr UnaryNot e1' \<le> UnaryExpr UnaryNot e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<triangleright> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using NotNode
          by (metis False IRNode.inject(31) b l not_excluded_keep_type singletonD no_encoding)
        then have "\<exists> xe2. (g2 \<turnstile> n \<triangleright> UnaryExpr UnaryNot xe2) \<and> UnaryExpr UnaryNot xe1 \<le> UnaryExpr UnaryNot xe2"
          by (metis NotNode.prems l mono_unary rep.NotNode)
        then show ?thesis
          by meson
      qed
    next
      case (NegateNode n x xe1)
      have k: "g1 \<turnstile> n \<triangleright> UnaryExpr UnaryNeg xe1" using f NegateNode
        by (simp add: NegateNode.hyps(2) rep.NegateNode)
      obtain xn where l: "kind g1 n = NegateNode xn"
        using NegateNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<triangleright> xe1"
        using NegateNode.hyps(1) NegateNode.hyps(2) by fastforce
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<triangleright> UnaryExpr UnaryNeg e2'" using NegateNode.hyps(1) l m n
          using NegateNode.prems True d rep.NegateNode by simp
        then have r: "UnaryExpr UnaryNeg e1' \<le> UnaryExpr UnaryNeg e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<triangleright> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using NegateNode
          by (metis False IRNode.inject(28) b l not_excluded_keep_type singleton_iff no_encoding)
        then have "\<exists> xe2. (g2 \<turnstile> n \<triangleright> UnaryExpr UnaryNeg xe2) \<and> UnaryExpr UnaryNeg xe1 \<le> UnaryExpr UnaryNeg xe2"
          by (metis NegateNode.prems l mono_unary rep.NegateNode)
        then show ?thesis
          by meson
      qed
    next
      case (LogicNegationNode n x xe1)
      have k: "g1 \<turnstile> n \<triangleright> UnaryExpr UnaryLogicNegation xe1" using f LogicNegationNode
        by (simp add: LogicNegationNode.hyps(2) rep.LogicNegationNode)
      obtain xn where l: "kind g1 n = LogicNegationNode xn"
        using LogicNegationNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<triangleright> xe1"
        using LogicNegationNode.hyps(1) LogicNegationNode.hyps(2) by fastforce
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<triangleright> UnaryExpr UnaryLogicNegation e2'" using LogicNegationNode.hyps(1) l m n
          using LogicNegationNode.prems True d rep.LogicNegationNode by simp
        then have r: "UnaryExpr UnaryLogicNegation e1' \<le> UnaryExpr UnaryLogicNegation e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<triangleright> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using LogicNegationNode
          by (metis False IRNode.inject(20) b encodes_contains ids_some l not_excluded_keep_type singleton_iff)
        then have "\<exists> xe2. (g2 \<turnstile> n \<triangleright> UnaryExpr UnaryLogicNegation xe2) \<and> UnaryExpr UnaryLogicNegation xe1 \<le> UnaryExpr UnaryLogicNegation xe2"
          by (metis LogicNegationNode.prems l mono_unary rep.LogicNegationNode)
        then show ?thesis
          by meson
      qed
    next
      case (AddNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<triangleright> BinaryExpr BinAdd xe1 ye1" using f AddNode
        by (simp add: AddNode.hyps(2) rep.AddNode)
      obtain xn yn where l: "kind g1 n = AddNode xn yn"
        using AddNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<triangleright> xe1"
        using AddNode.hyps(1) AddNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<triangleright> ye1"
        using AddNode.hyps(1) AddNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<triangleright> xe1" using mx by simp
        have "g1 \<turnstile> yn \<triangleright> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using AddNode
          by (metis IRNode.inject(2) a b c d l no_encoding not_excluded_keep_type repDet singletonD)
        have "\<exists> ye2. (g2 \<turnstile> yn \<triangleright> ye2) \<and> ye1 \<le> ye2"
          using AddNode
          by (metis IRNode.inject(2) a b c d l no_encoding not_excluded_keep_type repDet singletonD)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<triangleright> BinaryExpr BinAdd xe2 ye2) \<and> BinaryExpr BinAdd xe1 ye1 \<le> BinaryExpr BinAdd xe2 ye2"
          by (metis AddNode.prems l mono_binary rep.AddNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (MulNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<triangleright> BinaryExpr BinMul xe1 ye1" using f MulNode
        by (simp add: MulNode.hyps(2) rep.MulNode)
      obtain xn yn where l: "kind g1 n = MulNode xn yn"
        using MulNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<triangleright> xe1"
        using MulNode.hyps(1) MulNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<triangleright> ye1"
        using MulNode.hyps(1) MulNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<triangleright> xe1" using mx by simp
        have "g1 \<turnstile> yn \<triangleright> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using MulNode
          by (metis IRNode.inject(26) a b c d l no_encoding not_excluded_keep_type repDet singletonD)
        have "\<exists> ye2. (g2 \<turnstile> yn \<triangleright> ye2) \<and> ye1 \<le> ye2"
          using MulNode
          by (metis IRNode.inject(26) a b c d l no_encoding not_excluded_keep_type repDet singletonD)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<triangleright> BinaryExpr BinMul xe2 ye2) \<and> BinaryExpr BinMul xe1 ye1 \<le> BinaryExpr BinMul xe2 ye2"
          by (metis MulNode.prems l mono_binary rep.MulNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (SubNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<triangleright> BinaryExpr BinSub xe1 ye1" using f SubNode
        by (simp add: SubNode.hyps(2) rep.SubNode)
      obtain xn yn where l: "kind g1 n = SubNode xn yn"
        using SubNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<triangleright> xe1"
        using SubNode.hyps(1) SubNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<triangleright> ye1"
        using SubNode.hyps(1) SubNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<triangleright> xe1" using mx by simp
        have "g1 \<turnstile> yn \<triangleright> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using SubNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(42))
        have "\<exists> ye2. (g2 \<turnstile> yn \<triangleright> ye2) \<and> ye1 \<le> ye2"
          using SubNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(42))
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<triangleright> BinaryExpr BinSub xe2 ye2) \<and> BinaryExpr BinSub xe1 ye1 \<le> BinaryExpr BinSub xe2 ye2"
          by (metis SubNode.prems l mono_binary rep.SubNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (AndNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<triangleright> BinaryExpr BinAnd xe1 ye1" using f AndNode
        by (simp add: AndNode.hyps(2) rep.AndNode)
      obtain xn yn where l: "kind g1 n = AndNode xn yn"
        using AndNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<triangleright> xe1"
        using AndNode.hyps(1) AndNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<triangleright> ye1"
        using AndNode.hyps(1) AndNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<triangleright> xe1" using mx by simp
        have "g1 \<turnstile> yn \<triangleright> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using AndNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(3))
        have "\<exists> ye2. (g2 \<turnstile> yn \<triangleright> ye2) \<and> ye1 \<le> ye2"
          using AndNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(3))
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<triangleright> BinaryExpr BinAnd xe2 ye2) \<and> BinaryExpr BinAnd xe1 ye1 \<le> BinaryExpr BinAnd xe2 ye2"
          by (metis AndNode.prems l mono_binary rep.AndNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (OrNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<triangleright> BinaryExpr BinOr xe1 ye1" using f OrNode
        by (simp add: OrNode.hyps(2) rep.OrNode)
      obtain xn yn where l: "kind g1 n = OrNode xn yn"
        using OrNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<triangleright> xe1"
        using OrNode.hyps(1) OrNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<triangleright> ye1"
        using OrNode.hyps(1) OrNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<triangleright> xe1" using mx by simp
        have "g1 \<turnstile> yn \<triangleright> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using OrNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(32))
        have "\<exists> ye2. (g2 \<turnstile> yn \<triangleright> ye2) \<and> ye1 \<le> ye2"
          using OrNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(32))
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<triangleright> BinaryExpr BinOr xe2 ye2) \<and> BinaryExpr BinOr xe1 ye1 \<le> BinaryExpr BinOr xe2 ye2"
          by (metis OrNode.prems l mono_binary rep.OrNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (XorNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<triangleright> BinaryExpr BinXor xe1 ye1" using f XorNode
        by (simp add: XorNode.hyps(2) rep.XorNode)
      obtain xn yn where l: "kind g1 n = XorNode xn yn"
        using XorNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<triangleright> xe1"
        using XorNode.hyps(1) XorNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<triangleright> ye1"
        using XorNode.hyps(1) XorNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<triangleright> xe1" using mx by simp
        have "g1 \<turnstile> yn \<triangleright> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using XorNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(46))
        have "\<exists> ye2. (g2 \<turnstile> yn \<triangleright> ye2) \<and> ye1 \<le> ye2"
          using XorNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(46))
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<triangleright> BinaryExpr BinXor xe2 ye2) \<and> BinaryExpr BinXor xe1 ye1 \<le> BinaryExpr BinXor xe2 ye2"
          by (metis XorNode.prems l mono_binary rep.XorNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerBelowNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<triangleright> BinaryExpr BinIntegerBelow xe1 ye1" using f IntegerBelowNode
        by (simp add: IntegerBelowNode.hyps(2) rep.IntegerBelowNode)
      obtain xn yn where l: "kind g1 n = IntegerBelowNode xn yn"
        using IntegerBelowNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<triangleright> xe1"
        using IntegerBelowNode.hyps(1) IntegerBelowNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<triangleright> ye1"
        using IntegerBelowNode.hyps(1) IntegerBelowNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<triangleright> xe1" using mx by simp
        have "g1 \<turnstile> yn \<triangleright> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using IntegerBelowNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(12))
        have "\<exists> ye2. (g2 \<turnstile> yn \<triangleright> ye2) \<and> ye1 \<le> ye2"
          using IntegerBelowNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(12))
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<triangleright> BinaryExpr BinIntegerBelow xe2 ye2) \<and> BinaryExpr BinIntegerBelow xe1 ye1 \<le> BinaryExpr BinIntegerBelow xe2 ye2"
          by (metis IntegerBelowNode.prems l mono_binary rep.IntegerBelowNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerEqualsNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<triangleright> BinaryExpr BinIntegerEquals xe1 ye1" using f IntegerEqualsNode
        by (simp add: IntegerEqualsNode.hyps(2) rep.IntegerEqualsNode)
      obtain xn yn where l: "kind g1 n = IntegerEqualsNode xn yn"
        using IntegerEqualsNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<triangleright> xe1"
        using IntegerEqualsNode.hyps(1) IntegerEqualsNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<triangleright> ye1"
        using IntegerEqualsNode.hyps(1) IntegerEqualsNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<triangleright> xe1" using mx by simp
        have "g1 \<turnstile> yn \<triangleright> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using IntegerEqualsNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(13))
        have "\<exists> ye2. (g2 \<turnstile> yn \<triangleright> ye2) \<and> ye1 \<le> ye2"
          using IntegerEqualsNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(13))
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<triangleright> BinaryExpr BinIntegerEquals xe2 ye2) \<and> BinaryExpr BinIntegerEquals xe1 ye1 \<le> BinaryExpr BinIntegerEquals xe2 ye2"
          by (metis IntegerEqualsNode.prems l mono_binary rep.IntegerEqualsNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerLessThanNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<triangleright> BinaryExpr BinIntegerLessThan xe1 ye1" using f IntegerLessThanNode
        by (simp add: IntegerLessThanNode.hyps(2) rep.IntegerLessThanNode)
      obtain xn yn where l: "kind g1 n = IntegerLessThanNode xn yn"
        using IntegerLessThanNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<triangleright> xe1"
        using IntegerLessThanNode.hyps(1) IntegerLessThanNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<triangleright> ye1"
        using IntegerLessThanNode.hyps(1) IntegerLessThanNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<triangleright> xe1" using mx by simp
        have "g1 \<turnstile> yn \<triangleright> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using IntegerLessThanNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(14))
        have "\<exists> ye2. (g2 \<turnstile> yn \<triangleright> ye2) \<and> ye1 \<le> ye2"
          using IntegerLessThanNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(14))
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<triangleright> BinaryExpr BinIntegerLessThan xe2 ye2) \<and> BinaryExpr BinIntegerLessThan xe1 ye1 \<le> BinaryExpr BinIntegerLessThan xe2 ye2"
          by (metis IntegerLessThanNode.prems l mono_binary rep.IntegerLessThanNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (NarrowNode n inputBits resultBits x xe1)
      have k: "g1 \<turnstile> n \<triangleright> UnaryExpr (UnaryNarrow inputBits resultBits) xe1" using f NarrowNode
        by (simp add: NarrowNode.hyps(2) rep.NarrowNode)
      obtain xn where l: "kind g1 n = NarrowNode inputBits resultBits xn"
        using NarrowNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<triangleright> xe1"
        using NarrowNode.hyps(1) NarrowNode.hyps(2)
        by auto
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<triangleright> UnaryExpr (UnaryNarrow inputBits resultBits) e2'" using NarrowNode.hyps(1) l m n
          using NarrowNode.prems True d rep.NarrowNode by simp
        then have r: "UnaryExpr (UnaryNarrow inputBits resultBits) e1' \<le> UnaryExpr (UnaryNarrow inputBits resultBits) e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<triangleright> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using NarrowNode
          by (metis False IRNode.inject(27) b encodes_contains l not_excluded_keep_type not_in_g singleton_iff)
        then have "\<exists> xe2. (g2 \<turnstile> n \<triangleright> UnaryExpr (UnaryNarrow inputBits resultBits) xe2) \<and> UnaryExpr (UnaryNarrow inputBits resultBits) xe1 \<le> UnaryExpr (UnaryNarrow inputBits resultBits) xe2"
          by (metis NarrowNode.prems l mono_unary rep.NarrowNode)
        then show ?thesis
          by meson
      qed
    next
      case (SignExtendNode n inputBits resultBits x xe1)
      have k: "g1 \<turnstile> n \<triangleright> UnaryExpr (UnarySignExtend inputBits resultBits) xe1" using f SignExtendNode
        by (simp add: SignExtendNode.hyps(2) rep.SignExtendNode)
      obtain xn where l: "kind g1 n = SignExtendNode inputBits resultBits xn"
        using SignExtendNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<triangleright> xe1"
        using SignExtendNode.hyps(1) SignExtendNode.hyps(2)
        by auto
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<triangleright> UnaryExpr (UnarySignExtend inputBits resultBits) e2'" using SignExtendNode.hyps(1) l m n
          using SignExtendNode.prems True d rep.SignExtendNode by simp
        then have r: "UnaryExpr (UnarySignExtend inputBits resultBits) e1' \<le> UnaryExpr (UnarySignExtend inputBits resultBits) e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<triangleright> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using SignExtendNode
          by (metis False IRNode.inject(37) b encodes_contains l not_excluded_keep_type not_in_g singleton_iff)
        then have "\<exists> xe2. (g2 \<turnstile> n \<triangleright> UnaryExpr (UnarySignExtend inputBits resultBits) xe2) \<and> UnaryExpr (UnarySignExtend inputBits resultBits) xe1 \<le> UnaryExpr (UnarySignExtend inputBits resultBits) xe2"
          by (metis SignExtendNode.prems l mono_unary rep.SignExtendNode)
        then show ?thesis
          by meson
      qed
    next
      case (ZeroExtendNode n inputBits resultBits x xe1)
      have k: "g1 \<turnstile> n \<triangleright> UnaryExpr (UnaryZeroExtend inputBits resultBits) xe1" using f ZeroExtendNode
        by (simp add: ZeroExtendNode.hyps(2) rep.ZeroExtendNode)
      obtain xn where l: "kind g1 n = ZeroExtendNode inputBits resultBits xn"
        using ZeroExtendNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<triangleright> xe1"
        using ZeroExtendNode.hyps(1) ZeroExtendNode.hyps(2)
        by auto
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<triangleright> UnaryExpr (UnaryZeroExtend inputBits resultBits) e2'" using ZeroExtendNode.hyps(1) l m n
          using ZeroExtendNode.prems True d rep.ZeroExtendNode by simp
        then have r: "UnaryExpr (UnaryZeroExtend inputBits resultBits) e1' \<le> UnaryExpr (UnaryZeroExtend inputBits resultBits) e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<triangleright> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<triangleright> xe2) \<and> xe1 \<le> xe2"
          using ZeroExtendNode
          by (metis False IRNode.inject(47) b encodes_contains l not_excluded_keep_type not_in_g singleton_iff)
        then have "\<exists> xe2. (g2 \<turnstile> n \<triangleright> UnaryExpr (UnaryZeroExtend inputBits resultBits) xe2) \<and> UnaryExpr (UnaryZeroExtend inputBits resultBits) xe1 \<le> UnaryExpr (UnaryZeroExtend inputBits resultBits) xe2"
          by (metis ZeroExtendNode.prems l mono_unary rep.ZeroExtendNode)
        then show ?thesis
          by meson
      qed
    next
      case (LeafNode n s)
    then show ?case
      by (metis eq_refl rep.LeafNode)
    qed
  qed
qed
      





(*
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
*)

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
      using no_encoding
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
  using graph_semantics_preservation
  by auto

text_raw \<open>\Snip{tree-to-graph-rewriting}
\begin{center}
@{thm[display, margin=40] tree_to_graph_rewriting [no_vars]}
\end{center}
\EndSnip\<close>

(*
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
*)

end
