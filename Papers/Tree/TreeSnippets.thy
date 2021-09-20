theory TreeSnippets
  imports 
    Semantics.TreeToGraphThms
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

text_raw \<open>\Snip{graph-refinement}
\begin{center}
@{thm[display, margin=60] graph_refinement_def [no_vars]}
\end{center}
\EndSnip\<close>

(* hide as_set, should treat IRGraph as a set of pairs in paper *)
translations
  "n" <= "CONST as_set n"



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

text_raw \<open>\Snip{graph-semantics-preservation}
\begin{center}
@{thm[display, margin=30] graph_semantics_preservation [no_vars]}
\end{center}
\EndSnip\<close>

text_raw \<open>\Snip{maximal-sharing}
@{thm[display, margin=50] maximal_sharing [no_vars]}
\EndSnip\<close>

text_raw \<open>\Snip{tree-to-graph-rewriting}
\begin{center}
@{thm[display, margin=40] tree_to_graph_rewriting [no_vars]}
\end{center}
\EndSnip\<close>

text_raw \<open>\Snip{graph-construction}
\begin{center}
@{thm[display, margin=40] graph_construction [no_vars]}
\end{center}
\EndSnip\<close>


end
