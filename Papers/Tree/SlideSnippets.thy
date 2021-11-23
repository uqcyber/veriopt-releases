theory SlideSnippets
imports Semantics.TreeToGraphThms
begin

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

notation (latex)
  IRTreeEval.ord_IRExpr_inst.less_eq_IRExpr ("_ \<longmapsto> _")

text_raw \<open>\Snip{abstract-syntax-tree}%
@{datatype[display,margin=40] IRExpr}
\EndSnip\<close>

text_raw \<open>\Snip{tree-semantics}%
\induct{@{thm[mode=Rule] evaltree.ConstantExpr [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] evaltree.ParameterExpr [no_vars]}}{semantics:parameter}
\induct{@{thm[mode=Rule] evaltree.UnaryExpr [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] evaltree.BinaryExpr [no_vars]}}{semantics:binary}
\induct{@{thm[mode=Rule] evaltree.LeafExpr [no_vars]}}{semantics:leaf}
\EndSnip\<close>

text_raw \<open>\Snip{expression-refinement}%
\begin{center}
@{thm le_expr_def [no_vars]} 
\end{center}
\EndSnip\<close>

text_raw \<open>\Snip{graph2tree}
\induct{@{thm[mode=Rule] rep.ConstantNode [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] rep.AbsNode [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] rep.AddNode [no_vars]}}{semantics:binary}
\EndSnip\<close>

text_raw \<open>\Snip{graph-semantics}
\begin{center}
@{thm encodeeval_def}
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

text_raw \<open>\Snip{graph-represents-expression}
\begin{center}
@{thm[display] graph_represents_expression_def [no_vars]}
\end{center}
\EndSnip\<close>

text_raw \<open>\Snip{graph-construction}
\begin{center}
@{thm[display, margin=40] graph_construction [no_vars]}
\end{center}
\EndSnip\<close>

end