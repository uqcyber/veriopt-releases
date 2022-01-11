theory TreeSnippets
  imports 
    Semantics.TreeToGraphThms
    Optimizations.CanonicalizationSyntax
    Veriopt.Snipping
    "HOL-Library.OptionalSugar"
begin

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

notation (latex)
  IRTreeEval.ord_IRExpr_inst.less_eq_IRExpr ("_ \<longmapsto> _")

notation (latex)
  valid_value ("_ \<subseteq> \<index>")

notation (latex)
  val_to_bool ("bool-of _")

notation (latex)
  constantAsStamp ("stamp-from-value _")


snipbegin \<open>ast-example\<close>
text "@{value[display,margin=25] \<open>BinaryExpr BinAdd (BinaryExpr BinMul x x) (BinaryExpr BinMul x x)\<close>}"
snipend -

snipbegin \<open>abstract-syntax-tree\<close>
text \<open>@{datatype[display,margin=40] IRExpr}\<close>
snipend -

snipbegin \<open>tree-semantics\<close>
text \<open>
\induct{@{thm[mode=Rule] evaltree.ConstantExpr [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] evaltree.ParameterExpr [no_vars]}}{semantics:parameter}
\induct{@{thm[mode=Rule] evaltree.ConditionalExpr [no_vars]}}{semantics:conditional}
\induct{@{thm[mode=Rule] evaltree.UnaryExpr [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] evaltree.BinaryExpr [no_vars]}}{semantics:binary}
\induct{@{thm[mode=Rule] evaltree.LeafExpr [no_vars]}}{semantics:leaf}
\<close>
snipend -
(*\induct{@{thm[mode=Rule] evaltree.ConvertExpr [no_vars]}}{semantics:convert}*)

snipbegin \<open>tree-evaluation-deterministic\<close>
text \<open>@{thm[display] evalDet [no_vars]}\<close>
snipend -

snipbegin \<open>expression-refinement\<close>
text \<open>@{thm le_expr_def [no_vars]} \<close>
snipend -

snipbegin \<open>expression-refinement-monotone\<close>
text \<open>
\begin{tabular}{l@ {~~@{text "\<Longrightarrow>"}~~}l}
@{thm (prem 1) mono_unary} & @{thm (concl) mono_unary}\\
@{thm (prem 1) mono_binary} @{text \<and>} @{thm (prem 2) mono_binary} & @{thm (concl) mono_binary}\\
@{thm (prem 1) mono_conditional} @{text \<and>} @{thm (prem 2) mono_conditional} @{text \<and>} @{thm (prem 3) mono_conditional} & @{thm (concl) mono_conditional}
\end{tabular}
\<close>
snipend -


(* Experimenting with auto generated optimizations
notation (latex)
  Transform ("_ \<^latex>\<open>&\<close> _")
notation (latex)
  Conditional ("_ \<^latex>\<open>&\<close>_\<^latex>\<open>\\\\\<close>\\ \<^latex>\<open>&\<close>if _")

translations
  "t" <= "CONST rewrite_obligation t"

print_optimizations
snipbegin \<open>optimization rules\<close>
text_raw \<open>\begin{tabular}{l@ {~~@{text "\<longmapsto>"}~~}l}\<close>
text_raw \<open>@{thm constant_add(1) [no_vars]}\\\<close>
text_raw \<open>@{thm AddShiftConstantRight(1) [no_vars]}\\\<close>
text_raw \<open>@{thm AddNeutral(1) [no_vars]}\<close>
text_raw \<open>\end{tabular}\<close>
snipend -
*)


(* definition 5 (semantics-preserving) is there a distinction in Isabelle? *)

snipbegin \<open>graph-representation\<close>
text \<open>@{bold \<open>typedef\<close>} @{term[source] \<open>IRGraph = {g :: ID \<rightharpoonup> (IRNode \<times> Stamp) . finite (dom g)}\<close>}\<close>
snipend -

snipbegin \<open>graph2tree\<close>
text \<open>
\induct{@{thm[mode=Rule] rep.ConstantNode [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] rep.ParameterNode [no_vars]}}{semantics:parameter}
\induct{@{thm[mode=Rule] rep.ConditionalNode [no_vars]}}{semantics:conditional}
\induct{@{thm[mode=Rule] rep.AbsNode [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] rep.SignExtendNode [no_vars]}}{semantics:convert}
\induct{@{thm[mode=Rule] rep.AddNode [no_vars]}}{semantics:binary}
\induct{@{thm[mode=Rule] rep.LeafNode [no_vars]}}{semantics:leaf}
\<close>
snipend -

snipbegin \<open>preeval\<close>
text \<open>@{thm is_preevaluated.simps}\<close>
snipend -

snipbegin \<open>deterministic-representation\<close>
text \<open>@{thm[display] repDet [no_vars]}\<close>
snipend -

snipbegin \<open>well-formed-term-graph\<close>
text "@{thm (rhs) wf_term_graph_def [no_vars]}"
snipend -

(* definition 9 (well-formed graph) no? *)

snipbegin \<open>graph-semantics\<close>
text \<open>@{thm encodeeval_def}\<close>
snipend -

snipbegin \<open>graph-semantics-deterministic\<close>
text \<open>@{thm graphDet [no_vars]}\<close>
snipend -

snipbegin \<open>graph-refinement\<close>
text \<open>@{thm[display, margin=60] graph_refinement_def [no_vars]}\<close>
snipend -

(* hide as_set, should treat IRGraph as a set of pairs in paper *)
translations
  "n" <= "CONST as_set n"

snipbegin \<open>graph-semantics-preservation\<close>
text \<open>@{thm[display, margin=30] graph_semantics_preservation [no_vars]}\<close>
snipend -

snipbegin \<open>maximal-sharing\<close>
text \<open>@{thm[display, margin=50] maximal_sharing [no_vars]}\<close>
snipend -

snipbegin \<open>tree-to-graph-rewriting\<close>
text \<open>@{thm[display, margin=30] tree_to_graph_rewriting [no_vars]}\<close>
snipend -

snipbegin \<open>term-graph-refines-term\<close>
text \<open>@{thm[display] graph_represents_expression_def [no_vars]}\<close>
snipend -

snipbegin \<open>graph-construction\<close>
text \<open>@{thm[display, margin=40] graph_construction [no_vars]}\<close>
snipend -


end
