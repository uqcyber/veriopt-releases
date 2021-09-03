theory TreeSnippets
  imports 
    Semantics.IRTreeEvalThms
    HOL.Relation
begin

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

notation (latex)
  IRTreeEval.ord_IRExpr_inst.less_eq_IRExpr ("_ \<longmapsto> _")

text_raw \<open>\Snip{abstract-syntax-tree}%
@{datatype[display,margin=45] IRExpr}
\EndSnip\<close>

text_raw \<open>\Snip{tree-semantics}%
\induct{@{thm[mode=Rule] evaltree.ConstantExpr [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] evaltree.ParameterExpr [no_vars]}}{semantics:parameter}
\induct{@{thm[mode=Rule] evaltree.ConditionalExpr [no_vars]}}{semantics:conditional}
\induct{@{thm[mode=Rule] evaltree.UnaryExpr [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] evaltree.ConvertExpr [no_vars]}}{semantics:convert}
\induct{@{thm[mode=Rule] evaltree.BinaryExpr [no_vars]}}{semantics:binary}
\induct{@{thm[mode=Rule] evaltree.LeafExpr [no_vars]}}{semantics:leaf}
\EndSnip\<close>

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
  "graph_refinement g1 g2 = (\<forall> nid \<in> ids g1. (\<exists> e. (g1 \<turnstile> nid \<triangleright> e) \<longrightarrow> 
        (\<forall>m p v. ([g1, m, p] \<turnstile> nid \<mapsto> v) \<longrightarrow> ([g2, m, p] \<turnstile> nid \<mapsto> v))))"

text_raw \<open>\Snip{graph-refinement}
\begin{center}
@{thm[display, margin=60] graph_refinement_def [no_vars]}
\end{center}
\EndSnip\<close>

definition as_set :: "IRGraph \<Rightarrow> (ID \<times> IRNode) set" where
  "as_set g = {(nid, kind g nid) | nid . nid \<in> ids g}"

(* hide as_set, should treat IRGraph as a set of pairs in paper *)
translations
  "n" <= "CONST as_set n"

definition domain_subtraction :: "'a set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set"
  (infix "\<unlhd>" 30) where
  "domain_subtraction s r = {(x, y) . (x, y) \<in> r | x \<notin> s}"

notation (latex)
  domain_subtraction ("_ \<^latex>\<open>$\\ndres$\<close> _")

lemma graph_semantics_preservation:
  "e1 \<le> e2 \<and> (g1 \<turnstile> nid \<triangleright> e1) \<and> (g2 \<turnstile> nid \<triangleright> e2) \<and> (({nid} \<unlhd> as_set g1) \<subseteq> as_set g2) \<Longrightarrow> graph_refinement g1 g2"
  by (smt (z3) IRExpr.simps(13) graph_refinement_def repDet)

text_raw \<open>\Snip{graph-semantics-preservation}
\begin{center}
@{thm[display, margin=30] graph_semantics_preservation [no_vars]}
\end{center}
\EndSnip\<close>

definition maximal_sharing:
  "maximal_sharing g = (\<forall> nid1 nid2 . nid1 \<in> ids g \<and> nid2 \<in> ids g \<longrightarrow> 
      (\<forall> e. (g \<turnstile> nid1 \<triangleright> e) \<and> (g \<turnstile> nid2 \<triangleright> e) \<longrightarrow> nid1 = nid2))"

text_raw \<open>\Snip{maximal-sharing}
@{thm[display, margin=50] maximal_sharing [no_vars]}
\EndSnip\<close>

lemma tree_to_graph_rewriting:
  "e1 \<le> e2 
  \<and> (g1 \<turnstile> nid \<triangleright> e1) \<and> maximal_sharing g1
  \<and> ({nid} \<unlhd> as_set g1) \<subseteq> as_set g2 
  \<and> (g2 \<turnstile> nid \<triangleright> e2) \<and> maximal_sharing g2
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
  \<and> (g2 \<turnstile> nid \<triangleright> e2)
  \<and> maximal_sharing g2
  \<Longrightarrow> graph_refinement g1 g2"
  by (smt (z3) IRExpr.simps(13) graph_refinement_def repDet)

text_raw \<open>\Snip{graph-construction}
\begin{center}
@{thm[display, margin=40] graph_construction [no_vars]}
\end{center}
\EndSnip\<close>

end