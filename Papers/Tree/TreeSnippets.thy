section \<open>Verifying term graph optimizations using Isabelle/HOL\<close>

theory TreeSnippets
  imports
    Canonicalizations.BinaryNode
    Canonicalizations.ConditionalPhase
    Canonicalizations.AddPhase
    Semantics.TreeToGraphThms
    Snippets.Snipping
    "HOL-Library.OptionalSugar"
begin

\<comment> \<open>First, we disable undesirable markup.\<close>
declare [[show_types=false,show_sorts=false]]
no_notation ConditionalExpr ("_ ? _ : _")


subsection \<open>Markup syntax for common operations\<close>

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

notation (latex)
  valid_value ("_ \<in> _")

notation (latex)
  val_to_bool ("\<^latex>\<open>bool-of\<close> _")

notation (latex)
  constantAsStamp ("\<^latex>\<open>stamp-from-value\<close> _")

notation (latex)
  size ("\<^latex>\<open>trm(\<close>_\<^latex>\<open>)\<close>")


subsection \<open>Representing canonicalization optimizations\<close>

text \<open>
We wish to provide an example of the semantics layers 
at which optimizations can be expressed.
\<close>

\<comment> \<open>Algebraic laws\<close>
lemma diff_self:
  fixes x :: int
  shows "x - x = 0"
  by simp
lemma diff_diff_cancel:
  fixes x y :: int
  shows "x - (x - y) = y"
  by simp
thm diff_self
thm diff_diff_cancel
snipbegin \<open>algebraic-laws\<close>
text \<open>\begin{align}
@{thm diff_self[show_types=false]}\\
@{thm diff_diff_cancel[show_types=false]}
\end{align}\<close>
snipend -

\<comment> \<open>Values\<close>
lemma diff_self_value: "\<forall>v::'a::len word. v - v = 0"
  by simp
lemma diff_diff_cancel_value:
  "\<forall> v\<^sub>1 v\<^sub>2::'a::len word . v\<^sub>1 - (v\<^sub>1 - v\<^sub>2) = v\<^sub>2"
  by simp

snipbegin \<open>algebraic-laws-values\<close>
text_raw \<open>\begin{align}
@{thm diff_self_value[show_types]} \label{prop-v-minus-v}\\
@{thm diff_diff_cancel_value[show_types]}
\end{align}\<close>
snipend -

\<comment> \<open>Expression\<close>
translations
  "n" <= "CONST ConstantExpr (CONST IntVal b n)"
  "x - y" <= "CONST BinaryExpr (CONST BinSub) x y"
notation (ExprRule output)
  Refines ("_ \<longmapsto> _")
lemma diff_self_expr:
  assumes "\<forall>m p v. [m,p] \<turnstile> exp[e - e] \<mapsto> IntVal b v"
  shows "exp[e - e] \<ge> exp[const (IntVal b 0)]"
  using assms apply simp
  by (metis(full_types) evalDet val_to_bool.simps(1) zero_neq_one)

lemma diff_diff_cancel_expr:
  shows "exp[e\<^sub>1 - (e\<^sub>1 - e\<^sub>2)] \<ge> exp[e\<^sub>2]"
  apply simp sorry

snipbegin \<open>algebraic-laws-expressions\<close>
text_raw \<open>\begin{align}
@{thm[mode=ExprRule] (concl) diff_self_expr} \label{prop-MinusSame} \\
@{thm[mode=ExprRule] (concl) diff_diff_cancel_expr}
\end{align}\<close>
snipend -
no_translations
  "n" <= "CONST ConstantExpr (CONST IntVal b n)"
  "x - y" <= "CONST BinaryExpr (CONST BinSub) x y"


definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

lemma wf_stamp_eval:
  assumes "wf_stamp e"
  assumes "stamp_expr e = IntegerStamp b lo hi"
  shows "\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> (\<exists>vv. v = IntVal b vv)"
  using assms unfolding wf_stamp_def
  using valid_int_same_bits valid_int
  by metis

phase SnipPhase
  terminating size
begin
lemma sub_same_val:
  assumes "val[e - e] = IntVal b v"
  shows "val[e - e] = val[IntVal b 0]"
  using assms by (cases e; auto)

snipbegin \<open>sub-same-32\<close>
optimization SubIdentity:
  "(e - e) \<longmapsto> ConstantExpr (IntVal b 0)
     when ((stamp_expr exp[e - e] = IntegerStamp b lo hi) \<and> wf_stamp exp[e - e])"
snipend -
  apply (rule impI) apply simp
proof -
  assume assms: "stamp_binary BinSub (stamp_expr e) (stamp_expr e) = IntegerStamp b lo hi \<and> wf_stamp exp[e - e]"
  have "\<forall>m p v . ([m, p] \<turnstile> exp[e - e] \<mapsto> v) \<longrightarrow> (\<exists>vv. v = IntVal b vv)"
    using assms wf_stamp_eval
    by (metis stamp_expr.simps(2))
  then show "\<forall>m p v. ([m,p] \<turnstile> BinaryExpr BinSub e e \<mapsto> v) \<longrightarrow> ([m,p] \<turnstile> ConstantExpr (IntVal b 0) \<mapsto> v)"
    by (smt (verit, best) BinaryExprE TreeSnippets.wf_stamp_def assms bin_eval.simps(3) constantAsStamp.simps(1) evalDet stamp_expr.simps(2) sub_same_val unfold_const valid_stamp.simps(1) valid_value.simps(1))
qed
thm_oracles SubIdentity
end

subsection \<open>Representing terms\<close>

text \<open>
We wish to show a simple example of expressions represented as terms.
\<close>

snipbegin \<open>ast-example\<close>
text "@{value[display,margin=40] \<open>BinaryExpr BinAdd (BinaryExpr BinMul x x) (BinaryExpr BinMul x x)\<close>}"
snipend -

text \<open>
Then we need to show the datatypes that compose the example expression.
\<close>

snipbegin \<open>abstract-syntax-tree\<close>
text \<open>@{datatype[display,margin=40] IRExpr}\<close>
snipend -

snipbegin \<open>value\<close>
text \<open>@{datatype[display,margin=40,show_abbrevs] Value}\<close>
snipend -


subsection \<open>Term semantics\<close>

text \<open>
The core expression evaluation functions need to be introduced.
\<close>

snipbegin \<open>eval\<close>
text \<open>@{term_type[mode=type_def] unary_eval}\\
@{term_type[mode=type_def] bin_eval}\<close>
snipend -

text \<open>
We then provide the full semantics of IR expressions.
\<close>

no_translations
  ("prop") "P \<and> Q \<Longrightarrow> R" <= ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R"
translations
  ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R" <= ("prop") "P \<and> Q \<Longrightarrow> R"
snipbegin \<open>tree-semantics\<close>
text \<open>
\induct{@{thm[mode=Rule] evaltree.UnaryExpr [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] evaltree.BinaryExpr [no_vars]}}{semantics:binary}
\induct{@{thm[mode=Rule] evaltree.ConditionalExpr [no_vars]}}{semantics:conditional}
\induct{@{thm[mode=Rule] evaltree.ConstantExpr [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] evaltree.ParameterExpr [no_vars]}}{semantics:parameter}
\induct{@{thm[mode=Rule] evaltree.LeafExpr [no_vars]}}{semantics:leaf}
\<close>
snipend -
no_translations
  ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R" <= ("prop") "P \<and> Q \<Longrightarrow> R"
translations
  ("prop") "P \<and> Q \<Longrightarrow> R" <= ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R"


text \<open>And show that expression evaluation is deterministic.\<close>

snipbegin \<open>tree-evaluation-deterministic\<close>
text \<open>@{thm[display] evalDet [no_vars]}\<close>
snipend -


text \<open>
We then want to start demonstrating the obligations for optimizations.
For this we define refinement over terms.
\<close>

snipbegin \<open>expression-refinement\<close>
text \<open>@{thm le_expr_def [no_vars]} \<close>
snipend -

text \<open>
To motivate this definition we show the obligations generated
by optimization definitions.
\<close>

phase SnipPhase
  terminating size
begin
snipbegin \<open>InverseLeftSub\<close>
optimization InverseLeftSub:
  "(e\<^sub>1 - e\<^sub>2) + e\<^sub>2 \<longmapsto> e\<^sub>1"
snipend -
  snipbegin \<open>InverseLeftSubObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -
  using RedundantSubAdd by auto

snipbegin \<open>InverseRightSub\<close>
optimization InverseRightSub: "e\<^sub>2 + (e\<^sub>1 - e\<^sub>2) \<longmapsto> e\<^sub>1"
snipend -
  snipbegin \<open>InverseRightSubObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -
  using RedundantSubAdd2(1) rewrite_preservation.simps(1) by blast
end

snipbegin \<open>expression-refinement-monotone\<close>
text \<open>@{thm[display,margin=60] mono_unary}
@{thm[display,margin=60] mono_binary}
@{thm[display,margin=60] mono_conditional}
\<close>
snipend -


phase SnipPhase 
  terminating size
begin
snipbegin \<open>BinaryFoldConstant\<close>
optimization BinaryFoldConstant: "BinaryExpr op (const v1) (const v2) \<longmapsto> ConstantExpr (bin_eval op v1 v2)"
snipend -
  snipbegin \<open>BinaryFoldConstantObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -
  using size_non_const apply auto[1]
  using BinaryFoldConstant(1) by auto

snipbegin \<open>AddCommuteConstantRight\<close>
optimization AddCommuteConstantRight:
  "((const v) + y) \<longmapsto> (y + (const v)) when \<not>(is_ConstantExpr y)"
snipend -
  snipbegin \<open>AddCommuteConstantRightObligation\<close>
  text \<open>@{subgoals[display,margin=50]}\<close>
  snipend -
  using AddShiftConstantRight by auto

snipbegin \<open>AddNeutral\<close>
optimization AddNeutral: "(e + (const (IntVal 32 0))) \<longmapsto> e"
snipend -
  snipbegin \<open>AddNeutralObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -
  using AddNeutral(1) rewrite_preservation.simps(1) by blast

snipbegin \<open>AddToSub\<close>
optimization AddToSub: "-e + y \<longmapsto> y - e"
snipend -
  snipbegin \<open>AddToSubObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -
  using AddLeftNegateToSub by auto

end

definition trm where "trm = size"

snipbegin \<open>phase\<close>
phase AddCanonicalizations
  terminating trm
begin
  text_raw "\\dots"
end
snipend -

hide_const (open) "Form.wf_stamp"

snipbegin \<open>phase-example\<close>
phase Conditional
  terminating trm
begin
snipend -

snipbegin \<open>phase-example-1\<close>optimization negate_condition: "((!e) ? x : y) \<longmapsto> (e ? y : x)"snipend -
  using ConditionalPhase.NegateConditionFlipBranches
   by (auto simp: trm_def)

snipbegin \<open>phase-example-2\<close>optimization const_true: "(true ? x : y) \<longmapsto> x"snipend -
  by (auto simp: trm_def)

snipbegin \<open>phase-example-3\<close>optimization const_false: "(false ? x : y) \<longmapsto> y"snipend -
  by (auto simp: trm_def)

snipbegin \<open>phase-example-4\<close>optimization equal_branches: "(e ? x : x) \<longmapsto> x"snipend -
  by (auto simp: trm_def)

snipbegin \<open>phase-example-5\<close>optimization condition_bounds_x: "((u < v) ? x : y) \<longmapsto> x
                   when (stamp_under (stamp_expr u) (stamp_expr v) 
                            \<and> wf_stamp u \<and> wf_stamp v)"snipend -
  apply (auto simp: trm_def)
  using ConditionalPhase.condition_bounds_x(1)
  by (metis(full_types) StampEvalThms.wf_stamp_def TreeSnippets.wf_stamp_def bin_eval.simps(12) stamp_under_defn)

snipbegin \<open>phase-example-6\<close>optimization condition_bounds_y: "((x < y) ? x : y) \<longmapsto> y
                   when (stamp_under (stamp_expr y) (stamp_expr x) \<and> wf_stamp x \<and> wf_stamp y)"snipend -
  apply (auto simp: trm_def)
  using ConditionalPhase.condition_bounds_y(1)
  by (metis(full_types) StampEvalThms.wf_stamp_def TreeSnippets.wf_stamp_def bin_eval.simps(12) stamp_under_defn_inverse)


snipbegin \<open>phase-example-7\<close>end snipend -

snipbegin \<open>termination\<close>
text \<open>
@{thm[display,margin=80] size.simps(1)}
@{thm[display,margin=80] size.simps(2)}
@{thm[display,margin=80] size.simps(7)}
@{thm[display,margin=80] size.simps(15)}
@{thm[display,margin=80] size.simps(16)}
@{thm[display,margin=80] size.simps(17)}
\<close>
snipend -


(* definition 5 (semantics-preserving) is there a distinction in Isabelle? *)

snipbegin \<open>graph-representation\<close>
text \<open>@{bold \<open>typedef\<close>} IRGraph = 

@{term[source] \<open>{g :: ID \<rightharpoonup> (IRNode \<times> Stamp) . finite (dom g)}\<close>}\<close>
snipend -

no_translations
  ("prop") "P \<and> Q \<Longrightarrow> R" <= ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R"
translations
  ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R" <= ("prop") "P \<and> Q \<Longrightarrow> R"
snipbegin \<open>graph2tree\<close>
text \<open>
\induct{@{thm[mode=Rule] rep.ConstantNode [no_vars]}}{rep:constant}
\induct{@{thm[mode=Rule] rep.ParameterNode [no_vars]}}{rep:parameter}
\induct{@{thm[mode=Rule] rep.ConditionalNode [no_vars]}}{rep:conditional}
\induct{@{thm[mode=Rule] rep.AbsNode [no_vars]}}{rep:unary}
\induct{@{thm[mode=Rule] rep.SignExtendNode [no_vars]}}{rep:convert}
\induct{@{thm[mode=Rule] rep.AddNode [no_vars]}}{rep:binary}
\induct{@{thm[mode=Rule] rep.LeafNode [no_vars]}}{rep:leaf}
\induct{@{thm[mode=Rule] rep.RefNode [no_vars]}}{rep:ref}
\<close>
snipend -
no_translations
  ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R" <= ("prop") "P \<and> Q \<Longrightarrow> R"
translations
  ("prop") "P \<and> Q \<Longrightarrow> R" <= ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R"


snipbegin \<open>preeval\<close>
text \<open>@{thm is_preevaluated.simps}\<close>
snipend -

snipbegin \<open>deterministic-representation\<close>
text \<open>@{thm[display] repDet [no_vars]}\<close>
snipend -
thm_oracles repDet

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
thm_oracles graphDet

notation (latex)
  graph_refinement ("\<^latex>\<open>term-graph-refinement\<close> _")

snipbegin \<open>graph-refinement\<close>
text \<open>@{thm[display, margin=60] graph_refinement_def [no_vars]}\<close>
snipend -

(* hide as_set, should treat IRGraph as a set of pairs in paper *)
translations
  "n" <= "CONST as_set n"

snipbegin \<open>graph-semantics-preservation\<close>
text \<open>@{thm[display, margin=30] graph_semantics_preservation_subscript [no_vars]}\<close>
snipend -
thm_oracles graph_semantics_preservation_subscript

snipbegin \<open>maximal-sharing\<close>
text \<open>@{thm[display, margin=50] maximal_sharing [no_vars]}\<close>
snipend -

snipbegin \<open>tree-to-graph-rewriting\<close>
text \<open>@{thm[display, margin=30] tree_to_graph_rewriting [no_vars]}\<close>
snipend -
thm_oracles tree_to_graph_rewriting

snipbegin \<open>term-graph-refines-term\<close>
text \<open>@{thm[display] graph_represents_expression_def [no_vars]}\<close>
snipend -

snipbegin \<open>term-graph-evaluation\<close>
text \<open>@{thm[display] term_graph_evaluation [no_vars]}\<close>
snipend -

snipbegin \<open>graph-construction\<close>
text \<open>@{thm[display, margin=40] graph_construction [no_vars]}\<close>
snipend -
thm_oracles graph_construction

snipbegin \<open>term-graph-reconstruction\<close>
text \<open>@{thm[display] term_graph_reconstruction [no_vars]}\<close>
snipend -

snipbegin \<open>refined-insert\<close>
text \<open>@{thm[display, margin=40] refined_insert [no_vars]}\<close>
snipend -

end
