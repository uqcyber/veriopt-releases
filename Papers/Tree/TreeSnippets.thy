theory TreeSnippets
  imports 
    Canonicalizations.ConditionalPhase
    Optimizations.CanonicalizationSyntax
    Semantics.TreeToGraphThms
    Snippets.Snipping
    "HOL-Library.OptionalSugar"
begin

no_notation ConditionalExpr ("_ ? _ : _")

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

translations
  "y > x" <= "x < y"

notation (latex)
  greater ("_ >/ _")

(* lengthen rewrite arrow slightly
notation (latex)
  Transform ("_ \<longmapsto> _")
notation (latex)
  Conditional ("_ \<longmapsto> _ \<^latex>\<open> when \<close> _")
*)

(* hide type casting *)
translations
  "n" <= "CONST Rep_intexp n"
  "n" <= "CONST Rep_i32exp n"
  "n" <= "CONST Rep_i64exp n"


lemma vminusv: "\<forall>vv v . vv = IntVal32 v \<longrightarrow> v - v = 0"
  by simp
thm_oracles vminusv

lemma vminusv2: "\<forall> v::int32 . v - v = 0"
  by simp

lemma redundant_sub:
  "\<forall>vv\<^sub>1 vv\<^sub>2 v\<^sub>1 v\<^sub>2 . vv\<^sub>1 = IntVal32 v\<^sub>1 \<and> vv\<^sub>2 = IntVal32 v\<^sub>2 \<longrightarrow> v\<^sub>1 - (v\<^sub>1 - v\<^sub>2) = v\<^sub>2"
  by simp
thm_oracles redundant_sub

lemma redundant_sub2:
  "\<forall> (v\<^sub>1::int32) (v\<^sub>2::int32) . v\<^sub>1 - (v\<^sub>1 - v\<^sub>2) = v\<^sub>2"
  by simp

snipbegin \<open>val-eq\<close>
text "@{thm vminusv}"
text "@{thm redundant_sub}"
snipend -

lemma sub_same_32_val:
  assumes "val[e - e] \<noteq> UndefVal"
  assumes "is_IntVal32 e"
  shows "val[e - e] = val[const 0]"
  using assms by (cases e; auto)

phase tmp
  terminating size
begin
snipbegin \<open>sub-same-32\<close>
optimization sub_same_32: "(e::i32exp) - e \<longmapsto> const (IntVal32 0)"
  snipend -
  defer apply simp using sub_same_32_val
  apply (metis Value.disc(2) bin_eval.simps(3) evalDet i32e_eval unfold_binary unfold_const32)
  unfolding size.simps
  by (metis add_strict_increasing gr_implies_not0 less_one linorder_not_le size_gt_0)

lemma sub_same_64_val:
  assumes "val[e - e] \<noteq> UndefVal"
  assumes "is_IntVal64 e"
  shows "val[e - e] = val[IntVal64 0]"
  using assms by (cases e; auto)

snipbegin \<open>sub-same-64\<close>
optimization sub_same_64: "(e::i64exp) - e \<longmapsto> const (IntVal64 0)"
  snipend -
  defer apply simp using sub_same_64_val
  apply (metis Value.discI(2) bin_eval.simps(3) evalDet i64e_eval unfold_binary unfold_const64)
  by (simp add: Suc_le_eq add_strict_increasing size_gt_0)
end

thm_oracles sub_same_32


snipbegin \<open>ast-example\<close>
text "@{value[display] \<open>BinaryExpr BinAdd (BinaryExpr BinMul x x) (BinaryExpr BinMul x x)\<close>}"
snipend -

snipbegin \<open>abstract-syntax-tree\<close>
text \<open>@{datatype[display,margin=40] IRExpr}\<close>
snipend -

snipbegin \<open>value\<close>
text \<open>@{datatype[display,margin=40] Value}\<close>
snipend -

snipbegin \<open>eval\<close>
text \<open>@{term_type[mode=spaced_type_def] unary_eval}\<close>
text \<open>@{term_type[mode=spaced_type_def] bin_eval}\<close>
snipend -

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
(*\induct{@{thm[mode=Rule] evaltree.ConvertExpr [no_vars]}}{semantics:convert}*)

snipbegin \<open>tree-evaluation-deterministic\<close>
text \<open>@{thm[display] evalDet [no_vars]}\<close>
snipend -

thm_oracles evalDet

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

ML \<open>
(*fun get_list (phase: phase option) =
  case phase of
    NONE => [] |
    SOME p => (#rewrites p)

fun get_rewrite name thy =
  let 
    val (phases, lookup) = (case RWList.get thy of
      NoPhase store => store |
      InPhase (name, store, _) => store)
    val rewrites = (map (fn x => get_list (lookup x)) phases)
  in
    rewrites
  end
  
fun rule_print name =
  Document_Output.antiquotation_pretty name (Args.term)
    (fn ctxt => fn (rule) => (*Pretty.str "hello")*)
      Pretty.block (print_all_phases (Proof_Context.theory_of ctxt)));
(*
      Goal_Display.pretty_goal
        (Config.put Goal_Display.show_main_goal main ctxt)
        (#goal (Proof.goal (Toplevel.proof_of (Toplevel.presentation_state ctxt)))));
*)

val _ = Theory.setup
 (rule_print \<^binding>\<open>rule\<close>);*)
\<close>


(*snipbegin \<open>OptimizationList\<close>
text \<open>@{rule BinaryFoldConstant}\<close>
snipend -*)

phase SnipPhase 
  terminating size
begin
snipbegin \<open>BinaryFoldConstant\<close>
optimization BinaryFoldConstant: "BinaryExpr op (const v1) (const v2) \<longmapsto> ConstantExpr (bin_eval op v1 v2) when int_and_equal_bits v1 v2 "
snipend -

  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  snipbegin \<open>BinaryFoldConstantObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -

  using BinaryFoldConstant by auto

snipbegin \<open>AddCommuteConstantRight\<close>
optimization AddCommuteConstantRight: "((const v) + y) \<longmapsto> y + (const v) when \<not>(is_ConstantExpr y)"
snipend -

  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  snipbegin \<open>AddCommuteConstantRightObligation\<close>
  text \<open>@{subgoals[display,margin=50]}\<close>
  snipend -

  using AddShiftConstantRight by auto

snipbegin \<open>AddNeutral\<close>
optimization AddNeutral: "((e::i32exp) + (const (IntVal32 0))) \<longmapsto> e"
snipend -

  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  snipbegin \<open>AddNeutralObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -

  using neutral_zero(1) rewrite_preservation.simps(1) by blast

snipbegin \<open>InverseLeftSub\<close>
optimization InverseLeftSub: "((e\<^sub>1::intexp) - (e\<^sub>2::intexp)) + e\<^sub>2 \<longmapsto> e\<^sub>1"
snipend -

  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  snipbegin \<open>InverseLeftSubObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -

  using neutral_left_add_sub by auto

snipbegin \<open>InverseRightSub\<close>
optimization InverseRightSub: "(e\<^sub>2::intexp) + ((e\<^sub>1::intexp) - e\<^sub>2) \<longmapsto> e\<^sub>1"
snipend -

  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  snipbegin \<open>InverseRightSubObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -

  using neutral_right_add_sub by auto

snipbegin \<open>AddToSub\<close>
optimization AddToSub: "-e + y \<longmapsto> y - e"
snipend -


  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
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
  using ConditionalPhase.negate_condition
   by (auto simp: trm_def)

snipbegin \<open>phase-example-2\<close>optimization const_true: "(true ? x : y) \<longmapsto> x"snipend -
  by (auto simp: trm_def)

snipbegin \<open>phase-example-3\<close>optimization const_false: "(false ? x : y) \<longmapsto> y"snipend -
  by (auto simp: trm_def)

snipbegin \<open>phase-example-4\<close>optimization equal_branches: "(e ? x : x) \<longmapsto> x"snipend -
  by (auto simp: trm_def)

(*
snipbegin \<open>phase-example-5\<close>optimization condition_bounds_x: "((u < v) ? x : y) \<longmapsto> x
                   when (stamp_under (stamp_expr u) (stamp_expr v) 
                            \<and> wf_stamp u \<and> wf_stamp v)"snipend -
  using ConditionalPhase.condition_bounds_x(1)
  by (blast, auto simp: trm_def)

snipbegin \<open>phase-example-6\<close>optimization condition_bounds_y: "((x < y) ? x : y) \<longmapsto> y
                   when (stamp_under (stamp_expr y) (stamp_expr x) \<and> wf_stamp x \<and> wf_stamp y)"snipend -
  using ConditionalPhase.condition_bounds_y(1)
  by (blast, auto simp: trm_def)
*)

snipbegin \<open>phase-example-7\<close>end snipend -

snipbegin \<open>termination\<close>
text \<open>\begin{tabular}{l@ {~~@{text "="}~~}l}
@{thm (lhs) size.simps(1)} & @{thm (rhs) size.simps(1)}\\
@{thm (lhs) size.simps(2)} & @{thm (rhs) size.simps(2)}\\
@{thm (lhs) size.simps(14)} & @{thm (rhs) size.simps(14)}\\
@{thm (lhs) size.simps(15)} & @{thm (rhs) size.simps(15)}\\
@{thm (lhs) size.simps(16)} & @{thm (rhs) size.simps(16)}\\
@{thm (lhs) size.simps(17)} & @{thm (rhs) size.simps(17)}
\end{tabular}\<close>
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
