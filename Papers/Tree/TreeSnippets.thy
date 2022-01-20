theory TreeSnippets
  imports 
    Semantics.TreeToGraphThms
    Optimizations.CanonicalizationSyntax
    Veriopt.Snipping
    "HOL-Library.OptionalSugar"
begin

no_notation ConditionalExpr ("_ ? _ : _")

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

notation (latex)
  IRTreeEval.ord_IRExpr_inst.less_eq_IRExpr ("_ \<longmapsto> _")

notation (latex)
  valid_value ("_ \<in> _")

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

notation (latex)
  size ("\<^latex>\<open>trm(\<close>_\<^latex>\<open>)\<close>")

phase SnipPhase 
  trm size
begin
snipbegin \<open>BinaryFoldConstant\<close>
optimization BinaryFoldConstant: "BinaryExpr op c1 c2 \<mapsto> ConstantExpr (bin_eval op val_c1 val_c2) when int_and_equal_bits val_c1 val_c2 "
snipend -

  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  snipbegin \<open>BinaryFoldConstantObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -

  using BinaryFoldConstant by auto

snipbegin \<open>AddShiftConstantRight\<close>
optimization AddShiftConstantRight: "(c1 + y) \<mapsto> y + c1 when \<not>(is_ConstantExpr y)"
snipend -

  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  snipbegin \<open>AddShiftConstantRightObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -

  using AddShiftConstantRight by auto

snipbegin \<open>AddNeutral\<close>
optimization AddNeutral: "(e + (const (IntVal32 0))) \<mapsto> e when (stamp_expr e = IntegerStamp 32 l u)"
snipend -

  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  snipbegin \<open>AddNeutralObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -

  using AddNeutral by auto

snipbegin \<open>NeutralLeftSub\<close>
optimization NeutralLeftSub: "(e\<^sub>1 - e\<^sub>2) + e\<^sub>2 \<mapsto> e\<^sub>1"
snipend -

  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  snipbegin \<open>NeutralLeftSubObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -

  using neutral_left_add_sub by auto

snipbegin \<open>NeutralRightSub\<close>
optimization NeutralRightSub: " e\<^sub>2 + (e\<^sub>1 - e\<^sub>2) \<mapsto> e\<^sub>1"
snipend -

  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  snipbegin \<open>NeutralRightSubObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -

  using neutral_right_add_sub by auto

snipbegin \<open>AddToSub\<close>
optimization AddToSub: "-e + y \<mapsto> y - e"
snipend -


  unfolding rewrite_preservation.simps rewrite_termination.simps
   apply (rule conjE, simp, simp del: le_expr_def)
  snipbegin \<open>AddToSubObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -

  using AddLeftNegateToSub by auto


end

snipbegin \<open>phase\<close>
phase AddCanonicalizations
  trm size
begin
  text_raw "\\dots"
end
snipend -

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
text \<open>@{thm[display, margin=30] graph_semantics_preservation_subscript [no_vars]}\<close>
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
