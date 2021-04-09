theory ATVA2021
  imports
    IRGraph
    IREval
    IRStepObj
    Canonicalization
begin

notation (latex)
  NoNode ("\<epsilon>")

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

text_raw \<open>\Snip{isbinary}
@{text \<open>isBinaryArithmeticNodeType ::\<close>} @{typeof isBinaryArithmeticNodeType}
\EndSnip\<close>

(* figure out how to export a subset of IRNode!!! *)

text_raw \<open>\Snip{inputs_of}%
@{text \<open>inputs_of :: \<close>} @{typeof inputs_of}

@{thm inputs_of_ConstantNode}

@{thm inputs_of_ParameterNode}

@{thm inputs_of_ValuePhiNode}

@{thm inputs_of_AddNode}

@{thm inputs_of_IfNode}
\EndSnip\<close>

text_raw \<open>\Snip{graphdefnostamp}
@{bold \<open>typedef\<close>} @{term[source] \<open>IRGraph = {g :: ID \<rightharpoonup> IRNode . finite (dom g)}\<close>}
\EndSnip\<close>

text_raw \<open>\Snip{helpers_display}%
@{text \<open>ids :: \<close>} @{typeof ids_fake}

@{thm ids_fake.simps}\\[0.75em]

@{text \<open>kind :: \<close>} @{typeof kind_fake}

@{thm kind_fake.simps}\\[0.75em]

@{text \<open>inputs :: \<close>} @{typeof inputs}

@{thm inputs.simps}\\[0.75em]

@{text \<open>succ :: \<close>} @{typeof succ}

@{thm succ.simps}\\[0.75em]

@{text \<open>input_edges :: \<close>} @{typeof input_edges}

@{thm input_edges.simps}\\[0.75em]

@{text \<open>usages :: \<close>} @{typeof usages}

@{thm usages.simps}\\[0.75em]

@{text \<open>successor_edges :: \<close>} @{typeof successor_edges}

@{thm successor_edges.simps}\\[0.75em]

@{text \<open>predecessors :: \<close>} @{typeof predecessors}

@{thm predecessors.simps}\\[0.75em]
\EndSnip\<close>


text_raw \<open>\Snip{wff_start_def}%
@{thm[display,margin=40] wff_start_def}
\EndSnip\<close>
text_raw \<open>\Snip{wff_closed_def}%
@{thm[display,margin=40] wff_closed_def}
\EndSnip\<close> 
text_raw \<open>\Snip{wff_phis_def}%
@{thm[display,margin=40] wff_phis_def}
\EndSnip\<close> 
text_raw \<open>\Snip{wff_ends_def}%
@{thm[display,margin=40] wff_ends_def}
\EndSnip\<close>

text_raw \<open>\Snip{wff_graph_def}%
@{text \<open>wff_graph :: \<close>} @{typeof wff_graph}

@{thm[display] wff_graph.simps}
\EndSnip\<close>


text_raw \<open>\Snip{programdef}
{@bold \<open>type-synonym\<close>} Signature = @{typeof Signature}

{@bold \<open>type-synonym\<close>} Program = @{typeof Program}
\<close>

(* TODO: add heap here *)

text_raw \<open>\Snip{ExpressionSemantics}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule,display] eval.ConstantNode [no_vars]}}{eval:const}
\induct{@{thm[mode=Rule,display] eval.ParameterNode [no_vars]}}{eval:param}
\induct{@{thm[mode=Rule,display] eval.ValuePhiNode [no_vars]}}{eval:phi}
\induct{@{thm[mode=Rule,display] eval.NegateNode [no_vars]}}{eval:neg}
\induct{@{thm[mode=Rule,display] eval.AddNode [no_vars]}}{eval:add}
\induct{@{thm[mode=Rule,display] eval.InvokeNodeEval [no_vars]}}{eval:invoke}
\induct{@{thm[mode=Rule,display] eval.LoadFieldNode [no_vars]}}{eval:load}
\induct{@{thm[mode=Rule,display] eval.RefNode [no_vars]}}{eval:ref}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>

text_raw \<open>\Snip{EvalAll}%\<close>
text \<open>
\begin{center}
@{thm[mode=Rule] eval_all.Base [no_vars]}\\[8px]
@{thm[mode=Rule] eval_all.Transitive [no_vars]}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>


text_raw \<open>\Snip{StepSemantics}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] step.SequentialNode [no_vars]}}{step:seq}
\induct{@{thm[mode=Rule] step.IfNode [no_vars]}}{step:if}
\induct{@{thm[mode=Rule] step.EndNodes [no_vars]}}{step:end}
\induct{@{thm[mode=Rule] step.RefNode [no_vars]}}{step:ref}
\induct{@{thm[mode=Rule] step.NewInstanceNode [no_vars]}}{step:newinst}
\induct{@{thm[mode=Rule] step.LoadFieldNode [no_vars]}}{step:load}
\induct{@{thm[mode=Rule] step.StoreFieldNode [no_vars]}}{step:store}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>


text_raw \<open>\Snip{TopStepSemantics}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] step_top.Lift [no_vars]}}{top:lift}
\induct{@{thm[mode=Rule] step_top.InvokeNodeStep [no_vars]}}{top:invoke}
\induct{@{thm[mode=Rule] step_top.ReturnNode [no_vars]}}{top:return}
\induct{@{thm[mode=Rule] step_top.UnwindNode [no_vars]}}{top:unwind}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>

text_raw \<open>\Snip{CreateAddNodeDisplay}%
@{thm[display] create_add.simps}
\EndSnip\<close>

text_raw \<open>\Snip{AddNodeCreateDisplay}%
@{thm[display] add_node_create}
\EndSnip\<close>

text_raw \<open>\Snip{CreateIfNodeDisplay}%
@{thm[display] create_if.simps}
\EndSnip\<close>

text_raw \<open>\Snip{Stutter}%\<close>
text \<open>
\begin{center}
@{thm[mode=Rule] stutter.StutterStep [no_vars]}\\[8px]
@{thm[mode=Rule] stutter.Transitive [no_vars]}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>

text_raw \<open>\Snip{IfNodeCreateDisplay}%
@{thm[display] if_node_create}
\EndSnip\<close>

(* EXPERIMENTAL *)
notation (latex output)
  filtered_inputs ("inputs\<^latex>\<open>\\ensuremath{^{\\mathit{\<close>_\<llangle>_\<rrangle>\<^latex>\<open>}}}\<close>\<^latex>\<open>\\ensuremath{_{\\mathit{\<close>_\<^latex>\<open>}}}\<close>")
notation (latex output)
  filtered_successors ("succ\<^latex>\<open>\\ensuremath{^{\\mathit{\<close>_\<llangle>_\<rrangle>\<^latex>\<open>}}}\<close>\<^latex>\<open>\\ensuremath{_{\\mathit{\<close>_\<^latex>\<open>}}}\<close>")
notation (latex output)
  filtered_usages ("usages\<^latex>\<open>\\ensuremath{^{\\mathit{\<close>_\<llangle>_\<rrangle>\<^latex>\<open>}}}\<close>\<^latex>\<open>\\ensuremath{_{\\mathit{\<close>_\<^latex>\<open>}}}\<close>")

text_raw \<open>\Snip{example2}%
@{term[display] \<open>filtered_inputs g nid f\<close>}
\EndSnip\<close>

notation (latex output)
  Pure.dummy_pattern ("-")

(* take out bits from intvals - changes if we change to deal with bits *)
notation (latex output)
  IntVal ("IntVal (2 _)")

end