theory ValidationSnippets
  imports
    IRGraphSort
    Snippets.Snipping
    Graph.Comparison
    ConditionalElimination.ConditionalElimination
begin

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

snipbegin \<open>StepSemantics\<close>
text \<open>
@{thm[display,margin=60] intval_mod.simps(1)}

\induct{@{thm[mode=Rule] step.SignedRemNode [no_vars]}}{eval:rem}
\<close>
snipend -

(* moduloSnippet not checked in
text_raw \<open>\Snip{ModuloSnippet}%
@{thm[display,margin=80] moduloSnippet_def}
\EndSnip\<close>
*)

snipbegin \<open>ModuloTestSnippet\<close>
text \<open>@{theory_text "static_test moduloSnippet [(IntVal 32 (1)), (Intval 32 (-2147483648))] (IntVal 32 (1))"}\<close>
snipend -

snipbegin \<open>ConditionalInitialEncoding\<close>
(* initial: ConditionalEliminationTest4_test1Snippet*)
definition test1_initial :: IRGraph where
"test1_initial = irgraph [
(0, (StartNode (Some 3) 7), VoidStamp),
(1, (ParameterNode 0), default_stamp),
(2, (ParameterNode 1), default_stamp),
(3, (FrameState [] None None None), IllegalStamp),
(4, (IntegerLessThanNode 2 1), VoidStamp),
(5, (BeginNode 8), VoidStamp),
(6, (BeginNode 13), VoidStamp),
(7, (IfNode 4 6 5), VoidStamp),
(8, (EndNode), VoidStamp),
(9, (MergeNode  [8, 10] (Some 16) 18), VoidStamp),
(10, (EndNode), VoidStamp),
(11, (BeginNode 15), VoidStamp),
(12, (BeginNode 10), VoidStamp),
(13, (IfNode 4 11 12), VoidStamp),
(14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
(15, (ReturnNode (Some 14) None), VoidStamp),
(16, (FrameState [] None None None), IllegalStamp),
(17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
(18, (ReturnNode (Some 17) None), VoidStamp)
]"
snipend -

snipbegin \<open>ConditionalOptimizedEncoding\<close>
(* final: ConditionalEliminationTest4_test1Snippet*)
definition test1_final :: IRGraph where 
"test1_final = irgraph [
(0, (StartNode (Some 3) 7), VoidStamp),
(1, (ParameterNode 0), default_stamp),
(2, (ParameterNode 1), default_stamp),
(3, (FrameState [] None None None), IllegalStamp),
(4, (IntegerLessThanNode 2 1), VoidStamp),
(5, (BeginNode 8), VoidStamp),
(6, (BeginNode 13), VoidStamp),
(7, (IfNode 4 6 5), VoidStamp),
(8, (EndNode), VoidStamp),
(9, (MergeNode  [8, 10] (Some 16) 18), VoidStamp),
(10, (EndNode), VoidStamp),
(11, (BeginNode 15), VoidStamp),
(12, (BeginNode 10), VoidStamp),
(13, (IfNode 19 11 12), VoidStamp),
(14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
(15, (ReturnNode (Some 14) None), VoidStamp),
(16, (FrameState [] None None None), IllegalStamp),
(17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
(18, (ReturnNode (Some 17) None), VoidStamp),
(19, (ConstantNode (IntVal 1 (1))), VoidStamp)
]"
snipend -

value "runConditionalElimination test1_initial"

snipbegin \<open>ConditionalTest\<close>
corollary "(runConditionalElimination test1_initial) \<approx>\<^sub>s test1_final"
  by eval
snipend -

end
