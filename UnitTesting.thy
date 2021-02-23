section \<open>Testing of IR Semantics based on GraalVM Unit Tests\<close>

theory UnitTesting
  imports
    IRStepObj
begin

declare [[ML_source_trace]]

inductive static_test :: "IRGraph \<Rightarrow> Value list \<Rightarrow> Value \<Rightarrow> bool"
  where
  "\<lbrakk>state = new_map ps;
    (\<lambda>x. Some g) \<turnstile> ([('''', 0, state), ('''', 0, state)], new_heap) | [] \<longrightarrow>* ((end # xs), heap) | l \<rbrakk>
    \<Longrightarrow> static_test g ps (m_val (prod.snd (prod.snd end)) 0)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testE) static_test .


(* gr1 *)
definition gr1 :: IRGraph where
  "gr1 = irgraph [
  (0, (StartNode  (Some 2) 5), default_stamp),
  (1, (ParameterNode 0), default_stamp),
  (2, (FrameState []  None None None), default_stamp),
  (3, (ConstantNode (IntVal 32 42)), default_stamp),
  (4, (AddNode 1 3), default_stamp),
  (5, (ReturnNode  (Some 3)  None), default_stamp)
  ]"
value "static_test gr1 [(IntVal 32 17)] (IntVal 32 42)"




(* ================= unittest8_phi_negint run =================== *)

(* Lorg/graalvm/compiler/api/directives/test/BlackholeDirectiveTest;.booleanSnippet*)
definition unit_booleanSnippet_3 :: IRGraph where
  "unit_booleanSnippet_3 = irgraph [
  (0, (StartNode  (Some 2) 11), default_stamp),
  (1, (ParameterNode 0), default_stamp),
  (2, (FrameState []  None None None), default_stamp),
  (3, (ConstantNode (IntVal 32 3)), default_stamp),
  (4, (ConstantNode (IntVal 32 4)), default_stamp),
  (5, (IntegerLessThanNode 1 4), default_stamp),
  (6, (ConstantNode (IntVal 32 0)), default_stamp),
  (7, (ConstantNode (IntVal 32 1)), default_stamp),
  (8, (ConditionalNode 5 6 7), default_stamp),
  (9, (BeginNode 12), default_stamp),
  (10, (BeginNode 13), default_stamp),
  (11, (IfNode 5 10 9), default_stamp),
  (12, (ReturnNode  (Some 7)  None), default_stamp),
  (13, (ReturnNode  (Some 7)  None), default_stamp)
  ]"
value "static_test unit_booleanSnippet_3 [(IntVal 32 (5))] (IntVal 32 (1))"


(* Lorg/graalvm/compiler/replacements/test/FoldTest;.callTest*)
(*
definition unit_callTest_6059 :: IRGraph where
  "unit_callTest_6059 = irgraph [
  (0, (StartNode  (Some 1) 7), default_stamp),
  (1, (FrameState []  None None None), default_stamp),
  (2, (FrameState []  None None None), default_stamp),
  (3, (ConstantNode (IntVal 32 FoldTest.FoldUtils@205149679)), default_stamp),
  (4, (ConstantNode (IntVal 32 21)), default_stamp),
  (5, (ConstantNode (IntVal 32 2)), default_stamp),
  (6, (ConstantNode (IntVal 32 42)), default_stamp),
  (7, (ReturnNode  (Some 6)  None), default_stamp)
  ]"
value "static_test unit_callTest_6059 [] (IntVal 32 (42))"
*)

(* Lorg/graalvm/compiler/api/directives/test/BlackholeDirectiveTest;.intSnippet*)
definition unit_intSnippet_1 :: IRGraph where
  "unit_intSnippet_1 = irgraph [
  (0, (StartNode  (Some 2) 5), default_stamp),
  (1, (ParameterNode 0), default_stamp),
  (2, (FrameState []  None None None), default_stamp),
  (3, (ConstantNode (IntVal 32 42)), default_stamp),
  (4, (AddNode 1 3), default_stamp),
  (5, (ReturnNode  (Some 3)  None), default_stamp)
  ]"
value "static_test unit_intSnippet_1 [(IntVal 32 (17))] (IntVal 32 (42))"


(* Lorg/graalvm/compiler/api/directives/test/OpaqueDirectiveTest;.intSnippet*)
definition unit_intSnippet_17 :: IRGraph where
  "unit_intSnippet_17 = irgraph [
  (0, (StartNode  (Some 1) 3), default_stamp),
  (1, (FrameState []  None None None), default_stamp),
  (2, (ConstantNode (IntVal 32 8)), default_stamp),
  (3, (ReturnNode  (Some 2)  None), default_stamp)
  ]"
value "static_test unit_intSnippet_17 [] (IntVal 32 (8))"


(* Lorg/graalvm/compiler/core/test/IfCanonicalizerTest;.test7Snippet*)
definition unit_test7Snippet_255 :: IRGraph where
  "unit_test7Snippet_255 = irgraph [
  (0, (StartNode  (Some 2) 7), default_stamp),
  (1, (ParameterNode 0), default_stamp),
  (2, (FrameState []  None None None), default_stamp),
  (3, (ConstantNode (IntVal 32 0)), default_stamp),
  (4, (IntegerLessThanNode 1 3), default_stamp),
  (5, (BeginNode 15), default_stamp),
  (6, (BeginNode 10), default_stamp),
  (7, (IfNode 4 6 5), default_stamp),
  (8, (ConstantNode (IntVal 32 1024)), default_stamp),
  (9, (IntegerLessThanNode 1 8), default_stamp),
  (10, (EndNode), default_stamp),
  (11, (MergeNode  [10, 12]  (Some 19) 22), default_stamp),
  (12, (EndNode), default_stamp),
  (13, (BeginNode 18), default_stamp),
  (14, (BeginNode 12), default_stamp),
  (15, (IfNode 9 13 14), default_stamp),
  (16, (ConstantNode (IntVal 32 1)), default_stamp),
  (17, (AddNode 1 16), default_stamp),
  (18, (ReturnNode  (Some 17)  None), default_stamp),
  (19, (FrameState []  None None None), default_stamp),
  (20, (ConstantNode (IntVal 32 (-1))), default_stamp),
  (21, (AddNode 1 20), default_stamp),
  (22, (ReturnNode  (Some 21)  None), default_stamp)
  ]"
value "static_test unit_test7Snippet_255 [(IntVal 32 (-1))] (IntVal 32 (-2))"


(* Lorg/graalvm/compiler/core/test/IfCanonicalizerTest;.test8Snippet*)
definition unit_test8Snippet_256 :: IRGraph where
  "unit_test8Snippet_256 = irgraph [
  (0, (StartNode  (Some 2) 7), default_stamp),
  (1, (ParameterNode 0), default_stamp),
  (2, (FrameState []  None None None), default_stamp),
  (3, (ConstantNode (IntVal 32 0)), default_stamp),
  (4, (IntegerLessThanNode 1 3), default_stamp),
  (5, (BeginNode 16), default_stamp),
  (6, (BeginNode 11), default_stamp),
  (7, (IfNode 4 6 5), default_stamp),
  (8, (ConstantNode (IntVal 32 1024)), default_stamp),
  (9, (ConstantNode (IntVal 32 1025)), default_stamp),
  (10, (IntegerLessThanNode 1 9), default_stamp),
  (11, (EndNode), default_stamp),
  (12, (MergeNode  [11, 13]  (Some 20) 23), default_stamp),
  (13, (EndNode), default_stamp),
  (14, (BeginNode 19), default_stamp),
  (15, (BeginNode 13), default_stamp),
  (16, (IfNode 10 14 15), default_stamp),
  (17, (ConstantNode (IntVal 32 1)), default_stamp),
  (18, (AddNode 1 17), default_stamp),
  (19, (ReturnNode  (Some 18)  None), default_stamp),
  (20, (FrameState []  None None None), default_stamp),
  (21, (ConstantNode (IntVal 32 (-1))), default_stamp),
  (22, (AddNode 1 21), default_stamp),
  (23, (ReturnNode  (Some 22)  None), default_stamp)
  ]"
value "static_test unit_test8Snippet_256 [(IntVal 32 (-1))] (IntVal 32 (-2))"


(* Lorg/graalvm/compiler/core/test/IfCanonicalizerTest;.test9Snippet*)
definition unit_test9Snippet_257 :: IRGraph where
  "unit_test9Snippet_257 = irgraph [
  (0, (StartNode  (Some 2) 7), default_stamp),
  (1, (ParameterNode 0), default_stamp),
  (2, (FrameState []  None None None), default_stamp),
  (3, (ConstantNode (IntVal 32 0)), default_stamp),
  (4, (IntegerLessThanNode 1 3), default_stamp),
  (5, (BeginNode 14), default_stamp),
  (6, (BeginNode 15), default_stamp),
  (7, (IfNode 4 6 5), default_stamp),
  (8, (ConstantNode (IntVal 32 1)), default_stamp),
  (10, (ConstantNode (IntVal 32 1024)), default_stamp),
  (11, (IntegerLessThanNode 1 10), default_stamp),
  (12, (BeginNode 17), default_stamp),
  (13, (BeginNode 20), default_stamp),
  (14, (IfNode 11 13 12), default_stamp),
  (15, (EndNode), default_stamp),
  (16, (MergeNode  [15, 17, 20]  (Some 21) 22), default_stamp),
  (17, (EndNode), default_stamp),
  (18, (ValuePhiNode 18  [8, 10, 19] 16), default_stamp),
  (19, (AddNode 1 8), default_stamp),
  (20, (EndNode), default_stamp),
  (21, (FrameState []  None None None), default_stamp),
  (22, (ReturnNode  (Some 18)  None), default_stamp)
  ]"
value "static_test unit_test9Snippet_257 [(IntVal 32 (-1))] (IntVal 32 (1))"


(* Lorg/graalvm/compiler/core/test/IfCanonicalizerTest;.test9Snippet*)
definition unit_test9Snippet_258 :: IRGraph where
  "unit_test9Snippet_258 = irgraph [
  (0, (StartNode  (Some 2) 7), default_stamp),
  (1, (ParameterNode 0), default_stamp),
  (2, (FrameState []  None None None), default_stamp),
  (3, (ConstantNode (IntVal 32 0)), default_stamp),
  (4, (IntegerLessThanNode 1 3), default_stamp),
  (5, (BeginNode 14), default_stamp),
  (6, (BeginNode 15), default_stamp),
  (7, (IfNode 4 6 5), default_stamp),
  (8, (ConstantNode (IntVal 32 1)), default_stamp),
  (10, (ConstantNode (IntVal 32 1024)), default_stamp),
  (11, (IntegerLessThanNode 1 10), default_stamp),
  (12, (BeginNode 17), default_stamp),
  (13, (BeginNode 20), default_stamp),
  (14, (IfNode 11 13 12), default_stamp),
  (15, (EndNode), default_stamp),
  (16, (MergeNode  [15, 17, 20]  (Some 21) 22), default_stamp),
  (17, (EndNode), default_stamp),
  (18, (ValuePhiNode 18  [8, 10, 19] 16), default_stamp),
  (19, (AddNode 1 8), default_stamp),
  (20, (EndNode), default_stamp),
  (21, (FrameState []  None None None), default_stamp),
  (22, (ReturnNode  (Some 18)  None), default_stamp)
  ]"
value "static_test unit_test9Snippet_258 [(IntVal 32 (1025))] (IntVal 32 (1024))"


(* Lorg/graalvm/compiler/api/directives/test/ControlFlowAnchorDirectiveTest;.verifyMergeSnippet*)
definition unit_verifyMergeSnippet_11 :: IRGraph where
  "unit_verifyMergeSnippet_11 = irgraph [
  (0, (StartNode  (Some 2) 8), default_stamp),
  (1, (ParameterNode 0), default_stamp),
  (2, (FrameState []  None None None), default_stamp),
  (3, (ConstantNode (IntVal 32 5)), default_stamp),
  (4, (ConstantNode (IntVal 32 6)), default_stamp),
  (5, (IntegerLessThanNode 1 4), default_stamp),
  (6, (BeginNode 10), default_stamp),
  (7, (BeginNode 12), default_stamp),
  (8, (IfNode 5 7 6), default_stamp),
  (9, (ConstantNode (IntVal 32 1)), default_stamp),
  (10, (ReturnNode  (Some 9)  None), default_stamp),
  (11, (ConstantNode (IntVal 32 2)), default_stamp),
  (12, (ReturnNode  (Some 11)  None), default_stamp)
  ]"
value "static_test unit_verifyMergeSnippet_11 [(IntVal 32 (42))] (IntVal 32 (1))"

end