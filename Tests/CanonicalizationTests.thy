theory
  CanonicalizationTests
imports
  Optimizations.Canonicalization
begin

subsection \<open>IntegerEqualsCanonicalizerTest\<close>
(* initial: IntegerEqualsCanonicalizerTest_testSubtractEqualsZeroSnippet*)
definition IntegerEqualsCanonicalizerTest_testSubtractEqualsZeroSnippet_initial :: IRGraph where  "IntegerEqualsCanonicalizerTest_testSubtractEqualsZeroSnippet_initial = irgraph [
  (0, (StartNode (Some 3) 9), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SubNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (IntegerEqualsNode 1 2), VoidStamp),
  (7, (BeginNode 12), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (IfNode 6 8 7), VoidStamp),
  (10, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (ReturnNode (Some 10) None), VoidStamp),
  (12, (ReturnNode (Some 5) None), VoidStamp)
  ]"

(* final: IntegerEqualsCanonicalizerTest_testSubtractEqualsZeroSnippet*)
definition IntegerEqualsCanonicalizerTest_testSubtractEqualsZeroSnippet_final :: IRGraph where  "IntegerEqualsCanonicalizerTest_testSubtractEqualsZeroSnippet_final = irgraph [
  (0, (StartNode None 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
  (5, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (ConditionalNode 4 5 3), IntegerStamp 32 (0) (1)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"

values "{g' . CanonicalizationPhase IntegerEqualsCanonicalizerTest_testSubtractEqualsZeroSnippet_initial (0, {}, None) g'}"



subsection \<open>IfCanonicalizerTest\<close>

(* initial: IfCanonicalizerTest_test1Snippet*)
definition IfCanonicalizerTest_test1Snippet_initial :: IRGraph where  "IfCanonicalizerTest_test1Snippet_initial = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 3 3), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ReturnNode (Some 8) None), VoidStamp),
  (10, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"

(* final: IfCanonicalizerTest_test1Snippet*)
definition IfCanonicalizerTest_test1Snippet_final :: IRGraph where  "IfCanonicalizerTest_test1Snippet_final = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"

values "{g' . CanonicalizationPhase IfCanonicalizerTest_test1Snippet_initial (0, {}, None) g'}"


(* initial: IfCanonicalizerTest_test2Snippet*)
definition IfCanonicalizerTest_test2Snippet_initial :: IRGraph where  "IfCanonicalizerTest_test2Snippet_initial = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 3 3), VoidStamp),
  (5, (BeginNode 23), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 16), VoidStamp),
  (10, (IfNode 4 9 8), VoidStamp),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode  [11, 13] (Some 19) 21), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (BeginNode 18), VoidStamp),
  (15, (BeginNode 13), VoidStamp),
  (16, (IfNode 4 14 15), VoidStamp),
  (17, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (18, (ReturnNode (Some 17) None), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (ConstantNode (IntVal 32 (3))), IntegerStamp 32 (3) (3)),
  (21, (ReturnNode (Some 20) None), VoidStamp),
  (22, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (23, (ReturnNode (Some 22) None), VoidStamp)
  ]"

(* final: IfCanonicalizerTest_test2Snippet*)
definition IfCanonicalizerTest_test2Snippet_final :: IRGraph where  "IfCanonicalizerTest_test2Snippet_final = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"
values "{g' . CanonicalizationPhase IfCanonicalizerTest_test2Snippet_initial (0, {}, None) g'}"


(* initial: IfCanonicalizerTest_test3Snippet*)
definition IfCanonicalizerTest_test3Snippet_initial :: IRGraph where  "IfCanonicalizerTest_test3Snippet_initial = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 3 3), VoidStamp),
  (5, (BeginNode 43), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (IntegerEqualsNode 3 8), VoidStamp),
  (10, (BeginNode 15), VoidStamp),
  (11, (BeginNode 20), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (BeginNode 24), VoidStamp),
  (14, (BeginNode 17), VoidStamp),
  (15, (IfNode 9 14 13), VoidStamp),
  (16, (ConstantNode (IntVal 32 (3))), IntegerStamp 32 (3) (3)),
  (17, (ReturnNode (Some 16) None), VoidStamp),
  (18, (IntegerLessThanNode 3 3), VoidStamp),
  (19, (BeginNode 29), VoidStamp),
  (20, (EndNode), VoidStamp),
  (21, (MergeNode  [20, 22, 26, 32, 35] (Some 40) 41), VoidStamp),
  (22, (EndNode), VoidStamp),
  (23, (BeginNode 22), VoidStamp),
  (24, (IfNode 18 23 19), VoidStamp),
  (25, (IntegerLessThanNode 3 8), VoidStamp),
  (26, (EndNode), VoidStamp),
  (27, (BeginNode 34), VoidStamp),
  (28, (BeginNode 26), VoidStamp),
  (29, (IfNode 25 27 28), VoidStamp),
  (30, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (31, (BeginNode 38), VoidStamp),
  (32, (EndNode), VoidStamp),
  (33, (BeginNode 32), VoidStamp),
  (34, (IfNode 18 33 31), VoidStamp),
  (35, (EndNode), VoidStamp),
  (36, (BeginNode 39), VoidStamp),
  (37, (BeginNode 35), VoidStamp),
  (38, (IfNode 25 36 37), VoidStamp),
  (39, (ReturnNode (Some 8) None), VoidStamp),
  (40, (FrameState [] None None None), IllegalStamp),
  (41, (ReturnNode (Some 16) None), VoidStamp),
  (42, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (43, (ReturnNode (Some 42) None), VoidStamp)
  ]"

(* final: IfCanonicalizerTest_test3Snippet*)
definition IfCanonicalizerTest_test3Snippet_final :: IRGraph where  "IfCanonicalizerTest_test3Snippet_final = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"

(* initial: IfCanonicalizerTest_test4Snippet*)
definition IfCanonicalizerTest_test4Snippet_initial :: IRGraph where  "IfCanonicalizerTest_test4Snippet_initial = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 3 3), VoidStamp),
  (5, (BeginNode 10), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ReturnNode (Some 8) None), VoidStamp),
  (10, (ReturnNode (Some 8) None), VoidStamp)
  ]"

(* final: IfCanonicalizerTest_test4Snippet*)
definition IfCanonicalizerTest_test4Snippet_final :: IRGraph where  "IfCanonicalizerTest_test4Snippet_final = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"

(* initial: IfCanonicalizerTest_test5Snippet*)
definition IfCanonicalizerTest_test5Snippet_initial :: IRGraph where  "IfCanonicalizerTest_test5Snippet_initial = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (4, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (IntegerEqualsNode 4 4), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (BeginNode 12), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (EndNode), VoidStamp),
  (11, (MergeNode  [10, 12] (Some 14) 21), VoidStamp),
  (12, (EndNode), VoidStamp),
  (13, (ValuePhiNode 13  [3, 9] 11), IntegerStamp 32 (1) (2)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (ConstantNode (IntVal 32 (3))), IntegerStamp 32 (3) (3)),
  (16, (AddNode 13 15), IntegerStamp 32 (4) (5)),
  (17, (MulNode 4 16), IntegerStamp 32 (-2147483648) (2147483647)),
  (18, (IntegerEqualsNode 17 4), VoidStamp),
  (19, (BeginNode 23), VoidStamp),
  (20, (BeginNode 22), VoidStamp),
  (21, (IfNode 18 20 19), VoidStamp),
  (22, (ReturnNode (Some 9) None), VoidStamp),
  (23, (ReturnNode (Some 9) None), VoidStamp)
  ]"

(* final: IfCanonicalizerTest_test5Snippet*)
definition IfCanonicalizerTest_test5Snippet_final :: IRGraph where  "IfCanonicalizerTest_test5Snippet_final = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"



end