theory
  CanonicalizationTests
imports
  Optimizations.Canonicalization
  Tests.IRGraphSort
  Graph.Comparison
begin

thm CanonicalizationStep.equation
thm CanonicalizationPhase.equation

definition CanonicalizationPhaseAnalysisStart where
  "CanonicalizationPhaseAnalysisStart = None"


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
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (BeginNode 9), VoidStamp),
  (4, (BeginNode 7), VoidStamp),
  (5, (IfNode 10 4 3), VoidStamp),
  (6, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (ReturnNode (Some 6) None), VoidStamp),
  (8, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (9, (ReturnNode (Some 8) None), VoidStamp),
  (10, (ConstantNode (IntVal 1 (1))), VoidStamp)
  ]"

value "
  eqGraph
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IfCanonicalizerTest_test1Snippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IfCanonicalizerTest_test1Snippet_final
"

value "
  diffNodesInfo
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IfCanonicalizerTest_test1Snippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IfCanonicalizerTest_test1Snippet_final
"


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
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (BeginNode 21), VoidStamp),
  (4, (BeginNode 8), VoidStamp),
  (5, (IfNode 22 4 3), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (BeginNode 14), VoidStamp),
  (8, (IfNode 22 7 6), VoidStamp),
  (9, (EndNode), VoidStamp),
  (10, (MergeNode  [9, 11] (Some 17) 19), VoidStamp),
  (11, (EndNode), VoidStamp),
  (12, (BeginNode 16), VoidStamp),
  (13, (BeginNode 11), VoidStamp),
  (14, (IfNode 22 12 13), VoidStamp),
  (15, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (16, (ReturnNode (Some 15) None), VoidStamp),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ConstantNode (IntVal 32 (3))), IntegerStamp 32 (3) (3)),
  (19, (ReturnNode (Some 18) None), VoidStamp),
  (20, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (21, (ReturnNode (Some 20) None), VoidStamp),
  (22, (ConstantNode (IntVal 1 (1))), VoidStamp)
  ]"

value "
  eqGraph
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IfCanonicalizerTest_test2Snippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IfCanonicalizerTest_test2Snippet_final
"

value "
  diffNodesInfo
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IfCanonicalizerTest_test2Snippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IfCanonicalizerTest_test2Snippet_final
"


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
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (BeginNode 37), VoidStamp),
  (4, (BeginNode 9), VoidStamp),
  (5, (IfNode 38 4 3), VoidStamp),
  (6, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (BeginNode 12), VoidStamp),
  (8, (BeginNode 16), VoidStamp),
  (9, (IfNode 39 8 7), VoidStamp),
  (10, (BeginNode 20), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 39 11 10), VoidStamp),
  (13, (ConstantNode (IntVal 32 (3))), IntegerStamp 32 (3) (3)),
  (14, (ReturnNode (Some 13) None), VoidStamp),
  (15, (BeginNode 24), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode  [16, 18, 21, 26, 29] (Some 34) 35), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (BeginNode 18), VoidStamp),
  (20, (IfNode 39 19 15), VoidStamp),
  (21, (EndNode), VoidStamp),
  (22, (BeginNode 28), VoidStamp),
  (23, (BeginNode 21), VoidStamp),
  (24, (IfNode 38 22 23), VoidStamp),
  (25, (BeginNode 32), VoidStamp),
  (26, (EndNode), VoidStamp),
  (27, (BeginNode 26), VoidStamp),
  (28, (IfNode 39 27 25), VoidStamp),
  (29, (EndNode), VoidStamp),
  (30, (BeginNode 33), VoidStamp),
  (31, (BeginNode 29), VoidStamp),
  (32, (IfNode 38 30 31), VoidStamp),
  (33, (ReturnNode (Some 6) None), VoidStamp),
  (34, (FrameState [] None None None), IllegalStamp),
  (35, (ReturnNode (Some 13) None), VoidStamp),
  (36, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (37, (ReturnNode (Some 36) None), VoidStamp),
  (38, (ConstantNode (IntVal 1 (1))), VoidStamp),
  (39, (ConstantNode (IntVal 1 (0))), VoidStamp)
  ]"

value "
  eqGraph
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IfCanonicalizerTest_test3Snippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IfCanonicalizerTest_test3Snippet_final
"

value "
  diffNodesGraph
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IfCanonicalizerTest_test3Snippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IfCanonicalizerTest_test3Snippet_final
"


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
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (BeginNode 8), VoidStamp),
  (4, (BeginNode 7), VoidStamp),
  (5, (IfNode 9 4 3), VoidStamp),
  (6, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (ReturnNode (Some 6) None), VoidStamp),
  (8, (ReturnNode (Some 6) None), VoidStamp),
  (9, (ConstantNode (IntVal 1 (1))), VoidStamp)
  ]"

value "
  eqGraph
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IfCanonicalizerTest_test4Snippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IfCanonicalizerTest_test4Snippet_final
"

value "
  diffNodesGraph
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IfCanonicalizerTest_test4Snippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IfCanonicalizerTest_test4Snippet_final
"


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
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (4, (BeginNode 8), VoidStamp),
  (5, (BeginNode 10), VoidStamp),
  (6, (IfNode 18 5 4), VoidStamp),
  (7, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (8, (EndNode), VoidStamp),
  (9, (MergeNode  [8, 10] (Some 12) 15), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (ValuePhiNode 11  [3, 7] 9), IntegerStamp 32 (1) (2)),
  (12, (FrameState [] None None None), IllegalStamp),
  (13, (BeginNode 17), VoidStamp),
  (14, (BeginNode 16), VoidStamp),
  (15, (IfNode 18 14 13), VoidStamp),
  (16, (ReturnNode (Some 7) None), VoidStamp),
  (17, (ReturnNode (Some 7) None), VoidStamp),
  (18, (ConstantNode (IntVal 1 (1))), VoidStamp)
  ]"

value "
  eqGraph
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IfCanonicalizerTest_test5Snippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IfCanonicalizerTest_test5Snippet_final
"

value "
  diffNodesGraph
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IfCanonicalizerTest_test5Snippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IfCanonicalizerTest_test5Snippet_final
"


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
  (5, (BeginNode 10), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ReturnNode (Some 8) None), VoidStamp),
  (10, (ReturnNode (Some 3) None), VoidStamp)
  ]"

value "
  eqGraph
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IntegerEqualsCanonicalizerTest_testSubtractEqualsZeroSnippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IntegerEqualsCanonicalizerTest_testSubtractEqualsZeroSnippet_final
"

value "
  diffNodesGraph
  (Predicate.the
    (CanonicalizationPhase_i_i_o
      IntegerEqualsCanonicalizerTest_testSubtractEqualsZeroSnippet_initial
      (0, {}, CanonicalizationPhaseAnalysisStart)
    ))
  IntegerEqualsCanonicalizerTest_testSubtractEqualsZeroSnippet_final
"



end