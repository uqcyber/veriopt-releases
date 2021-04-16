subsection \<open>Synthetic\<close>

theory
  ConditionalEliminationSyntheticTests
imports
  Optimizations.ConditionalElimination
begin

text \<open>
Synthetic optimization cases (written by hand during the development of the phase)
which are useful to ensure continued correctness.

Once the predicate compiler can be successfully defeated, these will ideally become
regression tests that will be automatically checked during building.
\<close>

definition ConditionalEliminationTest1_test1Snippet_initial :: IRGraph where
  "ConditionalEliminationTest1_test1Snippet_initial = irgraph [
  (0, (StartNode  (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState []  None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 39), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (5))), IntegerStamp 32 (5) (5)),
  (9, (IntegerEqualsNode 1 8), VoidStamp),
  (10, (BeginNode 16), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ConstantNode (IntVal 32 (100))), IntegerStamp 32 (100) (100)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 13  (Some 15)  None 18), VoidStamp),
  (15, (FrameState []  None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode  [16, 18]  (Some 19) 24), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (FrameState []  None None None), IllegalStamp),
  (20, (ConstantNode (IntVal 32 (101))), IntegerStamp 32 (101) (101)),
  (21, (IntegerLessThanNode 1 20), VoidStamp),
  (22, (BeginNode 30), VoidStamp),
  (23, (BeginNode 25), VoidStamp),
  (24, (IfNode 21 23 22), VoidStamp),
  (25, (EndNode), VoidStamp),
  (26, (MergeNode  [25, 27, 34]  (Some 35) 43), VoidStamp),
  (27, (EndNode), VoidStamp),
  (28, (BeginNode 32), VoidStamp),
  (29, (BeginNode 27), VoidStamp),
  (30, (IfNode 4 28 29), VoidStamp),
  (31, (ConstantNode (IntVal 32 (200))), IntegerStamp 32 (200) (200)),
  (32, (StoreFieldNode 32 ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 31  (Some 33)  None 34), VoidStamp),
  (33, (FrameState []  None None None), IllegalStamp),
  (34, (EndNode), VoidStamp),
  (35, (FrameState []  None None None), IllegalStamp),
  (36, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (37, (IntegerEqualsNode 1 36), VoidStamp),
  (38, (BeginNode 45), VoidStamp),
  (39, (EndNode), VoidStamp),
  (40, (MergeNode  [39, 41, 47]  (Some 48) 49), VoidStamp),
  (41, (EndNode), VoidStamp),
  (42, (BeginNode 41), VoidStamp),
  (43, (IfNode 37 42 38), VoidStamp),
  (44, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (45, (StoreFieldNode 45 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 44  (Some 46)  None 47), VoidStamp),
  (46, (FrameState []  None None None), IllegalStamp),
  (47, (EndNode), VoidStamp),
  (48, (FrameState []  None None None), IllegalStamp),
  (49, (StoreFieldNode 49 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3  (Some 50)  None 51), VoidStamp),
  (50, (FrameState []  None None None), IllegalStamp),
  (51, (ReturnNode  None  None), VoidStamp)
  ]"
values "{g' . ConditionalEliminationPhase ConditionalEliminationTest1_test1Snippet_initial (0, {}, [], []) g'}"


definition exAlwaysDistinct :: "IRGraph" where
  "exAlwaysDistinct = irgraph [
    (0, (StartNode (None) (4)), VoidStamp),
    (1, (ParameterNode (0)), IntegerStamp 32 (1) (2)),
    (2, (ParameterNode (1)), IntegerStamp 32 (3) (4)),
    (3, (IntegerEqualsNode (1) (2)), default_stamp),
    (4, (IfNode (3) (5) (6)), VoidStamp),
    (5, (BeginNode 7), VoidStamp),
    (6, (BeginNode 8), VoidStamp),
    (7, (EndNode), VoidStamp),
    (8, (EndNode), VoidStamp),
    (9, (MergeNode [7, 8] None 11), VoidStamp),
    (10, (ValuePhiNode 10 [1, 2] 9), VoidStamp),
    (11, (ReturnNode ((Some 10)) (None)), default_stamp)]"

values "{g' . ConditionalEliminationPhase exAlwaysDistinct (0, {}, [], []) g'}"


definition exNeverDistinct :: "IRGraph" where
  "exNeverDistinct = irgraph [
    (0, (StartNode (None) (4)), VoidStamp),
    (1, (ParameterNode (0)), IntegerStamp 32 (1) (1)),
    (2, (ParameterNode (1)), IntegerStamp 32 (1) (1)),
    (3, (IntegerEqualsNode (1) (2)), default_stamp),
    (4, (IfNode (3) (5) (6)), VoidStamp),
    (5, (BeginNode 7), VoidStamp),
    (6, (BeginNode 8), VoidStamp),
    (7, (EndNode), VoidStamp),
    (8, (EndNode), VoidStamp),
    (9, (MergeNode [7, 8] None 11), VoidStamp),
    (10, (ValuePhiNode 10 [1, 2] 9), VoidStamp),
    (11, (ReturnNode ((Some 10)) (None)), default_stamp)]"
values "{g' . ConditionalEliminationPhase exNeverDistinct (0, {}, [], []) g'}"

definition exImpliesElim :: "IRGraph" where
  "exImpliesElim = irgraph [
    (0, (StartNode (None) (4)), VoidStamp),
    (1, (ParameterNode (0)), default_stamp),
    (2, (ParameterNode (1)), default_stamp),
    (3, (IntegerEqualsNode (1) (2)), default_stamp),
    (4, (IfNode (3) (5) (6)), VoidStamp),
    (5, (BeginNode (9)), VoidStamp),
    (6, (BeginNode (7)), VoidStamp),
    (7, (EndNode), VoidStamp),
    (8, (IntegerLessThanNode (1) (2)), default_stamp),
    (9, (IfNode (8) (10) (11)), default_stamp),
    (10, (BeginNode 12), VoidStamp),
    (11, (BeginNode 13), VoidStamp),
    (12, (EndNode), VoidStamp),
    (13, (EndNode), VoidStamp),
    (14, (MergeNode [12, 13] None 15), VoidStamp),
    (15, (EndNode), VoidStamp),
    (16, (MergeNode [7, 15] None 17), VoidStamp),
    (17, (ReturnNode (Some 1) None), default_stamp)
  ]"
values "{g' . ConditionalEliminationPhase exImpliesElim (0, {}, [], []) g'}"

(* same as previous but condition is in else so condition is negated -- shouldn't optimize *)
definition exImpliesElimNeg :: "IRGraph" where
  "exImpliesElimNeg = irgraph [
    (0, (StartNode (None) (4)), VoidStamp),
    (1, (ParameterNode (0)), default_stamp),
    (2, (ParameterNode (1)), default_stamp),
    (3, (IntegerEqualsNode (1) (2)), default_stamp),
    (4, (IfNode (3) (6) (5)), VoidStamp),
    (5, (BeginNode (9)), VoidStamp),
    (6, (BeginNode (7)), VoidStamp),
    (7, (EndNode), VoidStamp),
    (8, (IntegerLessThanNode (1) (2)), default_stamp),
    (9, (IfNode (8) (10) (11)), default_stamp),
    (10, (BeginNode 12), VoidStamp),
    (11, (BeginNode 13), VoidStamp),
    (12, (EndNode), VoidStamp),
    (13, (EndNode), VoidStamp),
    (14, (MergeNode [12, 13] None 15), VoidStamp),
    (15, (EndNode), VoidStamp),
    (16, (MergeNode [7, 15] None 17), VoidStamp),
    (17, (ReturnNode (Some 1) None), default_stamp)
  ]"
values "{g' . ConditionalEliminationPhase exImpliesElimNeg (0, {}, [], []) g'}"


(* tests the negation implies rule *)
definition exImpliesElimNegation :: "IRGraph" where
  "exImpliesElimNegation = irgraph [
    (0, (StartNode (None) (4)), VoidStamp),
    (1, (ParameterNode (0)), default_stamp),
    (2, (ParameterNode (1)), default_stamp),
    (3, (IntegerEqualsNode (1) (2)), default_stamp),
    (4, (IfNode (3) (5) (6)), VoidStamp),
    (5, (BeginNode (9)), VoidStamp),
    (6, (BeginNode (7)), VoidStamp),
    (7, (EndNode), VoidStamp),
    (8, (IntegerLessThanNode (1) (2)), default_stamp),
    (200, (NegateNode 8), default_stamp),
    (9, (IfNode (200) (10) (11)), default_stamp),
    (10, (BeginNode 12), VoidStamp),
    (11, (BeginNode 13), VoidStamp),
    (12, (EndNode), VoidStamp),
    (13, (EndNode), VoidStamp),
    (14, (MergeNode [12, 13] None 15), VoidStamp),
    (15, (EndNode), VoidStamp),
    (16, (MergeNode [7, 15] None 17), VoidStamp),
    (17, (ReturnNode (Some 1) None), default_stamp)
  ]"
values "{g' . ConditionalEliminationPhase exImpliesElimNegation (0, {}, [], []) g'}"


definition ConditionalEliminationTest4_test2Snippet_initial :: IRGraph where
  "ConditionalEliminationTest4_test2Snippet_initial = irgraph [
  (0, (StartNode  (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) 2147483647),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) 2147483647),
  (3, (FrameState []  None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 8), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (EndNode), VoidStamp),
  (9, (MergeNode  [8, 10]  (Some 16) 18), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (BeginNode 15), VoidStamp),
  (12, (BeginNode 10), VoidStamp),
  (13, (IfNode 4 11 12), VoidStamp),
  (14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 1 1),
  (15, (ReturnNode  (Some 14)  None), VoidStamp),
  (16, (FrameState []  None None None), IllegalStamp),
  (17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 2 2),
  (18, (ReturnNode  (Some 17)  None), VoidStamp)
  ]"
values "{g' . ConditionalEliminationPhase ConditionalEliminationTest4_test2Snippet_initial (0, {}, [], []) g'}"

end