theory ConditionalEliminationTests
imports Optimizations.ConditionalElimination
begin


fun find_ref_nodes :: "IRGraph \<Rightarrow> (ID \<rightharpoonup> ID)" where
"find_ref_nodes g = map_of
  (map (\<lambda>n. (n, ir_ref (kind g n))) (filter (\<lambda>id. is_RefNode (kind g id)) (sorted_list_of_set (ids g))))"

fun replace_ref_nodes :: "IRGraph \<Rightarrow> (ID \<rightharpoonup> ID) \<Rightarrow> ID list \<Rightarrow> ID list" where
"replace_ref_nodes g m xs = map (\<lambda>id. (case (m id) of Some other \<Rightarrow> other | None \<Rightarrow> id)) xs"

inductive reachables :: "IRGraph \<Rightarrow> ID list \<Rightarrow> ID set \<Rightarrow> bool" where
"reachables g [] {}" |
"\<lbrakk>node = kind g n;
  new = (inputs_of node) @ (successors_of node);
  reachables g (to_see @ new) seen \<rbrakk> \<Longrightarrow> reachables g (n # to_see) ({n} \<union> seen)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) reachables .

inductive nodeEq :: "(ID \<rightharpoonup> ID) \<Rightarrow> IRGraph \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> ID \<Rightarrow> bool" where 
"\<lbrakk> kind g1 n1 = RefNode ref; nodeEq m g1 ref g2 n2 \<rbrakk> \<Longrightarrow> nodeEq m g1 n1 g2 n2" | 
"\<lbrakk> x = kind g1 n1; 
  y = kind g2 n2; 
  is_same_ir_node_type x y;
  replace_ref_nodes g1 m (successors_of x) = successors_of y; 
  replace_ref_nodes g1 m (inputs_of x) = inputs_of y \<rbrakk> 
  \<Longrightarrow> nodeEq m g1 n1 g2 n2"

code_pred [show_modes] nodeEq .

fun diffNodesGraph :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> ID set" where
"diffNodesGraph g1 g2 = (let refNodes = find_ref_nodes g1 in
    { n . n \<in> Predicate.the (reachables_i_i_o g1 [0]) \<and> (case refNodes n of Some _ \<Rightarrow> False | _ \<Rightarrow> True) \<and> \<not>(nodeEq refNodes g1 n g2 n)})"

fun eqGraph :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
"eqGraph isabelle_graph graal_graph = ((diffNodesGraph isabelle_graph graal_graph) = {})"




(* initial: ConditionalEliminationTest1_test1Snippet_basic*)
definition ConditionalEliminationTest1_test1Snippet_basic_initial :: IRGraph where
  "ConditionalEliminationTest1_test1Snippet_basic_initial = irgraph [
  (0, (StartNode  (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState []  None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 22), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 1 3), VoidStamp),
  (9, (BeginNode 15), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (IntVal 32 (200))), IntegerStamp 32 (200) (200)),
  (13, (StoreFieldNode 13 ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 12  (Some 14)  None 17), VoidStamp),
  (14, (FrameState []  None None None), IllegalStamp),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode  [15, 17]  (Some 18) 20), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (FrameState []  None None None), IllegalStamp),
  (19, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (20, (StoreFieldNode 20 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 19  (Some 21)  None 24), VoidStamp),
  (21, (FrameState []  None None None), IllegalStamp),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode  [22, 24]  (Some 25) 26), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (FrameState []  None None None), IllegalStamp),
  (26, (StoreFieldNode 26 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3  (Some 27)  None 28), VoidStamp),
  (27, (FrameState []  None None None), IllegalStamp),
  (28, (ReturnNode  None  None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest1_test1Snippet_basic*)
definition ConditionalEliminationTest1_test1Snippet_basic_final :: IRGraph where
  "ConditionalEliminationTest1_test1Snippet_basic_final = irgraph [
  (0, (StartNode  (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState []  None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 22), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 1 3), VoidStamp),
  (9, (BeginNode 15), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 29 10 9), VoidStamp),
  (12, (ConstantNode (IntVal 32 (200))), IntegerStamp 32 (200) (200)),
  (13, (StoreFieldNode 13 ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 12  (Some 14)  None 17), VoidStamp),
  (14, (FrameState []  None None None), IllegalStamp),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode  [15, 17]  (Some 18) 20), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (FrameState []  None None None), IllegalStamp),
  (19, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (20, (StoreFieldNode 20 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 19  (Some 21)  None 24), VoidStamp),
  (21, (FrameState []  None None None), IllegalStamp),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode  [22, 24]  (Some 25) 26), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (FrameState []  None None None), IllegalStamp),
  (26, (StoreFieldNode 26 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3  (Some 27)  None 28), VoidStamp),
  (27, (FrameState []  None None None), IllegalStamp),
  (28, (ReturnNode  None  None), VoidStamp),
  (29, (ConstantNode (IntVal 1 (0))), VoidStamp)
  ]"

values "{g' . ConditionalEliminationPhase ConditionalEliminationTest1_test1Snippet_basic_initial  (0, {}, [], []) g'}"

definition ConditionalEliminationTest1_test1Snippet_basic_isabelle :: IRGraph where
"ConditionalEliminationTest1_test1Snippet_basic_isabelle = irgraph [
    (11, IfNode 29 10 9, VoidStamp),
    (29, ConstantNode (IntVal 1 0), IntegerStamp 32 (- 2147483648) 2147483647),
    (0, StartNode (Some 2) 7, VoidStamp),
    (1, ParameterNode 0, IntegerStamp 32 (- 2147483648) 2147483647),
    (2, FrameState [] None None None, IllegalStamp),
    (3, ConstantNode (IntVal 32 0), IntegerStamp 32 0 0),
    (4, IntegerEqualsNode 1 3, VoidStamp), (5, BeginNode 22, VoidStamp),
    (6, BeginNode 11, VoidStamp), (7, IfNode 4 6 5, VoidStamp),
    (8, IntegerLessThanNode 1 3, VoidStamp), (9, BeginNode 15, VoidStamp),
    (10, BeginNode 13, VoidStamp), (11, IfNode 8 10 9, VoidStamp),
    (12, ConstantNode (IntVal 32 200), IntegerStamp 32 200 200),
    (13,
     StoreFieldNode 13
      ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 12
      (Some 14) None 17,
     VoidStamp),
    (14, FrameState [] None None None, IllegalStamp), (15, EndNode, VoidStamp),
    (16, MergeNode [15, 17] (Some 18) 20, VoidStamp), (17, EndNode, VoidStamp),
    (18, FrameState [] None None None, IllegalStamp),
    (19, ConstantNode (IntVal 32 1), IntegerStamp 32 1 1),
    (20,
     StoreFieldNode 20
      ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 19
      (Some 21) None 24,
     VoidStamp),
    (21, FrameState [] None None None, IllegalStamp), (22, EndNode, VoidStamp),
    (23, MergeNode [22, 24] (Some 25) 26, VoidStamp), (24, EndNode, VoidStamp),
    (25, FrameState [] None None None, IllegalStamp),
    (26,
     StoreFieldNode 26
      ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3
      (Some 27) None 28,
     VoidStamp),
    (27, FrameState [] None None None, IllegalStamp),
    (28, ReturnNode None None, VoidStamp)]"

(* compare test1Snippet_basic, isabelle optimised graph vs graal optimised graph *)
value "eqGraph ConditionalEliminationTest1_test1Snippet_basic_isabelle ConditionalEliminationTest1_test1Snippet_basic_final"





(* initial: ConditionalEliminationTest1_test1Snippet*)
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

(* final: ConditionalEliminationTest1_test1Snippet*)
definition ConditionalEliminationTest1_test1Snippet_final :: IRGraph where
  "ConditionalEliminationTest1_test1Snippet_final = irgraph [
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
  (12, (IfNode 52 11 10), VoidStamp),
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
  (24, (IfNode 53 23 22), VoidStamp),
  (25, (EndNode), VoidStamp),
  (26, (MergeNode  [25, 27, 34]  (Some 35) 43), VoidStamp),
  (27, (EndNode), VoidStamp),
  (28, (BeginNode 32), VoidStamp),
  (29, (BeginNode 27), VoidStamp),
  (30, (IfNode 53 28 29), VoidStamp),
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
  (43, (IfNode 52 42 38), VoidStamp),
  (44, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (45, (StoreFieldNode 45 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 44  (Some 46)  None 47), VoidStamp),
  (46, (FrameState []  None None None), IllegalStamp),
  (47, (EndNode), VoidStamp),
  (48, (FrameState []  None None None), IllegalStamp),
  (49, (StoreFieldNode 49 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3  (Some 50)  None 51), VoidStamp),
  (50, (FrameState []  None None None), IllegalStamp),
  (51, (ReturnNode  None  None), VoidStamp),
  (52, (ConstantNode (IntVal 1 (0))), VoidStamp),
  (53, (ConstantNode (IntVal 1 (1))), VoidStamp)
  ]"

values "{g' . ConditionalEliminationPhase ConditionalEliminationTest1_test1Snippet_initial  (0, {}, [], []) g'}"
definition ConditionalEliminationTest1_test1Snippet_isabelle :: IRGraph where
  "ConditionalEliminationTest1_test1Snippet_isabelle = irgraph
    [(43, IfNode 54 42 38, VoidStamp),
    (54, ConstantNode (IntVal 1 0), IntegerStamp 32 (- 2147483648) 2147483647),
    (24, IfNode 53 23 22, VoidStamp),
    (53, ConstantNode (IntVal 1 1), IntegerStamp 32 (- 2147483648) 2147483647),
    (12, IfNode 52 11 10, VoidStamp),
    (52, ConstantNode (IntVal 1 0), IntegerStamp 32 (- 2147483648) 2147483647),
    (0, StartNode (Some 2) 7, VoidStamp),
    (1, ParameterNode 0, IntegerStamp 32 (- 2147483648) 2147483647),
    (2, FrameState [] None None None, IllegalStamp),
    (3, ConstantNode (IntVal 32 0), IntegerStamp 32 0 0),
    (4, IntegerEqualsNode 1 3, VoidStamp), (5, BeginNode 39, VoidStamp),
    (6, BeginNode 12, VoidStamp), (7, IfNode 4 6 5, VoidStamp),
    (8, ConstantNode (IntVal 32 5), IntegerStamp 32 5 5),
    (9, IntegerEqualsNode 1 8, VoidStamp), (10, BeginNode 16, VoidStamp),
    (11, BeginNode 14, VoidStamp), 
    (12, IfNode 9 11 10, VoidStamp),
    (13, ConstantNode (IntVal 32 100), IntegerStamp 32 100 100),
    (14,
     StoreFieldNode 14
      ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 13
      (Some 15) None 18,
     VoidStamp),
    (15, FrameState [] None None None, IllegalStamp), (16, EndNode, VoidStamp),
    (17, MergeNode [16, 18] (Some 19) 24, VoidStamp), (18, EndNode, VoidStamp),
    (19, FrameState [] None None None, IllegalStamp),
    (20, ConstantNode (IntVal 32 101), IntegerStamp 32 101 101),
    (21, IntegerLessThanNode 1 20, VoidStamp), (22, BeginNode 30, VoidStamp),
    (23, BeginNode 25, VoidStamp), (24, IfNode 21 23 22, VoidStamp),
    (25, EndNode, VoidStamp), (26, MergeNode [25, 27, 34] (Some 35) 43, VoidStamp),
    (27, EndNode, VoidStamp), (28, BeginNode 32, VoidStamp),
    (29, BeginNode 27, VoidStamp), (30, IfNode 4 28 29, VoidStamp),
    (31, ConstantNode (IntVal 32 200), IntegerStamp 32 200 200),
    (32,
     StoreFieldNode 32
      ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 31
      (Some 33) None 34,
     VoidStamp),
    (33, FrameState [] None None None, IllegalStamp), (34, EndNode, VoidStamp),
    (35, FrameState [] None None None, IllegalStamp),
    (36, ConstantNode (IntVal 32 2), IntegerStamp 32 2 2),
    (37, IntegerEqualsNode 1 36, VoidStamp), (38, BeginNode 45, VoidStamp),
    (39, EndNode, VoidStamp), (40, MergeNode [39, 41, 47] (Some 48) 49, VoidStamp),
    (41, EndNode, VoidStamp), (42, BeginNode 41, VoidStamp),
    (43, IfNode 37 42 38, VoidStamp),
    (44, ConstantNode (IntVal 32 1), IntegerStamp 32 1 1),
    (45,
     StoreFieldNode 45
      ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 44
      (Some 46) None 47,
     VoidStamp),
    (46, FrameState [] None None None, IllegalStamp), (47, EndNode, VoidStamp),
    (48, FrameState [] None None None, IllegalStamp),
    (49,
     StoreFieldNode 49
      ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3
      (Some 50) None 51,
     VoidStamp),
    (50, FrameState [] None None None, IllegalStamp),
    (51, ReturnNode None None, VoidStamp)]"

(* compare test1Snippet_basic, isabelle optimised graph vs graal optimised graph *)
(* Works for now *)
value "eqGraph ConditionalEliminationTest1_test1Snippet_isabelle ConditionalEliminationTest1_test1Snippet_final"








(* initial: ConditionalEliminationTest1_test2Snippet*)
definition ConditionalEliminationTest1_test2Snippet_initial :: IRGraph where
  "ConditionalEliminationTest1_test2Snippet_initial = irgraph [
  (0, (StartNode  (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState []  None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 28), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (100))), IntegerStamp 32 (100) (100)),
  (9, (ConstantNode (IntVal 32 (101))), IntegerStamp 32 (101) (101)),
  (10, (IntegerLessThanNode 1 9), VoidStamp),
  (11, (BeginNode 19), VoidStamp),
  (12, (BeginNode 14), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode  [14, 16, 23]  (Some 24) 32), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (BeginNode 21), VoidStamp),
  (18, (BeginNode 16), VoidStamp),
  (19, (IfNode 4 17 18), VoidStamp),
  (20, (ConstantNode (IntVal 32 (200))), IntegerStamp 32 (200) (200)),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 20  (Some 22)  None 23), VoidStamp),
  (22, (FrameState []  None None None), IllegalStamp),
  (23, (EndNode), VoidStamp),
  (24, (FrameState []  None None None), IllegalStamp),
  (25, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (26, (IntegerEqualsNode 1 25), VoidStamp),
  (27, (BeginNode 34), VoidStamp),
  (28, (EndNode), VoidStamp),
  (29, (MergeNode  [28, 30, 36]  (Some 37) 38), VoidStamp),
  (30, (EndNode), VoidStamp),
  (31, (BeginNode 30), VoidStamp),
  (32, (IfNode 26 31 27), VoidStamp),
  (33, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (34, (StoreFieldNode 34 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 33  (Some 35)  None 36), VoidStamp),
  (35, (FrameState []  None None None), IllegalStamp),
  (36, (EndNode), VoidStamp),
  (37, (FrameState []  None None None), IllegalStamp),
  (38, (StoreFieldNode 38 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3  (Some 39)  None 40), VoidStamp),
  (39, (FrameState []  None None None), IllegalStamp),
  (40, (ReturnNode  None  None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest1_test2Snippet*)
definition ConditionalEliminationTest1_test2Snippet_final :: IRGraph where
  "ConditionalEliminationTest1_test2Snippet_final = irgraph [
  (0, (StartNode  (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState []  None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 28), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (100))), IntegerStamp 32 (100) (100)),
  (9, (ConstantNode (IntVal 32 (101))), IntegerStamp 32 (101) (101)),
  (10, (IntegerLessThanNode 1 9), VoidStamp),
  (11, (BeginNode 19), VoidStamp),
  (12, (BeginNode 14), VoidStamp),
  (13, (IfNode 41 12 11), VoidStamp),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode  [14, 16, 23]  (Some 24) 32), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (BeginNode 21), VoidStamp),
  (18, (BeginNode 16), VoidStamp),
  (19, (IfNode 41 17 18), VoidStamp),
  (20, (ConstantNode (IntVal 32 (200))), IntegerStamp 32 (200) (200)),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 20  (Some 22)  None 23), VoidStamp),
  (22, (FrameState []  None None None), IllegalStamp),
  (23, (EndNode), VoidStamp),
  (24, (FrameState []  None None None), IllegalStamp),
  (25, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (26, (IntegerEqualsNode 1 25), VoidStamp),
  (27, (BeginNode 34), VoidStamp),
  (28, (EndNode), VoidStamp),
  (29, (MergeNode  [28, 30, 36]  (Some 37) 38), VoidStamp),
  (30, (EndNode), VoidStamp),
  (31, (BeginNode 30), VoidStamp),
  (32, (IfNode 42 31 27), VoidStamp),
  (33, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (34, (StoreFieldNode 34 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 33  (Some 35)  None 36), VoidStamp),
  (35, (FrameState []  None None None), IllegalStamp),
  (36, (EndNode), VoidStamp),
  (37, (FrameState []  None None None), IllegalStamp),
  (38, (StoreFieldNode 38 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3  (Some 39)  None 40), VoidStamp),
  (39, (FrameState []  None None None), IllegalStamp),
  (40, (ReturnNode  None  None), VoidStamp),
  (41, (ConstantNode (IntVal 1 (1))), VoidStamp),
  (42, (ConstantNode (IntVal 1 (0))), VoidStamp)
  ]"


values "{g' . ConditionalEliminationPhase ConditionalEliminationTest1_test2Snippet_initial  (0, {}, [], []) g'}"
definition ConditionalEliminationTest1_test2Snippet_isabelle :: IRGraph where
  "ConditionalEliminationTest1_test2Snippet_isabelle = irgraph
   [(32, IfNode 42 31 27, VoidStamp),
    (42, ConstantNode (IntVal 1 0), IntegerStamp 32 (- 2147483648) 2147483647),
    (13, IfNode 41 12 11, VoidStamp),
    (41, ConstantNode (IntVal 1 1), IntegerStamp 32 (- 2147483648) 2147483647),
    (0, StartNode (Some 2) 7, VoidStamp),
    (1, ParameterNode 0, IntegerStamp 32 (- 2147483648) 2147483647),
    (2, FrameState [] None None None, IllegalStamp),
    (3, ConstantNode (IntVal 32 0), IntegerStamp 32 0 0),
    (4, IntegerEqualsNode 1 3, VoidStamp), (5, BeginNode 28, VoidStamp),
    (6, BeginNode 13, VoidStamp), (7, IfNode 4 6 5, VoidStamp),
    (8, ConstantNode (IntVal 32 100), IntegerStamp 32 100 100),
    (9, ConstantNode (IntVal 32 101), IntegerStamp 32 101 101),
    (10, IntegerLessThanNode 1 9, VoidStamp), (11, BeginNode 19, VoidStamp),
    (12, BeginNode 14, VoidStamp), (13, IfNode 10 12 11, VoidStamp),
    (14, EndNode, VoidStamp), (15, MergeNode [14, 16, 23] (Some 24) 32, VoidStamp),
    (16, EndNode, VoidStamp), (17, BeginNode 21, VoidStamp),
    (18, BeginNode 16, VoidStamp), (19, IfNode 4 17 18, VoidStamp),
    (20, ConstantNode (IntVal 32 200), IntegerStamp 32 200 200),
    (21,
     StoreFieldNode 21
      ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 20
      (Some 22) None 23,
     VoidStamp),
    (22, FrameState [] None None None, IllegalStamp), (23, EndNode, VoidStamp),
    (24, FrameState [] None None None, IllegalStamp),
    (25, ConstantNode (IntVal 32 2), IntegerStamp 32 2 2),
    (26, IntegerEqualsNode 1 25, VoidStamp), (27, BeginNode 34, VoidStamp),
    (28, EndNode, VoidStamp), (29, MergeNode [28, 30, 36] (Some 37) 38, VoidStamp),
    (30, EndNode, VoidStamp), (31, BeginNode 30, VoidStamp),
    (32, IfNode 26 31 27, VoidStamp),
    (33, ConstantNode (IntVal 32 1), IntegerStamp 32 1 1),
    (34,
     StoreFieldNode 34
      ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 33
      (Some 35) None 36,
     VoidStamp),
    (35, FrameState [] None None None, IllegalStamp), (36, EndNode, VoidStamp),
    (37, FrameState [] None None None, IllegalStamp),
    (38,
     StoreFieldNode 38
      ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3
      (Some 39) None 40,
     VoidStamp),
    (39, FrameState [] None None None, IllegalStamp),
    (40, ReturnNode None None, VoidStamp)]"

(* Graphs are not equal because current isabelle optimisation isn't flow sensitive/don't consider InfoElements *) 
value "diffNodesGraph ConditionalEliminationTest1_test2Snippet_isabelle ConditionalEliminationTest1_test2Snippet_final"
value "eqGraph ConditionalEliminationTest1_test2Snippet_isabelle ConditionalEliminationTest1_test2Snippet_final"





(* initial: ConditionalEliminationTest1_test3Snippet*)
definition ConditionalEliminationTest1_test3Snippet_initial :: IRGraph where
  "ConditionalEliminationTest1_test3Snippet_initial = irgraph [
  (0, (StartNode  (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState []  None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 10), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (IntegerLessThanNode 1 8), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (MergeNode  [10, 12, 18, 24, 31, 37, 43, 53, 56]  (Some 57) 58), VoidStamp),
  (12, (EndNode), VoidStamp),
  (13, (BeginNode 21), VoidStamp),
  (14, (BeginNode 12), VoidStamp),
  (15, (IfNode 9 13 14), VoidStamp),
  (16, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (17, (IntegerLessThanNode 1 16), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (BeginNode 27), VoidStamp),
  (20, (BeginNode 18), VoidStamp),
  (21, (IfNode 17 19 20), VoidStamp),
  (22, (ConstantNode (IntVal 32 (3))), IntegerStamp 32 (3) (3)),
  (23, (IntegerLessThanNode 1 22), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (BeginNode 33), VoidStamp),
  (26, (BeginNode 24), VoidStamp),
  (27, (IfNode 23 25 26), VoidStamp),
  (28, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (29, (IntegerLessThanNode 1 3), VoidStamp),
  (30, (BeginNode 39), VoidStamp),
  (31, (EndNode), VoidStamp),
  (32, (BeginNode 31), VoidStamp),
  (33, (IfNode 29 32 30), VoidStamp),
  (34, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (35, (IntegerLessThanNode 1 28), VoidStamp),
  (36, (BeginNode 45), VoidStamp),
  (37, (EndNode), VoidStamp),
  (38, (BeginNode 37), VoidStamp),
  (39, (IfNode 35 38 36), VoidStamp),
  (40, (ConstantNode (IntVal 32 (-3))), IntegerStamp 32 (-3) (-3)),
  (41, (IntegerLessThanNode 1 34), VoidStamp),
  (42, (BeginNode 49), VoidStamp),
  (43, (EndNode), VoidStamp),
  (44, (BeginNode 43), VoidStamp),
  (45, (IfNode 41 44 42), VoidStamp),
  (46, (IntegerEqualsNode 1 8), VoidStamp),
  (47, (BeginNode 54), VoidStamp),
  (48, (BeginNode 51), VoidStamp),
  (49, (IfNode 46 48 47), VoidStamp),
  (50, (ConstantNode (IntVal 32 (42))), IntegerStamp 32 (42) (42)),
  (51, (StoreFieldNode 51 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 50  (Some 52)  None 53), VoidStamp),
  (52, (FrameState []  None None None), IllegalStamp),
  (53, (EndNode), VoidStamp),
  (54, (StoreFieldNode 54 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 8  (Some 55)  None 56), VoidStamp),
  (55, (FrameState []  None None None), IllegalStamp),
  (56, (EndNode), VoidStamp),
  (57, (FrameState []  None None None), IllegalStamp),
  (58, (StoreFieldNode 58 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3  (Some 59)  None 60), VoidStamp),
  (59, (FrameState []  None None None), IllegalStamp),
  (60, (ReturnNode  None  None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest1_test3Snippet*)
definition ConditionalEliminationTest1_test3Snippet_final :: IRGraph where
  "ConditionalEliminationTest1_test3Snippet_final = irgraph [
  (0, (StartNode  (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState []  None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 10), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (IntegerLessThanNode 1 8), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (MergeNode  [10, 12, 18, 24, 31, 37, 43, 53, 56]  (Some 57) 58), VoidStamp),
  (12, (EndNode), VoidStamp),
  (13, (BeginNode 21), VoidStamp),
  (14, (BeginNode 12), VoidStamp),
  (15, (IfNode 61 13 14), VoidStamp),
  (16, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (17, (IntegerLessThanNode 1 16), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (BeginNode 27), VoidStamp),
  (20, (BeginNode 18), VoidStamp),
  (21, (IfNode 61 19 20), VoidStamp),
  (22, (ConstantNode (IntVal 32 (3))), IntegerStamp 32 (3) (3)),
  (23, (IntegerLessThanNode 1 22), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (BeginNode 33), VoidStamp),
  (26, (BeginNode 24), VoidStamp),
  (27, (IfNode 61 25 26), VoidStamp),
  (28, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (29, (IntegerLessThanNode 1 3), VoidStamp),
  (30, (BeginNode 39), VoidStamp),
  (31, (EndNode), VoidStamp),
  (32, (BeginNode 31), VoidStamp),
  (33, (IfNode 62 32 30), VoidStamp),
  (34, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (35, (IntegerLessThanNode 1 28), VoidStamp),
  (36, (BeginNode 45), VoidStamp),
  (37, (EndNode), VoidStamp),
  (38, (BeginNode 37), VoidStamp),
  (39, (IfNode 62 38 36), VoidStamp),
  (40, (ConstantNode (IntVal 32 (-3))), IntegerStamp 32 (-3) (-3)),
  (41, (IntegerLessThanNode 1 34), VoidStamp),
  (42, (BeginNode 49), VoidStamp),
  (43, (EndNode), VoidStamp),
  (44, (BeginNode 43), VoidStamp),
  (45, (IfNode 62 44 42), VoidStamp),
  (46, (IntegerEqualsNode 1 8), VoidStamp),
  (47, (BeginNode 54), VoidStamp),
  (48, (BeginNode 51), VoidStamp),
  (49, (IfNode 62 48 47), VoidStamp),
  (50, (ConstantNode (IntVal 32 (42))), IntegerStamp 32 (42) (42)),
  (51, (StoreFieldNode 51 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 50  (Some 52)  None 53), VoidStamp),
  (52, (FrameState []  None None None), IllegalStamp),
  (53, (EndNode), VoidStamp),
  (54, (StoreFieldNode 54 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 8  (Some 55)  None 56), VoidStamp),
  (55, (FrameState []  None None None), IllegalStamp),
  (56, (EndNode), VoidStamp),
  (57, (FrameState []  None None None), IllegalStamp),
  (58, (StoreFieldNode 58 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3  (Some 59)  None 60), VoidStamp),
  (59, (FrameState []  None None None), IllegalStamp),
  (60, (ReturnNode  None  None), VoidStamp),
  (61, (ConstantNode (IntVal 1 (1))), VoidStamp),
  (62, (ConstantNode (IntVal 1 (0))), VoidStamp)
  ]"

values "{g' . ConditionalEliminationPhase ConditionalEliminationTest1_test3Snippet_initial  (0, {}, [], []) g'}"
definition ConditionalEliminationTest1_test3Snippet_isabelle :: IRGraph where
  "ConditionalEliminationTest1_test3Snippet_isabelle  = irgraph [
    (33, IfNode 64 32 30, VoidStamp),
    (64, ConstantNode (IntVal 1 0), IntegerStamp 32 (- 2147483648) 2147483647),
    (27, IfNode 63 25 26, VoidStamp),
    (63, ConstantNode (IntVal 1 1), IntegerStamp 32 (- 2147483648) 2147483647),
    (21, IfNode 62 19 20, VoidStamp),
    (62, ConstantNode (IntVal 1 1), IntegerStamp 32 (- 2147483648) 2147483647),
    (15, IfNode 61 13 14, VoidStamp),
    (61, ConstantNode (IntVal 1 1), IntegerStamp 32 (- 2147483648) 2147483647),
    (0, StartNode (Some 2) 7, VoidStamp),
    (1, ParameterNode 0, IntegerStamp 32 (- 2147483648) 2147483647),
    (2, FrameState [] None None None, IllegalStamp),
    (3, ConstantNode (IntVal 32 0), IntegerStamp 32 0 0),
    (4, IntegerEqualsNode 1 3, VoidStamp), (5, BeginNode 10, VoidStamp),
    (6, BeginNode 15, VoidStamp), (7, IfNode 4 6 5, VoidStamp),
    (8, ConstantNode (IntVal 32 1), IntegerStamp 32 1 1),
    (9, IntegerLessThanNode 1 8, VoidStamp), (10, EndNode, VoidStamp),
    (11, MergeNode [10, 12, 18, 24, 31, 37, 43, 53, 56] (Some 57) 58, VoidStamp),
    (12, EndNode, VoidStamp), (13, BeginNode 21, VoidStamp),
    (14, BeginNode 12, VoidStamp), (15, IfNode 9 13 14, VoidStamp),
    (16, ConstantNode (IntVal 32 2), IntegerStamp 32 2 2),
    (17, IntegerLessThanNode 1 16, VoidStamp), (18, EndNode, VoidStamp),
    (19, BeginNode 27, VoidStamp), (20, BeginNode 18, VoidStamp),
    (21, IfNode 17 19 20, VoidStamp),
    (22, ConstantNode (IntVal 32 3), IntegerStamp 32 3 3),
    (23, IntegerLessThanNode 1 22, VoidStamp), (24, EndNode, VoidStamp),
    (25, BeginNode 33, VoidStamp), (26, BeginNode 24, VoidStamp),
    (27, IfNode 23 25 26, VoidStamp),
    (28, ConstantNode (IntVal 32 (- 1)), IntegerStamp 32 (- 1) (- 1)),
    (29, IntegerLessThanNode 1 3, VoidStamp), (30, BeginNode 39, VoidStamp),
    (31, EndNode, VoidStamp), (32, BeginNode 31, VoidStamp),
    (33, IfNode 29 32 30, VoidStamp),
    (34, ConstantNode (IntVal 32 (- 2)), IntegerStamp 32 (- 2) (- 2)),
    (35, IntegerLessThanNode 1 28, VoidStamp), (36, BeginNode 45, VoidStamp),
    (37, EndNode, VoidStamp), (38, BeginNode 37, VoidStamp),
    (39, IfNode 35 38 36, VoidStamp),
    (40, ConstantNode (IntVal 32 (- 3)), IntegerStamp 32 (- 3) (- 3)),
    (41, IntegerLessThanNode 1 34, VoidStamp), (42, BeginNode 49, VoidStamp),
    (43, EndNode, VoidStamp), (44, BeginNode 43, VoidStamp),
    (45, IfNode 41 44 42, VoidStamp), (46, IntegerEqualsNode 1 8, VoidStamp),
    (47, BeginNode 54, VoidStamp), (48, BeginNode 51, VoidStamp),
    (49, IfNode 46 48 47, VoidStamp),
    (50, ConstantNode (IntVal 32 42), IntegerStamp 32 42 42),
    (51,
     StoreFieldNode 51
      ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 50
      (Some 52) None 53,
     VoidStamp),
    (52, FrameState [] None None None, IllegalStamp), (53, EndNode, VoidStamp),
    (54,
     StoreFieldNode 54
      ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 8
      (Some 55) None 56,
     VoidStamp),
    (55, FrameState [] None None None, IllegalStamp), (56, EndNode, VoidStamp),
    (57, FrameState [] None None None, IllegalStamp),
    (58,
     StoreFieldNode 58
      ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3
      (Some 59) None 60,
     VoidStamp),
    (59, FrameState [] None None None, IllegalStamp),
    (60, ReturnNode None None, VoidStamp)]"

(* Fails. Optimisation for this node in Graal uses tryFold and flow typing *)
value "diffNodesGraph ConditionalEliminationTest1_test3Snippet_isabelle ConditionalEliminationTest1_test3Snippet_final"
value "eqGraph ConditionalEliminationTest1_test3Snippet_isabelle ConditionalEliminationTest1_test3Snippet_final"







(* initial: ConditionalEliminationTest4_test1Snippet*)
definition ConditionalEliminationTest4_test1Snippet_initial :: IRGraph where
  "ConditionalEliminationTest4_test1Snippet_initial = irgraph [
  (0, (StartNode  (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState []  None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 8), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (EndNode), VoidStamp),
  (9, (MergeNode  [8, 10]  (Some 16) 18), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (BeginNode 15), VoidStamp),
  (12, (BeginNode 10), VoidStamp),
  (13, (IfNode 4 11 12), VoidStamp),
  (14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ReturnNode  (Some 14)  None), VoidStamp),
  (16, (FrameState []  None None None), IllegalStamp),
  (17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (18, (ReturnNode  (Some 17)  None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest4_test1Snippet*)
definition ConditionalEliminationTest4_test1Snippet_final :: IRGraph where
  "ConditionalEliminationTest4_test1Snippet_final = irgraph [
  (0, (StartNode  (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState []  None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 8), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (EndNode), VoidStamp),
  (9, (MergeNode  [8, 10]  (Some 16) 18), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (BeginNode 15), VoidStamp),
  (12, (BeginNode 10), VoidStamp),
  (13, (IfNode 19 11 12), VoidStamp),
  (14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ReturnNode  (Some 14)  None), VoidStamp),
  (16, (FrameState []  None None None), IllegalStamp),
  (17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (18, (ReturnNode  (Some 17)  None), VoidStamp),
  (19, (ConstantNode (IntVal 1 (1))), VoidStamp)
  ]"

values "{g' . ConditionalEliminationPhase ConditionalEliminationTest4_test1Snippet_initial  (0, {}, [], []) g'}"
definition ConditionalEliminationTest4_test1Snippet_isabelle :: IRGraph where
  "ConditionalEliminationTest4_test1Snippet_isabelle = irgraph
   [(13, IfNode 19 11 12, VoidStamp),
    (19, ConstantNode (IntVal 1 1), IntegerStamp 32 (- 2147483648) 2147483647),
    (0, StartNode (Some 3) 7, VoidStamp),
    (1, ParameterNode 0, IntegerStamp 32 (- 2147483648) 2147483647),
    (2, ParameterNode 1, IntegerStamp 32 (- 2147483648) 2147483647),
    (3, FrameState [] None None None, IllegalStamp),
    (4, IntegerLessThanNode 2 1, VoidStamp), (5, BeginNode 8, VoidStamp),
    (6, BeginNode 13, VoidStamp), (7, IfNode 4 6 5, VoidStamp),
    (8, EndNode, VoidStamp), (9, MergeNode [8, 10] (Some 16) 18, VoidStamp),
    (10, EndNode, VoidStamp), (11, BeginNode 15, VoidStamp),
    (12, BeginNode 10, VoidStamp), (13, IfNode 4 11 12, VoidStamp),
    (14, ConstantNode (IntVal 32 1), IntegerStamp 32 1 1),
    (15, ReturnNode (Some 14) None, VoidStamp),
    (16, FrameState [] None None None, IllegalStamp),
    (17, ConstantNode (IntVal 32 2), IntegerStamp 32 2 2),
    (18, ReturnNode (Some 17) None, VoidStamp)]"

(* Works for now *)
value "diffNodesGraph ConditionalEliminationTest4_test1Snippet_isabelle ConditionalEliminationTest4_test1Snippet_final"
value "eqGraph ConditionalEliminationTest4_test1Snippet_isabelle ConditionalEliminationTest4_test1Snippet_final"






(* initial: ConditionalEliminationTest4_test2Snippet*)
definition ConditionalEliminationTest4_test2Snippet_initial :: IRGraph where
  "ConditionalEliminationTest4_test2Snippet_initial = irgraph [
  (0, (StartNode  (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
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
  (14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ReturnNode  (Some 14)  None), VoidStamp),
  (16, (FrameState []  None None None), IllegalStamp),
  (17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (18, (ReturnNode  (Some 17)  None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest4_test2Snippet*)
definition ConditionalEliminationTest4_test2Snippet_final :: IRGraph where
  "ConditionalEliminationTest4_test2Snippet_final = irgraph [
  (0, (StartNode  (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
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
  (13, (IfNode 19 11 12), VoidStamp),
  (14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ReturnNode  (Some 14)  None), VoidStamp),
  (16, (FrameState []  None None None), IllegalStamp),
  (17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (18, (ReturnNode  (Some 17)  None), VoidStamp),
  (19, (ConstantNode (IntVal 1 (1))), VoidStamp)
  ]"

values "{g' . ConditionalEliminationPhase ConditionalEliminationTest4_test2Snippet_initial  (0, {}, [], []) g'}"
definition ConditionalEliminationTest4_test2Snippet_isabelle :: IRGraph where
  "ConditionalEliminationTest4_test2Snippet_isabelle = irgraph
   [(13, IfNode 19 11 12, VoidStamp),
    (19, ConstantNode (IntVal 1 1), IntegerStamp 32 (- 2147483648) 2147483647),
    (0, StartNode (Some 3) 7, VoidStamp),
    (1, ParameterNode 0, IntegerStamp 32 (- 2147483648) 2147483647),
    (2, ParameterNode 1, IntegerStamp 32 (- 2147483648) 2147483647),
    (3, FrameState [] None None None, IllegalStamp),
    (4, IntegerLessThanNode 1 2, VoidStamp), (5, BeginNode 8, VoidStamp),
    (6, BeginNode 13, VoidStamp), (7, IfNode 4 6 5, VoidStamp),
    (8, EndNode, VoidStamp), (9, MergeNode [8, 10] (Some 16) 18, VoidStamp),
    (10, EndNode, VoidStamp), (11, BeginNode 15, VoidStamp),
    (12, BeginNode 10, VoidStamp), (13, IfNode 4 11 12, VoidStamp),
    (14, ConstantNode (IntVal 32 1), IntegerStamp 32 1 1),
    (15, ReturnNode (Some 14) None, VoidStamp),
    (16, FrameState [] None None None, IllegalStamp),
    (17, ConstantNode (IntVal 32 2), IntegerStamp 32 2 2),
    (18, ReturnNode (Some 17) None, VoidStamp)]"

(* Works for now *)
value "diffNodesGraph ConditionalEliminationTest4_test2Snippet_isabelle ConditionalEliminationTest4_test2Snippet_final"
value "eqGraph ConditionalEliminationTest4_test2Snippet_isabelle ConditionalEliminationTest4_test2Snippet_final"

end