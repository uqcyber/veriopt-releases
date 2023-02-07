section \<open>Testing of IR Semantics based on GraalVM Unit Tests\<close>

theory UnitTesting
  imports
    Semantics.IRStepObj
begin

declare [[ML_source_trace]]

subsection \<open>Unit test helper functions\<close>

inductive static_test :: "IRGraph \<Rightarrow> Value list \<Rightarrow> Value \<Rightarrow> bool"
  where
  "\<lbrakk>config0 = (g, 0, new_map_state, ps);
    (\<lambda>x. None) \<turnstile> ([config0, config0], new_heap) | [] \<longrightarrow>* ((end # xs), heap) | l \<rbrakk>
    \<Longrightarrow> static_test g ps ((prod.fst(prod.snd(prod.snd end))) 0)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testE) static_test .


(* get the return value of the top-most function *)
fun get_result :: "(IRGraph \<times> ID \<times> MapState \<times> Params) \<Rightarrow> Value" where
  "get_result (g,i,m,p) = m 0"


text \<open>$object_test$ and $program_test$ run a static initialisation block first
   (to initialise static fields etc.), then a named method graph.  
  The $program_test$ driver takes an expected result value as an input,
  whereas the $object_test$ driver takes a result-checking function as input.
  This result-checking function is given the output heap as well as the result of the method,
  so that it can check various fields or properties of the method output.
  \<close>
inductive object_test :: "Program \<Rightarrow> Signature \<Rightarrow> Value list \<Rightarrow> (Value \<Rightarrow> FieldRefHeap \<Rightarrow> bool) => bool"
  where
  InitStatics:
  "\<lbrakk>Some init = prog '''';
    config0 = (init, 0, new_map_state, ps);
    prog \<turnstile> ([config0, config0], new_heap) | [] \<longrightarrow>* ((end1 # xs1), heap1) | l1;
    
    Some g = prog m;
    config1 = (g, 0, new_map_state, ps);
    prog \<turnstile> ([config1, config1], heap1) | [] \<longrightarrow>* ((end2 # xs2), heap2) | l2;
    result = get_result end2;
    checker result heap2 \<rbrakk>
    \<Longrightarrow> object_test prog m ps checker" |

  NoStatics:
  "\<lbrakk>'''' \<notin> dom prog;
    Some g = prog m;
    config1 = (g, 0, new_map_state, ps);
    prog \<turnstile> ([config1, config1], new_heap) | [] \<longrightarrow>* ((end2 # xs2), heap2) | l2;
    result = get_result end2;
    checker result heap2 \<rbrakk>
    \<Longrightarrow> object_test prog m ps checker"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testObj) object_test .

inductive program_test :: "Program \<Rightarrow> Signature \<Rightarrow> Value list \<Rightarrow> Value => bool"
  where
  "object_test prog m ps (\<lambda> x h. x = result)
    \<Longrightarrow> program_test prog m ps result"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testP) program_test .


subsection \<open>Unit test helper functions - Debug versions\<close>

inductive program_test_debug :: "Program \<Rightarrow> Signature \<Rightarrow> Value list \<Rightarrow> nat \<Rightarrow> ID \<times> MapState \<times> Params \<Rightarrow> bool"
  where
  NoStatics:
  "\<lbrakk>'''' \<notin> dom prog;
    Some g = prog m;
    config1 = (g, 0, new_map_state, ps);
    exec_debug prog ([config1, config1], new_heap) steps ((end2 # xs2), heap2) \<rbrakk>
    \<Longrightarrow> program_test_debug prog m ps steps (prod.snd end2)"
(* output end2 has type: "(IRGraph \<times> ID \<times> MapState \<times> Params)" *)
code_pred (
    modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testPin,
           i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as testPout) program_test_debug .

(* Example of using program_test_debug:
values "{m | m . program_test_debug prog mathodName paramList steps m}"
*)

inductive static_test_debug :: "IRGraph \<Rightarrow> Value list \<Rightarrow> nat \<Rightarrow>  ID \<times> MapState \<times> Params \<Rightarrow> bool"
  where
  "program_test_debug (Map.empty (''_'' \<mapsto> g)) ''_'' ps steps out 
   \<Longrightarrow> static_test_debug g ps steps out"
code_pred (
    modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testGin,
           i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as testGout) static_test_debug .

(* Example of using static_test_debug:
values "{m | m . static_test_debug graph paramList steps m}"
*)



subsection \<open>Start of Translated Unit Tests\<close>




(* temporary back-compatible functions for tests *)
fun IntVal32 :: "int64 \<Rightarrow> Value" where
  "IntVal32 val = new_int 32 val"

fun IntVal64 :: "int64 \<Rightarrow> Value" where
  "IntVal64 val = new_int 64 val"


(* Lorg/graalvm/compiler/jtt/hotpath/HP_scope02;.HP_scope02_test*)
definition unit_HP_scope02_test :: IRGraph where
  "unit_HP_scope02_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 28] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [3, 8] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 27] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 8 1), VoidStamp),
  (12, (LoopExitNode 6 (Some 14) 29), VoidStamp),
  (13, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 25), VoidStamp),
  (16, (IfNode 10 15 12), VoidStamp),
  (17, (ConstantNode (new_int 32 (20))), IntegerStamp 32 (20) (20)),
  (18, (ConstantNode (new_int 32 (21))), IntegerStamp 32 (21) (21)),
  (19, (IntegerLessThanNode 8 18), VoidStamp),
  (21, (LoopExitNode 6 (Some 23) 31), VoidStamp),
  (22, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (BeginNode 28), VoidStamp),
  (25, (IfNode 19 24 21), VoidStamp),
  (26, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (27, (AddNode 8 26), IntegerStamp 32 (-2147483648) (2147483647)),
  (28, (LoopEndNode 6), VoidStamp),
  (29, (EndNode), VoidStamp),
  (30, (MergeNode [29, 31] (Some 33) 34), VoidStamp),
  (31, (EndNode), VoidStamp),
  (32, (ValuePhiNode 32 [13, 22] 30), IntegerStamp 32 (-2147483648) (2147483647)),
  (33, (FrameState [] None None None), IllegalStamp),
  (34, (ReturnNode (Some 32) None), VoidStamp)
  ]"
value "static_test unit_HP_scope02_test  [(new_int 32 (40))] (new_int 32 (20))"

value "static_test unit_HP_scope02_test  [(new_int 32 (22))] (new_int 32 (20))"


(* Lorg/graalvm/compiler/core/test/IfCanonicalizerTest;.IfCanonicalizerTest_test10Snippet*)
definition unit_IfCanonicalizerTest_test10Snippet :: IRGraph where
  "unit_IfCanonicalizerTest_test10Snippet = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 64 (-1))), IntegerStamp 64 (-1) (-1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (BeginNode 20), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (IntVal 64 (0))), IntegerStamp 64 (0) (0)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [8, 14, 19] 16), IntegerStamp 64 (-1) (1)),
  (19, (ConstantNode (IntVal 64 (1))), IntegerStamp 64 (1) (1)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]"
value "static_test unit_IfCanonicalizerTest_test10Snippet  [(new_int 32 (0)), (new_int 32 (1))] (IntVal 64 (-1))"


(* Lorg/graalvm/compiler/core/test/IfCanonicalizerTest;.IfCanonicalizerTest_test7Snippet*)
definition unit_IfCanonicalizerTest_test7Snippet :: IRGraph where
  "unit_IfCanonicalizerTest_test7Snippet = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1024))), IntegerStamp 32 (1024) (1024)),
  (9, (IntegerLessThanNode 1 8), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (MergeNode [10, 12] (Some 19) 22), VoidStamp),
  (12, (EndNode), VoidStamp),
  (13, (BeginNode 18), VoidStamp),
  (14, (BeginNode 12), VoidStamp),
  (15, (IfNode 9 13 14), VoidStamp),
  (16, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (17, (AddNode 1 16), IntegerStamp 32 (-2147483648) (2147483647)),
  (18, (ReturnNode (Some 17) None), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (21, (AddNode 1 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (ReturnNode (Some 21) None), VoidStamp)
  ]"
value "static_test unit_IfCanonicalizerTest_test7Snippet  [(new_int 32 (-1))] (new_int 32 (-2))"


(* Lorg/graalvm/compiler/core/test/IfCanonicalizerTest;.IfCanonicalizerTest_test8Snippet*)
definition unit_IfCanonicalizerTest_test8Snippet :: IRGraph where
  "unit_IfCanonicalizerTest_test8Snippet = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1024))), IntegerStamp 32 (1024) (1024)),
  (9, (ConstantNode (new_int 32 (1025))), IntegerStamp 32 (1025) (1025)),
  (10, (IntegerLessThanNode 1 9), VoidStamp),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 20) 23), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (BeginNode 19), VoidStamp),
  (15, (BeginNode 13), VoidStamp),
  (16, (IfNode 10 14 15), VoidStamp),
  (17, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (18, (AddNode 1 17), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (ReturnNode (Some 18) None), VoidStamp),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (22, (AddNode 1 21), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (ReturnNode (Some 22) None), VoidStamp)
  ]"
value "static_test unit_IfCanonicalizerTest_test8Snippet  [(new_int 32 (-1))] (new_int 32 (-2))"


(* Lorg/graalvm/compiler/core/test/IfCanonicalizerTest;.IfCanonicalizerTest_test9Snippet*)
definition unit_IfCanonicalizerTest_test9Snippet :: IRGraph where
  "unit_IfCanonicalizerTest_test9Snippet = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (1024))), IntegerStamp 32 (1024) (1024)),
  (11, (IntegerLessThanNode 1 10), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (BeginNode 20), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [8, 10, 19] 16), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (AddNode 1 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]"
value "static_test unit_IfCanonicalizerTest_test9Snippet  [(new_int 32 (-1))] (new_int 32 (1))"

value "static_test unit_IfCanonicalizerTest_test9Snippet  [(new_int 32 (1025))] (new_int 32 (1024))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare0*)
definition unit_IfNodeCanonicalizationsTest_compare0 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare0 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (12, (ConditionalNode 4 10 11), IntegerStamp 32 (2) (3)),
  (13, (EndNode), VoidStamp),
  (14, (MergeNode [13, 15] (Some 17) 18), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (ValuePhiNode 16 [8, 12] 14), IntegerStamp 32 (1) (3)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare0  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare0  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare0  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare1*)
definition unit_IfNodeCanonicalizationsTest_compare1 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare1 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (10, (ConditionalNode 4 8 9), IntegerStamp 32 (1) (2)),
  (12, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (13, (EndNode), VoidStamp),
  (14, (MergeNode [13, 15] (Some 17) 18), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (ValuePhiNode 16 [10, 12] 14), IntegerStamp 32 (1) (3)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare1  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare1  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare1  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare10*)
definition unit_IfNodeCanonicalizationsTest_compare10 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare10 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (12, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (2) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare10  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare10  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare10  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare11*)
definition unit_IfNodeCanonicalizationsTest_compare11 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare11 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerEqualsNode 1 2), VoidStamp),
  (9, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (10, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (ConditionalNode 8 9 10), IntegerStamp 32 (1) (2)),
  (13, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [11, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare11  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare11  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare11  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare12*)
definition unit_IfNodeCanonicalizationsTest_compare12 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare12 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 1 2), VoidStamp),
  (11, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (12, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (2) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare12  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare12  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare12  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare13*)
definition unit_IfNodeCanonicalizationsTest_compare13 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare13 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 1 2), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (ConditionalNode 8 9 10), IntegerStamp 32 (1) (2)),
  (13, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [11, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare13  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare13  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare13  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare14*)
definition unit_IfNodeCanonicalizationsTest_compare14 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare14 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (12, (ConditionalNode 4 10 11), IntegerStamp 32 (2) (3)),
  (13, (EndNode), VoidStamp),
  (14, (MergeNode [13, 15] (Some 17) 18), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (ValuePhiNode 16 [8, 12] 14), IntegerStamp 32 (1) (3)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare14  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare14  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare14  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare15*)
definition unit_IfNodeCanonicalizationsTest_compare15 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare15 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (10, (ConditionalNode 4 8 9), IntegerStamp 32 (1) (2)),
  (12, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (13, (EndNode), VoidStamp),
  (14, (MergeNode [13, 15] (Some 17) 18), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (ValuePhiNode 16 [10, 12] 14), IntegerStamp 32 (1) (3)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare15  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare15  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare15  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare16*)
definition unit_IfNodeCanonicalizationsTest_compare16 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare16 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (11, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (12, (ConditionalNode 4 10 11), IntegerStamp 32 (2) (3)),
  (13, (EndNode), VoidStamp),
  (14, (MergeNode [13, 15] (Some 17) 18), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (ValuePhiNode 16 [8, 12] 14), IntegerStamp 32 (1) (3)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare16  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare16  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare16  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare17*)
definition unit_IfNodeCanonicalizationsTest_compare17 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare17 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConditionalNode 4 8 9), IntegerStamp 32 (1) (2)),
  (12, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (13, (EndNode), VoidStamp),
  (14, (MergeNode [13, 15] (Some 17) 18), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (ValuePhiNode 16 [10, 12] 14), IntegerStamp 32 (1) (3)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare17  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare17  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare17  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare18*)
definition unit_IfNodeCanonicalizationsTest_compare18 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare18 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 1 2), VoidStamp),
  (11, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (12, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (2) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare18  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare18  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare18  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare19*)
definition unit_IfNodeCanonicalizationsTest_compare19 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare19 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 1 2), VoidStamp),
  (9, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (10, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (ConditionalNode 8 9 10), IntegerStamp 32 (1) (2)),
  (13, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [11, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare19  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare19  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare19  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare2*)
definition unit_IfNodeCanonicalizationsTest_compare2 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare2 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 2 1), VoidStamp),
  (11, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (12, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (2) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare2  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare2  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare2  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare20*)
definition unit_IfNodeCanonicalizationsTest_compare20 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare20 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (12, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (2) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare20  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare20  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare20  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare21*)
definition unit_IfNodeCanonicalizationsTest_compare21 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare21 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerEqualsNode 1 2), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (ConditionalNode 8 9 10), IntegerStamp 32 (1) (2)),
  (13, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [11, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare21  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare21  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare21  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare22*)
definition unit_IfNodeCanonicalizationsTest_compare22 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare22 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (12, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (2) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare22  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare22  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare22  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare23*)
definition unit_IfNodeCanonicalizationsTest_compare23 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare23 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerEqualsNode 1 2), VoidStamp),
  (9, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (10, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (ConditionalNode 8 9 10), IntegerStamp 32 (1) (2)),
  (13, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [11, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare23  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare23  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare23  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare24*)
definition unit_IfNodeCanonicalizationsTest_compare24 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare24 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 1 2), VoidStamp),
  (11, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (12, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (2) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare24  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare24  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare24  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare25*)
definition unit_IfNodeCanonicalizationsTest_compare25 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare25 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 1 2), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (ConditionalNode 8 9 10), IntegerStamp 32 (1) (2)),
  (13, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [11, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare25  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare25  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare25  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare26*)
definition unit_IfNodeCanonicalizationsTest_compare26 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare26 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (12, (ConditionalNode 4 10 11), IntegerStamp 32 (2) (3)),
  (13, (EndNode), VoidStamp),
  (14, (MergeNode [13, 15] (Some 17) 18), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (ValuePhiNode 16 [8, 12] 14), IntegerStamp 32 (1) (3)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare26  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare26  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare26  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare27*)
definition unit_IfNodeCanonicalizationsTest_compare27 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare27 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (10, (ConditionalNode 4 8 9), IntegerStamp 32 (1) (2)),
  (12, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (13, (EndNode), VoidStamp),
  (14, (MergeNode [13, 15] (Some 17) 18), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (ValuePhiNode 16 [10, 12] 14), IntegerStamp 32 (1) (3)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare27  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare27  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare27  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare28*)
definition unit_IfNodeCanonicalizationsTest_compare28 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare28 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (11, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (12, (ConditionalNode 4 10 11), IntegerStamp 32 (2) (3)),
  (13, (EndNode), VoidStamp),
  (14, (MergeNode [13, 15] (Some 17) 18), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (ValuePhiNode 16 [8, 12] 14), IntegerStamp 32 (1) (3)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare28  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare28  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare28  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare29*)
definition unit_IfNodeCanonicalizationsTest_compare29 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare29 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConditionalNode 4 8 9), IntegerStamp 32 (1) (2)),
  (12, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (13, (EndNode), VoidStamp),
  (14, (MergeNode [13, 15] (Some 17) 18), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (ValuePhiNode 16 [10, 12] 14), IntegerStamp 32 (1) (3)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare29  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare29  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare29  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare3*)
definition unit_IfNodeCanonicalizationsTest_compare3 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare3 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 2 1), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (ConditionalNode 8 9 10), IntegerStamp 32 (1) (2)),
  (13, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [11, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare3  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare3  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare3  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare30*)
definition unit_IfNodeCanonicalizationsTest_compare30 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare30 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 1 2), VoidStamp),
  (11, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (12, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (2) (3)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (1) (3)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IfNodeCanonicalizationsTest_compare30  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare30  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare30  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"

end
