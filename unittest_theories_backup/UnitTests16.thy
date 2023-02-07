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


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare31*)
definition unit_IfNodeCanonicalizationsTest_compare31 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare31 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare31  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare31  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare31  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare32*)
definition unit_IfNodeCanonicalizationsTest_compare32 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare32 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare32  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare32  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare32  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare33*)
definition unit_IfNodeCanonicalizationsTest_compare33 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare33 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare33  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare33  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare33  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare34*)
definition unit_IfNodeCanonicalizationsTest_compare34 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare34 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare34  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare34  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare34  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare35*)
definition unit_IfNodeCanonicalizationsTest_compare35 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare35 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare35  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare35  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare35  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare36*)
definition unit_IfNodeCanonicalizationsTest_compare36 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare36 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare36  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare36  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare36  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare37*)
definition unit_IfNodeCanonicalizationsTest_compare37 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare37 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare37  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare37  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare37  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare38*)
definition unit_IfNodeCanonicalizationsTest_compare38 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare38 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare38  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare38  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare38  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare39*)
definition unit_IfNodeCanonicalizationsTest_compare39 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare39 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare39  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare39  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare39  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare4*)
definition unit_IfNodeCanonicalizationsTest_compare4 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare4 = irgraph [
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
value "static_test unit_IfNodeCanonicalizationsTest_compare4  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare4  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare4  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare40*)
definition unit_IfNodeCanonicalizationsTest_compare40 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare40 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 2 1), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare40  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare40  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare40  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare41*)
definition unit_IfNodeCanonicalizationsTest_compare41 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare41 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 2 1), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare41  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare41  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare41  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare42*)
definition unit_IfNodeCanonicalizationsTest_compare42 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare42 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare42  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare42  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare42  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare43*)
definition unit_IfNodeCanonicalizationsTest_compare43 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare43 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare43  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare43  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare43  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare44*)
definition unit_IfNodeCanonicalizationsTest_compare44 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare44 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare44  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare44  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare44  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare45*)
definition unit_IfNodeCanonicalizationsTest_compare45 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare45 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare45  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare45  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare45  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare46*)
definition unit_IfNodeCanonicalizationsTest_compare46 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare46 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare46  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare46  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare46  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare47*)
definition unit_IfNodeCanonicalizationsTest_compare47 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare47 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare47  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare47  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare47  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare48*)
definition unit_IfNodeCanonicalizationsTest_compare48 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare48 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare48  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare48  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare48  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare49*)
definition unit_IfNodeCanonicalizationsTest_compare49 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare49 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare49  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare49  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare49  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare5*)
definition unit_IfNodeCanonicalizationsTest_compare5 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare5 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 2 1), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare5  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare5  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare5  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare50*)
definition unit_IfNodeCanonicalizationsTest_compare50 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare50 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare50  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare50  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare50  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare51*)
definition unit_IfNodeCanonicalizationsTest_compare51 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare51 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare51  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare51  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare51  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare52*)
definition unit_IfNodeCanonicalizationsTest_compare52 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare52 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 2 1), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare52  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare52  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare52  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare53*)
definition unit_IfNodeCanonicalizationsTest_compare53 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare53 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 2 1), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare53  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare53  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare53  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare54*)
definition unit_IfNodeCanonicalizationsTest_compare54 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare54 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare54  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare54  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare54  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare55*)
definition unit_IfNodeCanonicalizationsTest_compare55 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare55 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare55  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare55  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare55  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare56*)
definition unit_IfNodeCanonicalizationsTest_compare56 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare56 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare56  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare56  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare56  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare57*)
definition unit_IfNodeCanonicalizationsTest_compare57 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare57 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare57  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare57  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare57  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare58*)
definition unit_IfNodeCanonicalizationsTest_compare58 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare58 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare58  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare58  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare58  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"

end
