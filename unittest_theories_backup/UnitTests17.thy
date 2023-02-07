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


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare59*)
definition unit_IfNodeCanonicalizationsTest_compare59 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare59 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare59  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare59  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare59  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare6*)
definition unit_IfNodeCanonicalizationsTest_compare6 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare6 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare6  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare6  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare6  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare60*)
definition unit_IfNodeCanonicalizationsTest_compare60 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare60 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare60  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare60  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare60  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare61*)
definition unit_IfNodeCanonicalizationsTest_compare61 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare61 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare61  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare61  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare61  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare62*)
definition unit_IfNodeCanonicalizationsTest_compare62 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare62 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare62  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare62  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare62  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare63*)
definition unit_IfNodeCanonicalizationsTest_compare63 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare63 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare63  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare63  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare63  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare64*)
definition unit_IfNodeCanonicalizationsTest_compare64 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare64 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare64  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare64  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare64  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare65*)
definition unit_IfNodeCanonicalizationsTest_compare65 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare65 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare65  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare65  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare65  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare66*)
definition unit_IfNodeCanonicalizationsTest_compare66 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare66 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare66  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare66  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare66  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare67*)
definition unit_IfNodeCanonicalizationsTest_compare67 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare67 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare67  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare67  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare67  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare68*)
definition unit_IfNodeCanonicalizationsTest_compare68 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare68 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare68  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare68  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare68  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare69*)
definition unit_IfNodeCanonicalizationsTest_compare69 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare69 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare69  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare69  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare69  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare7*)
definition unit_IfNodeCanonicalizationsTest_compare7 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare7 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare7  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare7  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare7  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare70*)
definition unit_IfNodeCanonicalizationsTest_compare70 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare70 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare70  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare70  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare70  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare71*)
definition unit_IfNodeCanonicalizationsTest_compare71 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare71 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare71  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare71  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare71  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare8*)
definition unit_IfNodeCanonicalizationsTest_compare8 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare8 = irgraph [
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
value "static_test unit_IfNodeCanonicalizationsTest_compare8  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare8  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_IfNodeCanonicalizationsTest_compare8  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/IfNodeCanonicalizationsTest;.IfNodeCanonicalizationsTest_compare9*)
definition unit_IfNodeCanonicalizationsTest_compare9 :: IRGraph where
  "unit_IfNodeCanonicalizationsTest_compare9 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
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
value "static_test unit_IfNodeCanonicalizationsTest_compare9  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (3))"

value "static_test unit_IfNodeCanonicalizationsTest_compare9  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_IfNodeCanonicalizationsTest_compare9  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/InferStamp01;.InferStamp01_testi0*)
definition unit_InferStamp01_testi0 :: IRGraph where
  "unit_InferStamp01_testi0 = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 22] None (Some 9) 17), VoidStamp),
  (7, (ValuePhiNode 7 [1, 19] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 21] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (IntegerLessThanNode 8 10), VoidStamp),
  (13, (LoopExitNode 6 (Some 15) 23), VoidStamp),
  (14, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 22), VoidStamp),
  (17, (IfNode 11 16 13), VoidStamp),
  (18, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (19, (RightShiftNode 7 18), IntegerStamp 32 (-32768) (32767)),
  (20, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (21, (AddNode 8 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (LoopEndNode 6), VoidStamp),
  (23, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_InferStamp01_testi0  [(new_int 32 (2005440938))] (new_int 32 (0))"

value "static_test unit_InferStamp01_testi0  [(new_int 32 (-142042710))] (new_int 32 (-1))"


(* Lorg/graalvm/compiler/jtt/optimize/InferStamp01;.InferStamp01_testi1*)
definition unit_InferStamp01_testi1 :: IRGraph where
  "unit_InferStamp01_testi1 = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 22] None (Some 9) 17), VoidStamp),
  (7, (ValuePhiNode 7 [1, 19] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 21] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (IntegerLessThanNode 8 10), VoidStamp),
  (13, (LoopExitNode 6 (Some 15) 23), VoidStamp),
  (14, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 22), VoidStamp),
  (17, (IfNode 11 16 13), VoidStamp),
  (18, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (19, (UnsignedRightShiftNode 7 18), IntegerStamp 32 (0) (65535)),
  (20, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (21, (AddNode 8 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (LoopEndNode 6), VoidStamp),
  (23, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_InferStamp01_testi1  [(new_int 32 (2005440938))] (new_int 32 (0))"

value "static_test unit_InferStamp01_testi1  [(new_int 32 (-142042710))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/InferStamp01;.InferStamp01_testi2*)
definition unit_InferStamp01_testi2 :: IRGraph where
  "unit_InferStamp01_testi2 = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 22] None (Some 9) 17), VoidStamp),
  (7, (ValuePhiNode 7 [1, 19] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 21] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (IntegerLessThanNode 8 10), VoidStamp),
  (13, (LoopExitNode 6 (Some 15) 23), VoidStamp),
  (14, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 22), VoidStamp),
  (17, (IfNode 11 16 13), VoidStamp),
  (18, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (19, (LeftShiftNode 7 18), IntegerStamp 32 (-2147483648) (2147418112)),
  (20, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (21, (AddNode 8 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (LoopEndNode 6), VoidStamp),
  (23, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_InferStamp01_testi2  [(new_int 32 (2005440938))] (new_int 32 (0))"

value "static_test unit_InferStamp01_testi2  [(new_int 32 (-142042710))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/Inline01;.Inline01_test*)
definition unit_Inline01_test :: IRGraph where
  "unit_Inline01_test = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (AddNode 7 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_Inline01_test  [(new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_Inline01_test  [(new_int 32 (1))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/jtt/optimize/Inline02;.Inline02_test*)
definition unit_Inline02_test :: IRGraph where
  "unit_Inline02_test = irgraph [
  (0, (StartNode (Some 2) 13), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (AddNode 1 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (AddNode 6 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (AddNode 1 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (AddNode 10 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (13, (ReturnNode (Some 12) None), VoidStamp)
  ]"
value "static_test unit_Inline02_test  [(new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_Inline02_test  [(new_int 32 (1))] (new_int 32 (5))"

value "static_test unit_Inline02_test  [(new_int 32 (2))] (new_int 32 (8))"


(* Lorg/graalvm/compiler/jtt/lang/Int_greater01;.Int_greater01_test*)
definition unit_Int_greater01_test :: IRGraph where
  "unit_Int_greater01_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (BeginNode 10), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ReturnNode (Some 4) None), VoidStamp),
  (10, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Int_greater01_test  [(new_int 32 (-2147483648))] (new_int 32 (0))"

value "static_test unit_Int_greater01_test  [(new_int 32 (-2))] (new_int 32 (0))"

value "static_test unit_Int_greater01_test  [(new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_Int_greater01_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Int_greater01_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_Int_greater01_test  [(new_int 32 (2))] (new_int 32 (1))"

value "static_test unit_Int_greater01_test  [(new_int 32 (2147483647))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/lang/Int_greater02;.Int_greater02_test*)
definition unit_Int_greater02_test :: IRGraph where
  "unit_Int_greater02_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (4, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (BeginNode 12), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ReturnNode (Some 9) None), VoidStamp),
  (11, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (12, (ReturnNode (Some 11) None), VoidStamp)
  ]"
value "static_test unit_Int_greater02_test  [(new_int 32 (-2147483648))] (new_int 32 (0))"

value "static_test unit_Int_greater02_test  [(new_int 32 (-2))] (new_int 32 (0))"

value "static_test unit_Int_greater02_test  [(new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_Int_greater02_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Int_greater02_test  [(new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_Int_greater02_test  [(new_int 32 (4))] (new_int 32 (0))"

value "static_test unit_Int_greater02_test  [(new_int 32 (5))] (new_int 32 (0))"

value "static_test unit_Int_greater02_test  [(new_int 32 (6))] (new_int 32 (1))"

value "static_test unit_Int_greater02_test  [(new_int 32 (2147483647))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/lang/Int_greater03;.Int_greater03_test*)
definition unit_Int_greater03_test :: IRGraph where
  "unit_Int_greater03_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (-5))), IntegerStamp 32 (-5) (-5)),
  (4, (ConstantNode (new_int 32 (-4))), IntegerStamp 32 (-4) (-4)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (BeginNode 12), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ReturnNode (Some 9) None), VoidStamp),
  (11, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (12, (ReturnNode (Some 11) None), VoidStamp)
  ]"
value "static_test unit_Int_greater03_test  [(new_int 32 (-2147483648))] (new_int 32 (0))"

value "static_test unit_Int_greater03_test  [(new_int 32 (-6))] (new_int 32 (0))"

value "static_test unit_Int_greater03_test  [(new_int 32 (-5))] (new_int 32 (0))"

value "static_test unit_Int_greater03_test  [(new_int 32 (-4))] (new_int 32 (1))"

value "static_test unit_Int_greater03_test  [(new_int 32 (-1))] (new_int 32 (1))"

value "static_test unit_Int_greater03_test  [(new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_Int_greater03_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_Int_greater03_test  [(new_int 32 (2))] (new_int 32 (1))"

value "static_test unit_Int_greater03_test  [(new_int 32 (2147483647))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/lang/Int_greaterEqual01;.Int_greaterEqual01_test*)
definition unit_Int_greaterEqual01_test :: IRGraph where
  "unit_Int_greaterEqual01_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 9), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ReturnNode (Some 8) None), VoidStamp),
  (10, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Int_greaterEqual01_test  [(new_int 32 (-2147483648))] (new_int 32 (0))"

value "static_test unit_Int_greaterEqual01_test  [(new_int 32 (-2))] (new_int 32 (0))"

value "static_test unit_Int_greaterEqual01_test  [(new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_Int_greaterEqual01_test  [(new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_Int_greaterEqual01_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_Int_greaterEqual01_test  [(new_int 32 (2))] (new_int 32 (1))"

value "static_test unit_Int_greaterEqual01_test  [(new_int 32 (2147483647))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/lang/Int_greaterEqual02;.Int_greaterEqual02_test*)
definition unit_Int_greaterEqual02_test :: IRGraph where
  "unit_Int_greaterEqual02_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 9), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ReturnNode (Some 8) None), VoidStamp),
  (10, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_Int_greaterEqual02_test  [(new_int 32 (-2147483648))] (new_int 32 (0))"

value "static_test unit_Int_greaterEqual02_test  [(new_int 32 (-2))] (new_int 32 (0))"

value "static_test unit_Int_greaterEqual02_test  [(new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_Int_greaterEqual02_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Int_greaterEqual02_test  [(new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_Int_greaterEqual02_test  [(new_int 32 (4))] (new_int 32 (0))"

value "static_test unit_Int_greaterEqual02_test  [(new_int 32 (5))] (new_int 32 (1))"

value "static_test unit_Int_greaterEqual02_test  [(new_int 32 (6))] (new_int 32 (1))"

value "static_test unit_Int_greaterEqual02_test  [(new_int 32 (2147483647))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/lang/Int_greaterEqual03;.Int_greaterEqual03_test*)
definition unit_Int_greaterEqual03_test :: IRGraph where
  "unit_Int_greaterEqual03_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (-5))), IntegerStamp 32 (-5) (-5)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 9), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ReturnNode (Some 8) None), VoidStamp),
  (10, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_Int_greaterEqual03_test  [(new_int 32 (-2147483648))] (new_int 32 (0))"

value "static_test unit_Int_greaterEqual03_test  [(new_int 32 (-6))] (new_int 32 (0))"

value "static_test unit_Int_greaterEqual03_test  [(new_int 32 (-5))] (new_int 32 (1))"

value "static_test unit_Int_greaterEqual03_test  [(new_int 32 (-4))] (new_int 32 (1))"

value "static_test unit_Int_greaterEqual03_test  [(new_int 32 (-1))] (new_int 32 (1))"

value "static_test unit_Int_greaterEqual03_test  [(new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_Int_greaterEqual03_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_Int_greaterEqual03_test  [(new_int 32 (2))] (new_int 32 (1))"

value "static_test unit_Int_greaterEqual03_test  [(new_int 32 (2147483647))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/lang/Int_less01;.Int_less01_test*)
definition unit_Int_less01_test :: IRGraph where
  "unit_Int_less01_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 10), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ReturnNode (Some 8) None), VoidStamp),
  (10, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Int_less01_test  [(new_int 32 (-2147483648))] (new_int 32 (1))"

value "static_test unit_Int_less01_test  [(new_int 32 (-2))] (new_int 32 (1))"

value "static_test unit_Int_less01_test  [(new_int 32 (-1))] (new_int 32 (1))"

value "static_test unit_Int_less01_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Int_less01_test  [(new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_Int_less01_test  [(new_int 32 (2))] (new_int 32 (0))"

value "static_test unit_Int_less01_test  [(new_int 32 (2147483647))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/lang/Int_less02;.Int_less02_test*)
definition unit_Int_less02_test :: IRGraph where
  "unit_Int_less02_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ReturnNode (Some 8) None), VoidStamp),
  (10, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_Int_less02_test  [(new_int 32 (-2147483648))] (new_int 32 (1))"

value "static_test unit_Int_less02_test  [(new_int 32 (-2))] (new_int 32 (1))"

value "static_test unit_Int_less02_test  [(new_int 32 (-1))] (new_int 32 (1))"

value "static_test unit_Int_less02_test  [(new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_Int_less02_test  [(new_int 32 (4))] (new_int 32 (1))"

value "static_test unit_Int_less02_test  [(new_int 32 (5))] (new_int 32 (0))"

value "static_test unit_Int_less02_test  [(new_int 32 (6))] (new_int 32 (0))"

value "static_test unit_Int_less02_test  [(new_int 32 (2147483647))] (new_int 32 (0))"

end
