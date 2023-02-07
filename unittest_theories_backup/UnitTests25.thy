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


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual42*)
definition unit_TrichotomyTest_testEqual42 :: Program where
  "unit_TrichotomyTest_testEqual42 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual42(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerLessThanNode 1 2), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (BeginNode 17), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (IntegerEqualsNode 1 2), VoidStamp),
  (10, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (11, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (12, (ConditionalNode 9 10 11), IntegerStamp 32 (0) (1)),
  (14, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17] (Some 20) 23), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [12, 14] 16), IntegerStamp 32 (-1) (1)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (FrameState [] (Some 19) None None), IllegalStamp),
  (21, (IntegerEqualsNode 18 10), VoidStamp),
  (22, (ConditionalNode 21 11 10), IntegerStamp 32 (0) (1)),
  (23, (ReturnNode (Some 22) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare42(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerEqualsNode 1 2), VoidStamp),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (ConditionalNode 8 9 10), IntegerStamp 32 (0) (1)),
  (13, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [11, 13] 15), IntegerStamp 32 (-1) (1)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual42 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual42(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual42 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual42(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual42 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual42(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual43*)
definition unit_TrichotomyTest_testEqual43 :: Program where
  "unit_TrichotomyTest_testEqual43 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual43(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerLessThanNode 1 2), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (BeginNode 17), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (IntegerLessThanNode 2 1), VoidStamp),
  (10, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (12, (ConditionalNode 9 10 11), IntegerStamp 32 (0) (1)),
  (14, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17] (Some 20) 23), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [12, 14] 16), IntegerStamp 32 (-1) (1)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (FrameState [] (Some 19) None None), IllegalStamp),
  (21, (IntegerEqualsNode 18 11), VoidStamp),
  (22, (ConditionalNode 21 10 11), IntegerStamp 32 (0) (1)),
  (23, (ReturnNode (Some 22) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare43(II)I'' \<mapsto> irgraph [
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
  (10, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (11, (ConditionalNode 8 9 10), IntegerStamp 32 (0) (1)),
  (13, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [11, 13] 15), IntegerStamp 32 (-1) (1)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual43 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual43(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual43 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual43(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual43 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual43(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual44*)
definition unit_TrichotomyTest_testEqual44 :: Program where
  "unit_TrichotomyTest_testEqual44 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual44(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerLessThanNode 1 2), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (BeginNode 17), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (IntegerEqualsNode 1 2), VoidStamp),
  (10, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (11, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (12, (ConditionalNode 9 10 11), IntegerStamp 32 (0) (1)),
  (14, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17] (Some 20) 23), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [12, 14] 16), IntegerStamp 32 (-1) (1)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (FrameState [] (Some 19) None None), IllegalStamp),
  (21, (IntegerEqualsNode 18 10), VoidStamp),
  (22, (ConditionalNode 21 11 10), IntegerStamp 32 (0) (1)),
  (23, (ReturnNode (Some 22) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare44(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerEqualsNode 1 2), VoidStamp),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (ConditionalNode 8 9 10), IntegerStamp 32 (0) (1)),
  (13, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [11, 13] 15), IntegerStamp 32 (-1) (1)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual44 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual44(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual44 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual44(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual44 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual44(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual45*)
definition unit_TrichotomyTest_testEqual45 :: Program where
  "unit_TrichotomyTest_testEqual45 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual45(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerEqualsNode 1 2), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 21), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (IntegerLessThanNode 1 2), VoidStamp),
  (10, (BeginNode 18), VoidStamp),
  (11, (BeginNode 16), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (15, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 26), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [13, 15, 20] 17), IntegerStamp 32 (-1) (1)),
  (20, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 20), VoidStamp),
  (25, (ConditionalNode 24 15 20), IntegerStamp 32 (0) (1)),
  (26, (ReturnNode (Some 25) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare45(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 20), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 1 2), VoidStamp),
  (9, (BeginNode 17), VoidStamp),
  (10, (BeginNode 15), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (14, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [12, 14, 19] 16), IntegerStamp 32 (-1) (1)),
  (19, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual45 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual45(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual45 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual45(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual45 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual45(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual46*)
definition unit_TrichotomyTest_testEqual46 :: Program where
  "unit_TrichotomyTest_testEqual46 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual46(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerEqualsNode 1 2), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 21), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (IntegerLessThanNode 2 1), VoidStamp),
  (10, (BeginNode 16), VoidStamp),
  (11, (BeginNode 18), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (15, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 26), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [13, 15, 20] 17), IntegerStamp 32 (-1) (1)),
  (20, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 20), VoidStamp),
  (25, (ConditionalNode 24 15 20), IntegerStamp 32 (0) (1)),
  (26, (ReturnNode (Some 25) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare46(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 20), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 2 1), VoidStamp),
  (9, (BeginNode 15), VoidStamp),
  (10, (BeginNode 17), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (14, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [12, 14, 19] 16), IntegerStamp 32 (-1) (1)),
  (19, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual46 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual46(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual46 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual46(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual46 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual46(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual47*)
definition unit_TrichotomyTest_testEqual47 :: Program where
  "unit_TrichotomyTest_testEqual47 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual47(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerEqualsNode 1 2), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 21), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (IntegerLessThanNode 2 1), VoidStamp),
  (10, (BeginNode 18), VoidStamp),
  (11, (BeginNode 16), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 26), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [13, 15, 20] 17), IntegerStamp 32 (-1) (1)),
  (20, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 20), VoidStamp),
  (25, (ConditionalNode 24 13 20), IntegerStamp 32 (0) (1)),
  (26, (ReturnNode (Some 25) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare47(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 20), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 2 1), VoidStamp),
  (9, (BeginNode 17), VoidStamp),
  (10, (BeginNode 15), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (14, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [12, 14, 19] 16), IntegerStamp 32 (-1) (1)),
  (19, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual47 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual47(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual47 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual47(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual47 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual47(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual48*)
definition unit_TrichotomyTest_testEqual48 :: Program where
  "unit_TrichotomyTest_testEqual48 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual48(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerEqualsNode 1 2), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 21), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (IntegerLessThanNode 1 2), VoidStamp),
  (10, (BeginNode 16), VoidStamp),
  (11, (BeginNode 18), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 26), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [13, 15, 20] 17), IntegerStamp 32 (-1) (1)),
  (20, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 20), VoidStamp),
  (25, (ConditionalNode 24 13 20), IntegerStamp 32 (0) (1)),
  (26, (ReturnNode (Some 25) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare48(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 20), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerLessThanNode 1 2), VoidStamp),
  (9, (BeginNode 15), VoidStamp),
  (10, (BeginNode 17), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (14, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [12, 14, 19] 16), IntegerStamp 32 (-1) (1)),
  (19, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual48 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual48(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual48 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual48(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual48 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual48(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual5*)
definition unit_TrichotomyTest_testEqual5 :: Program where
  "unit_TrichotomyTest_testEqual5 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual5(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerLessThanNode 2 1), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (BeginNode 16), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (IntegerLessThanNode 1 2), VoidStamp),
  (12, (BeginNode 21), VoidStamp),
  (13, (BeginNode 18), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 26), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [9, 15, 20] 17), IntegerStamp 32 (-1) (1)),
  (20, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 20), VoidStamp),
  (25, (ConditionalNode 24 9 20), IntegerStamp 32 (0) (1)),
  (26, (ReturnNode (Some 25) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare5(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 1 2), VoidStamp),
  (11, (BeginNode 20), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [8, 14, 19] 16), IntegerStamp 32 (-1) (1)),
  (19, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual5 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual5(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual5 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual5(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual5 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual5(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual6*)
definition unit_TrichotomyTest_testEqual6 :: Program where
  "unit_TrichotomyTest_testEqual6 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual6(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerLessThanNode 2 1), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (BeginNode 16), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (IntegerEqualsNode 1 2), VoidStamp),
  (12, (BeginNode 21), VoidStamp),
  (13, (BeginNode 18), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 26), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [9, 15, 20] 17), IntegerStamp 32 (-1) (1)),
  (20, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 15), VoidStamp),
  (25, (ConditionalNode 24 9 15), IntegerStamp 32 (0) (1)),
  (26, (ReturnNode (Some 25) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare6(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (BeginNode 20), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [8, 14, 19] 16), IntegerStamp 32 (-1) (1)),
  (19, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual6 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual6(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual6 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual6(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual6 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual6(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual7*)
definition unit_TrichotomyTest_testEqual7 :: Program where
  "unit_TrichotomyTest_testEqual7 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual7(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerLessThanNode 2 1), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (BeginNode 16), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (IntegerLessThanNode 1 2), VoidStamp),
  (12, (BeginNode 18), VoidStamp),
  (13, (BeginNode 21), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 26), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [9, 15, 20] 17), IntegerStamp 32 (-1) (1)),
  (20, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 15), VoidStamp),
  (25, (ConditionalNode 24 9 15), IntegerStamp 32 (0) (1)),
  (26, (ReturnNode (Some 25) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare7(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 1 2), VoidStamp),
  (11, (BeginNode 17), VoidStamp),
  (12, (BeginNode 20), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [8, 14, 19] 16), IntegerStamp 32 (-1) (1)),
  (19, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual7 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual7(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual7 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual7(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual7 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual7(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual8*)
definition unit_TrichotomyTest_testEqual8 :: Program where
  "unit_TrichotomyTest_testEqual8 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual8(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerLessThanNode 2 1), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (BeginNode 16), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (IntegerEqualsNode 1 2), VoidStamp),
  (12, (BeginNode 18), VoidStamp),
  (13, (BeginNode 21), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 26), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [9, 15, 20] 17), IntegerStamp 32 (-1) (1)),
  (20, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 20), VoidStamp),
  (25, (ConditionalNode 24 9 20), IntegerStamp 32 (0) (1)),
  (26, (ReturnNode (Some 25) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare8(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (BeginNode 17), VoidStamp),
  (12, (BeginNode 20), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [8, 14, 19] 16), IntegerStamp 32 (-1) (1)),
  (19, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual8 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual8(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual8 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual8(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual8 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual8(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testEqual9*)
definition unit_TrichotomyTest_testEqual9 :: Program where
  "unit_TrichotomyTest_testEqual9 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual9(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerEqualsNode 1 2), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (BeginNode 16), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (11, (IntegerLessThanNode 1 2), VoidStamp),
  (12, (BeginNode 21), VoidStamp),
  (13, (BeginNode 18), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 26), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [9, 15, 20] 17), IntegerStamp 32 (-1) (1)),
  (20, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 9), VoidStamp),
  (25, (ConditionalNode 24 20 9), IntegerStamp 32 (0) (1)),
  (26, (ReturnNode (Some 25) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare9(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (IntegerLessThanNode 1 2), VoidStamp),
  (11, (BeginNode 20), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [8, 14, 19] 16), IntegerStamp 32 (-1) (1)),
  (19, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testEqual9 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual9(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testEqual9 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual9(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testEqual9 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testEqual9(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testGreater1*)
definition unit_TrichotomyTest_testGreater1 :: Program where
  "unit_TrichotomyTest_testGreater1 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater1(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerLessThanNode 1 2), VoidStamp),
  (6, (BeginNode 17), VoidStamp),
  (7, (BeginNode 15), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (11, (IntegerEqualsNode 1 2), VoidStamp),
  (12, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (13, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (14, (ConditionalNode 11 12 13), IntegerStamp 32 (0) (1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17] (Some 20) 23), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [9, 14] 16), IntegerStamp 32 (-1) (1)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (FrameState [] (Some 19) None None), IllegalStamp),
  (21, (IntegerEqualsNode 18 13), VoidStamp),
  (22, (ConditionalNode 21 13 12), IntegerStamp 32 (0) (1)),
  (23, (ReturnNode (Some 22) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare1(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (0) (1)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (-1) (1)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testGreater1 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater1(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testGreater1 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater1(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testGreater1 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater1(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testGreater10*)
definition unit_TrichotomyTest_testGreater10 :: Program where
  "unit_TrichotomyTest_testGreater10 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater10(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerLessThanNode 1 2), VoidStamp),
  (6, (BeginNode 17), VoidStamp),
  (7, (BeginNode 15), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (11, (IntegerEqualsNode 1 2), VoidStamp),
  (12, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (13, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (14, (ConditionalNode 11 12 13), IntegerStamp 32 (0) (1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17] (Some 20) 23), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [9, 14] 16), IntegerStamp 32 (-1) (1)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (FrameState [] (Some 19) None None), IllegalStamp),
  (21, (IntegerEqualsNode 18 13), VoidStamp),
  (22, (ConditionalNode 21 13 12), IntegerStamp 32 (0) (1)),
  (23, (ReturnNode (Some 22) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare4(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (0) (1)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (-1) (1)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testGreater10 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater10(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testGreater10 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater10(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testGreater10 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater10(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testGreater100*)
definition unit_TrichotomyTest_testGreater100 :: Program where
  "unit_TrichotomyTest_testGreater100 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater100(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerEqualsNode 1 2), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (BeginNode 16), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (11, (IntegerLessThanNode 2 1), VoidStamp),
  (12, (BeginNode 18), VoidStamp),
  (13, (BeginNode 21), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 26), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [9, 15, 20] 17), IntegerStamp 32 (-1) (1)),
  (20, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 20), VoidStamp),
  (25, (ConditionalNode 24 20 9), IntegerStamp 32 (0) (1)),
  (26, (ReturnNode (Some 25) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compare34(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (IntegerLessThanNode 2 1), VoidStamp),
  (11, (BeginNode 17), VoidStamp),
  (12, (BeginNode 20), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [8, 14, 19] 16), IntegerStamp 32 (-1) (1)),
  (19, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testGreater100 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater100(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testGreater100 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater100(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testGreater100 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testGreater100(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"

end
