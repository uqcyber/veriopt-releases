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


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testSmallerEqual6*)
definition unit_TrichotomyTest_testSmallerEqual6 :: Program where
  "unit_TrichotomyTest_testSmallerEqual6 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual6(II)Z'' \<mapsto> irgraph [
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
  (24, (IntegerLessThanNode 19 9), VoidStamp),
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
value "program_test unit_TrichotomyTest_testSmallerEqual6 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual6(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testSmallerEqual6 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual6(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testSmallerEqual6 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual6(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testSmallerEqual7*)
definition unit_TrichotomyTest_testSmallerEqual7 :: Program where
  "unit_TrichotomyTest_testSmallerEqual7 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual7(II)Z'' \<mapsto> irgraph [
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
  (24, (IntegerLessThanNode 19 9), VoidStamp),
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
value "program_test unit_TrichotomyTest_testSmallerEqual7 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual7(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testSmallerEqual7 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual7(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testSmallerEqual7 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual7(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testSmallerEqual8*)
definition unit_TrichotomyTest_testSmallerEqual8 :: Program where
  "unit_TrichotomyTest_testSmallerEqual8 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual8(II)Z'' \<mapsto> irgraph [
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
  (24, (IntegerLessThanNode 19 9), VoidStamp),
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
value "program_test unit_TrichotomyTest_testSmallerEqual8 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual8(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testSmallerEqual8 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual8(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testSmallerEqual8 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual8(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testSmallerEqual9*)
definition unit_TrichotomyTest_testSmallerEqual9 :: Program where
  "unit_TrichotomyTest_testSmallerEqual9 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual9(II)Z'' \<mapsto> irgraph [
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
  (24, (IntegerLessThanNode 19 20), VoidStamp),
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
value "program_test unit_TrichotomyTest_testSmallerEqual9 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual9(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testSmallerEqual9 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual9(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "program_test unit_TrichotomyTest_testSmallerEqual9 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testSmallerEqual9(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedMathTest;.UnsignedMathTest_aboveOrEqualInt*)
definition unit_UnsignedMathTest_aboveOrEqualInt :: IRGraph where
  "unit_UnsignedMathTest_aboveOrEqualInt = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (IntegerBelowNode 1 2), VoidStamp),
  (7, (ConditionalNode 6 4 5), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_UnsignedMathTest_aboveOrEqualInt  [(new_int 32 (5)), (new_int 32 (7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_aboveOrEqualInt  [(new_int 32 (-3)), (new_int 32 (-7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_aboveOrEqualInt  [(new_int 32 (-3)), (new_int 32 (7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_aboveOrEqualInt  [(new_int 32 (42)), (new_int 32 (-5))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedMathTest;.UnsignedMathTest_aboveOrEqualLong*)
definition unit_UnsignedMathTest_aboveOrEqualLong :: IRGraph where
  "unit_UnsignedMathTest_aboveOrEqualLong = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (IntegerBelowNode 1 2), VoidStamp),
  (7, (ConditionalNode 6 4 5), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_UnsignedMathTest_aboveOrEqualLong  [(IntVal 64 (5)), (IntVal 64 (7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_aboveOrEqualLong  [(IntVal 64 (-3)), (IntVal 64 (-7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_aboveOrEqualLong  [(IntVal 64 (-3)), (IntVal 64 (7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_aboveOrEqualLong  [(IntVal 64 (42)), (IntVal 64 (-5))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedMathTest;.UnsignedMathTest_aboveThanInt*)
definition unit_UnsignedMathTest_aboveThanInt :: IRGraph where
  "unit_UnsignedMathTest_aboveThanInt = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (IntegerBelowNode 2 1), VoidStamp),
  (7, (ConditionalNode 6 4 5), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_UnsignedMathTest_aboveThanInt  [(new_int 32 (5)), (new_int 32 (7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_aboveThanInt  [(new_int 32 (-3)), (new_int 32 (-7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_aboveThanInt  [(new_int 32 (-3)), (new_int 32 (7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_aboveThanInt  [(new_int 32 (42)), (new_int 32 (-5))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedMathTest;.UnsignedMathTest_aboveThanLong*)
definition unit_UnsignedMathTest_aboveThanLong :: IRGraph where
  "unit_UnsignedMathTest_aboveThanLong = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (IntegerBelowNode 2 1), VoidStamp),
  (7, (ConditionalNode 6 4 5), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_UnsignedMathTest_aboveThanLong  [(IntVal 64 (5)), (IntVal 64 (7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_aboveThanLong  [(IntVal 64 (-3)), (IntVal 64 (-7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_aboveThanLong  [(IntVal 64 (-3)), (IntVal 64 (7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_aboveThanLong  [(IntVal 64 (42)), (IntVal 64 (-5))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedMathTest;.UnsignedMathTest_belowOrEqualInt*)
definition unit_UnsignedMathTest_belowOrEqualInt :: IRGraph where
  "unit_UnsignedMathTest_belowOrEqualInt = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (IntegerBelowNode 2 1), VoidStamp),
  (7, (ConditionalNode 6 4 5), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_UnsignedMathTest_belowOrEqualInt  [(new_int 32 (5)), (new_int 32 (7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_belowOrEqualInt  [(new_int 32 (-3)), (new_int 32 (-7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_belowOrEqualInt  [(new_int 32 (-3)), (new_int 32 (7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_belowOrEqualInt  [(new_int 32 (42)), (new_int 32 (-5))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedMathTest;.UnsignedMathTest_belowOrEqualLong*)
definition unit_UnsignedMathTest_belowOrEqualLong :: IRGraph where
  "unit_UnsignedMathTest_belowOrEqualLong = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (IntegerBelowNode 2 1), VoidStamp),
  (7, (ConditionalNode 6 4 5), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_UnsignedMathTest_belowOrEqualLong  [(IntVal 64 (5)), (IntVal 64 (7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_belowOrEqualLong  [(IntVal 64 (-3)), (IntVal 64 (-7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_belowOrEqualLong  [(IntVal 64 (-3)), (IntVal 64 (7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_belowOrEqualLong  [(IntVal 64 (42)), (IntVal 64 (-5))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedMathTest;.UnsignedMathTest_belowThanInt*)
definition unit_UnsignedMathTest_belowThanInt :: IRGraph where
  "unit_UnsignedMathTest_belowThanInt = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (IntegerBelowNode 1 2), VoidStamp),
  (7, (ConditionalNode 6 4 5), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_UnsignedMathTest_belowThanInt  [(new_int 32 (5)), (new_int 32 (7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_belowThanInt  [(new_int 32 (-3)), (new_int 32 (-7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_belowThanInt  [(new_int 32 (-3)), (new_int 32 (7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_belowThanInt  [(new_int 32 (42)), (new_int 32 (-5))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedMathTest;.UnsignedMathTest_belowThanLong*)
definition unit_UnsignedMathTest_belowThanLong :: IRGraph where
  "unit_UnsignedMathTest_belowThanLong = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (IntegerBelowNode 1 2), VoidStamp),
  (7, (ConditionalNode 6 4 5), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_UnsignedMathTest_belowThanLong  [(IntVal 64 (5)), (IntVal 64 (7))] (new_int 32 (1))"

value "static_test unit_UnsignedMathTest_belowThanLong  [(IntVal 64 (-3)), (IntVal 64 (-7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_belowThanLong  [(IntVal 64 (-3)), (IntVal 64 (7))] (new_int 32 (0))"

value "static_test unit_UnsignedMathTest_belowThanLong  [(IntVal 64 (42)), (IntVal 64 (-5))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/VN_Convert01;.VN_Convert01_test*)
definition unit_VN_Convert01_test :: IRGraph where
  "unit_VN_Convert01_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 19), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (9, (AddNode 1 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (NarrowNode 32 8 9), IntegerStamp 8 (-128) (127)),
  (12, (SignExtendNode 8 32 11), IntegerStamp 32 (-128) (127)),
  (13, (AddNode 12 12), IntegerStamp 32 (-256) (254)),
  (14, (ReturnNode (Some 13) None), VoidStamp),
  (15, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (16, (IntegerEqualsNode 1 15), VoidStamp),
  (17, (BeginNode 29), VoidStamp),
  (18, (BeginNode 24), VoidStamp),
  (19, (IfNode 16 18 17), VoidStamp),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (NarrowNode 32 16 9), IntegerStamp 16 (-32768) (32767)),
  (22, (SignExtendNode 16 32 21), IntegerStamp 32 (-32768) (32767)),
  (23, (AddNode 22 22), IntegerStamp 32 (-65536) (65534)),
  (24, (ReturnNode (Some 23) None), VoidStamp),
  (25, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (26, (IntegerEqualsNode 1 25), VoidStamp),
  (27, (BeginNode 34), VoidStamp),
  (28, (BeginNode 33), VoidStamp),
  (29, (IfNode 26 28 27), VoidStamp),
  (30, (FrameState [] None None None), IllegalStamp),
  (31, (ZeroExtendNode 16 32 21), IntegerStamp 32 (0) (65535)),
  (32, (AddNode 31 31), IntegerStamp 32 (0) (131070)),
  (33, (ReturnNode (Some 32) None), VoidStamp),
  (34, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_VN_Convert01_test  [(new_int 32 (0))] (new_int 32 (20))"

value "static_test unit_VN_Convert01_test  [(new_int 32 (1))] (new_int 32 (22))"

value "static_test unit_VN_Convert01_test  [(new_int 32 (2))] (new_int 32 (24))"


(* Lorg/graalvm/compiler/jtt/optimize/VN_Convert02;.VN_Convert02_test*)
definition unit_VN_Convert02_test :: Program where
  "unit_VN_Convert02_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.VN_Convert02.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 18), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (9, (AddNode 1 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Convert02.i2b(I)I'' [9]), VoidStamp),
  (11, (InvokeNode 11 10 None None (Some 12) 13), IntegerStamp 32 (-2147483648) (2147483647)),
  (12, (FrameState [] None None None), IllegalStamp),
  (13, (ReturnNode (Some 11) None), VoidStamp),
  (14, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (IntegerEqualsNode 1 14), VoidStamp),
  (16, (BeginNode 27), VoidStamp),
  (17, (BeginNode 20), VoidStamp),
  (18, (IfNode 15 17 16), VoidStamp),
  (19, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Convert02.i2s(I)I'' [9]), VoidStamp),
  (20, (InvokeNode 20 19 None None (Some 21) 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 20) None), VoidStamp),
  (23, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (24, (IntegerEqualsNode 1 23), VoidStamp),
  (25, (BeginNode 32), VoidStamp),
  (26, (BeginNode 29), VoidStamp),
  (27, (IfNode 24 26 25), VoidStamp),
  (28, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Convert02.i2c(I)I'' [9]), VoidStamp),
  (29, (InvokeNode 29 28 None None (Some 30) 31), IntegerStamp 32 (-2147483648) (2147483647)),
  (30, (FrameState [] None None None), IllegalStamp),
  (31, (ReturnNode (Some 29) None), VoidStamp),
  (32, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Convert02.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ConstantNode (new_int 1 (1))), IntegerStamp 1 (-1) (-1)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.optimize.VN_Convert02::cond'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Convert02.i2b(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (4, (SignExtendNode 8 32 3), IntegerStamp 32 (-128) (127)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Convert02::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 12), VoidStamp),
  (9, (BeginNode 13), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (AddNode 4 4), IntegerStamp 32 (-256) (254)),
  (12, (ReturnNode (Some 11) None), VoidStamp),
  (13, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Convert02.i2s(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (SignExtendNode 16 32 3), IntegerStamp 32 (-32768) (32767)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Convert02::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 12), VoidStamp),
  (9, (BeginNode 13), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (AddNode 4 4), IntegerStamp 32 (-65536) (65534)),
  (12, (ReturnNode (Some 11) None), VoidStamp),
  (13, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Convert02.i2c(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Convert02::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 12), VoidStamp),
  (9, (BeginNode 13), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (AddNode 4 4), IntegerStamp 32 (0) (131070)),
  (12, (ReturnNode (Some 11) None), VoidStamp),
  (13, (ReturnNode (Some 6) None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Convert02.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_VN_Convert02_test ''org.graalvm.compiler.jtt.optimize.VN_Convert02.test(I)I'' [(new_int 32 (0))] (new_int 32 (20))"

value "program_test unit_VN_Convert02_test ''org.graalvm.compiler.jtt.optimize.VN_Convert02.test(I)I'' [(new_int 32 (1))] (new_int 32 (22))"

value "program_test unit_VN_Convert02_test ''org.graalvm.compiler.jtt.optimize.VN_Convert02.test(I)I'' [(new_int 32 (2))] (new_int 32 (24))"


(* Lorg/graalvm/compiler/jtt/optimize/VN_Int01;.VN_Int01_test*)
definition unit_VN_Int01_test :: Program where
  "unit_VN_Int01_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.VN_Int01.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int01.add(I)I'' [1]), VoidStamp),
  (9, (InvokeNode 9 8 None None (Some 10) 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ReturnNode (Some 9) None), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (IntegerEqualsNode 1 12), VoidStamp),
  (14, (BeginNode 25), VoidStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 13 15 14), VoidStamp),
  (17, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int01.sub(I)I'' [1]), VoidStamp),
  (18, (InvokeNode 18 17 None None (Some 19) 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (ReturnNode (Some 18) None), VoidStamp),
  (21, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (22, (IntegerEqualsNode 1 21), VoidStamp),
  (23, (BeginNode 34), VoidStamp),
  (24, (BeginNode 27), VoidStamp),
  (25, (IfNode 22 24 23), VoidStamp),
  (26, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int01.mul(I)I'' [1]), VoidStamp),
  (27, (InvokeNode 27 26 None None (Some 28) 29), IntegerStamp 32 (-2147483648) (2147483647)),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode (Some 27) None), VoidStamp),
  (30, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (31, (IntegerEqualsNode 1 30), VoidStamp),
  (32, (BeginNode 43), VoidStamp),
  (33, (BeginNode 36), VoidStamp),
  (34, (IfNode 31 33 32), VoidStamp),
  (35, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int01.div(I)I'' [1]), VoidStamp),
  (36, (InvokeNode 36 35 None None (Some 37) 38), IntegerStamp 32 (-2147483648) (2147483647)),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (ReturnNode (Some 36) None), VoidStamp),
  (39, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (40, (IntegerEqualsNode 1 39), VoidStamp),
  (41, (BeginNode 52), VoidStamp),
  (42, (BeginNode 45), VoidStamp),
  (43, (IfNode 40 42 41), VoidStamp),
  (44, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int01.mod(I)I'' [1]), VoidStamp),
  (45, (InvokeNode 45 44 None None (Some 46) 47), IntegerStamp 32 (-2147483648) (2147483647)),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (ReturnNode (Some 45) None), VoidStamp),
  (48, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (49, (IntegerEqualsNode 1 48), VoidStamp),
  (50, (BeginNode 61), VoidStamp),
  (51, (BeginNode 54), VoidStamp),
  (52, (IfNode 49 51 50), VoidStamp),
  (53, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int01.and(I)I'' [1]), VoidStamp),
  (54, (InvokeNode 54 53 None None (Some 55) 56), IntegerStamp 32 (-2147483648) (2147483647)),
  (55, (FrameState [] None None None), IllegalStamp),
  (56, (ReturnNode (Some 54) None), VoidStamp),
  (57, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (58, (IntegerEqualsNode 1 57), VoidStamp),
  (59, (BeginNode 70), VoidStamp),
  (60, (BeginNode 63), VoidStamp),
  (61, (IfNode 58 60 59), VoidStamp),
  (62, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int01.or(I)I'' [1]), VoidStamp),
  (63, (InvokeNode 63 62 None None (Some 64) 65), IntegerStamp 32 (-2147483648) (2147483647)),
  (64, (FrameState [] None None None), IllegalStamp),
  (65, (ReturnNode (Some 63) None), VoidStamp),
  (66, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (67, (IntegerEqualsNode 1 66), VoidStamp),
  (68, (BeginNode 75), VoidStamp),
  (69, (BeginNode 72), VoidStamp),
  (70, (IfNode 67 69 68), VoidStamp),
  (71, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int01.xor(I)I'' [1]), VoidStamp),
  (72, (InvokeNode 72 71 None None (Some 73) 74), IntegerStamp 32 (-2147483648) (2147483647)),
  (73, (FrameState [] None None None), IllegalStamp),
  (74, (ReturnNode (Some 72) None), VoidStamp),
  (75, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int01.add(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (AddNode 4 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int01.sub(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (4, (ConstantNode (new_int 32 (-3))), IntegerStamp 32 (-3) (-3)),
  (5, (AddNode 1 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int01.mul(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (4, (MulNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (MulNode 4 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int01.div(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (9))), IntegerStamp 32 (9) (9)),
  (4, (SignedDivNode 4 3 1 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (SignedDivNode 5 3 1 None None 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (SignedDivNode 6 4 5 None None 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int01.mod(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (4, (SignedRemNode 4 3 1 None None 5), IntegerStamp 32 (0) (7)),
  (5, (SignedRemNode 5 3 1 None None 6), IntegerStamp 32 (0) (7)),
  (6, (SignedRemNode 6 4 5 None None 7), IntegerStamp 32 (0) (6)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int01.and(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (4, (AndNode 1 3), IntegerStamp 32 (0) (7)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int01.or(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (4, (OrNode 1 3), IntegerStamp 32 (-2147483641) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int01.xor(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (4, (XorNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]
  )"
value "program_test unit_VN_Int01_test ''org.graalvm.compiler.jtt.optimize.VN_Int01.test(I)I'' [(new_int 32 (0))] (new_int 32 (6))"

value "program_test unit_VN_Int01_test ''org.graalvm.compiler.jtt.optimize.VN_Int01.test(I)I'' [(new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_VN_Int01_test ''org.graalvm.compiler.jtt.optimize.VN_Int01.test(I)I'' [(new_int 32 (2))] (new_int 32 (36))"

value "program_test unit_VN_Int01_test ''org.graalvm.compiler.jtt.optimize.VN_Int01.test(I)I'' [(new_int 32 (3))] (new_int 32 (1))"

value "program_test unit_VN_Int01_test ''org.graalvm.compiler.jtt.optimize.VN_Int01.test(I)I'' [(new_int 32 (4))] (new_int 32 (0))"

value "program_test unit_VN_Int01_test ''org.graalvm.compiler.jtt.optimize.VN_Int01.test(I)I'' [(new_int 32 (5))] (new_int 32 (5))"

value "program_test unit_VN_Int01_test ''org.graalvm.compiler.jtt.optimize.VN_Int01.test(I)I'' [(new_int 32 (6))] (new_int 32 (7))"

value "program_test unit_VN_Int01_test ''org.graalvm.compiler.jtt.optimize.VN_Int01.test(I)I'' [(new_int 32 (7))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/VN_Int02;.VN_Int02_test*)
definition unit_VN_Int02_test :: Program where
  "unit_VN_Int02_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.VN_Int02.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 18), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (9, (AddNode 1 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int02.shift0(I)I'' [9]), VoidStamp),
  (11, (InvokeNode 11 10 None None (Some 12) 13), IntegerStamp 32 (-2147483648) (2147483647)),
  (12, (FrameState [] None None None), IllegalStamp),
  (13, (ReturnNode (Some 11) None), VoidStamp),
  (14, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (IntegerEqualsNode 1 14), VoidStamp),
  (16, (BeginNode 27), VoidStamp),
  (17, (BeginNode 20), VoidStamp),
  (18, (IfNode 15 17 16), VoidStamp),
  (19, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int02.shift1(I)I'' [9]), VoidStamp),
  (20, (InvokeNode 20 19 None None (Some 21) 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 20) None), VoidStamp),
  (23, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (24, (IntegerEqualsNode 1 23), VoidStamp),
  (25, (BeginNode 32), VoidStamp),
  (26, (BeginNode 29), VoidStamp),
  (27, (IfNode 24 26 25), VoidStamp),
  (28, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int02.shift2(I)I'' [9]), VoidStamp),
  (29, (InvokeNode 29 28 None None (Some 30) 31), IntegerStamp 32 (-2147483648) (2147483647)),
  (30, (FrameState [] None None None), IllegalStamp),
  (31, (ReturnNode (Some 29) None), VoidStamp),
  (32, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int02.shift0(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (RightShiftNode 1 3), IntegerStamp 32 (-1073741824) (1073741823)),
  (5, (AddNode 4 4), IntegerStamp 32 (-2147483648) (2147483646)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int02.shift1(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (UnsignedRightShiftNode 1 3), IntegerStamp 32 (0) (2147483647)),
  (5, (AddNode 4 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int02.shift2(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (LeftShiftNode 1 3), IntegerStamp 32 (-2147483648) (2147483646)),
  (5, (AddNode 4 4), IntegerStamp 32 (-2147483648) (2147483646)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]
  )"
value "program_test unit_VN_Int02_test ''org.graalvm.compiler.jtt.optimize.VN_Int02.test(I)I'' [(new_int 32 (0))] (new_int 32 (10))"

value "program_test unit_VN_Int02_test ''org.graalvm.compiler.jtt.optimize.VN_Int02.test(I)I'' [(new_int 32 (1))] (new_int 32 (10))"

value "program_test unit_VN_Int02_test ''org.graalvm.compiler.jtt.optimize.VN_Int02.test(I)I'' [(new_int 32 (2))] (new_int 32 (48))"


(* Lorg/graalvm/compiler/jtt/optimize/VN_Int03;.VN_Int03_test*)
definition unit_VN_Int03_test :: Program where
  "unit_VN_Int03_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.VN_Int03.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int03.add(I)I'' [1]), VoidStamp),
  (9, (InvokeNode 9 8 None None (Some 10) 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ReturnNode (Some 9) None), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (IntegerEqualsNode 1 12), VoidStamp),
  (14, (BeginNode 25), VoidStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 13 15 14), VoidStamp),
  (17, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int03.sub(I)I'' [1]), VoidStamp),
  (18, (InvokeNode 18 17 None None (Some 19) 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (ReturnNode (Some 18) None), VoidStamp),
  (21, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (22, (IntegerEqualsNode 1 21), VoidStamp),
  (23, (BeginNode 34), VoidStamp),
  (24, (BeginNode 27), VoidStamp),
  (25, (IfNode 22 24 23), VoidStamp),
  (26, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int03.mul(I)I'' [1]), VoidStamp),
  (27, (InvokeNode 27 26 None None (Some 28) 29), IntegerStamp 32 (-2147483648) (2147483647)),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode (Some 27) None), VoidStamp),
  (30, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (31, (IntegerEqualsNode 1 30), VoidStamp),
  (32, (BeginNode 43), VoidStamp),
  (33, (BeginNode 36), VoidStamp),
  (34, (IfNode 31 33 32), VoidStamp),
  (35, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int03.div(I)I'' [1]), VoidStamp),
  (36, (InvokeNode 36 35 None None (Some 37) 38), IntegerStamp 32 (-2147483648) (2147483647)),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (ReturnNode (Some 36) None), VoidStamp),
  (39, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (40, (IntegerEqualsNode 1 39), VoidStamp),
  (41, (BeginNode 52), VoidStamp),
  (42, (BeginNode 45), VoidStamp),
  (43, (IfNode 40 42 41), VoidStamp),
  (44, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int03.mod(I)I'' [1]), VoidStamp),
  (45, (InvokeNode 45 44 None None (Some 46) 47), IntegerStamp 32 (-2147483648) (2147483647)),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (ReturnNode (Some 45) None), VoidStamp),
  (48, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (49, (IntegerEqualsNode 1 48), VoidStamp),
  (50, (BeginNode 61), VoidStamp),
  (51, (BeginNode 54), VoidStamp),
  (52, (IfNode 49 51 50), VoidStamp),
  (53, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int03.and(I)I'' [1]), VoidStamp),
  (54, (InvokeNode 54 53 None None (Some 55) 56), IntegerStamp 32 (-2147483648) (2147483647)),
  (55, (FrameState [] None None None), IllegalStamp),
  (56, (ReturnNode (Some 54) None), VoidStamp),
  (57, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (58, (IntegerEqualsNode 1 57), VoidStamp),
  (59, (BeginNode 70), VoidStamp),
  (60, (BeginNode 63), VoidStamp),
  (61, (IfNode 58 60 59), VoidStamp),
  (62, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int03.or(I)I'' [1]), VoidStamp),
  (63, (InvokeNode 63 62 None None (Some 64) 65), IntegerStamp 32 (-2147483648) (2147483647)),
  (64, (FrameState [] None None None), IllegalStamp),
  (65, (ReturnNode (Some 63) None), VoidStamp),
  (66, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (67, (IntegerEqualsNode 1 66), VoidStamp),
  (68, (BeginNode 75), VoidStamp),
  (69, (BeginNode 72), VoidStamp),
  (70, (IfNode 67 69 68), VoidStamp),
  (71, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int03.xor(I)I'' [1]), VoidStamp),
  (72, (InvokeNode 72 71 None None (Some 73) 74), IntegerStamp 32 (-2147483648) (2147483647)),
  (73, (FrameState [] None None None), IllegalStamp),
  (74, (ReturnNode (Some 72) None), VoidStamp),
  (75, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int03.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ConstantNode (new_int 1 (1))), IntegerStamp 1 (-1) (-1)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.optimize.VN_Int03::cond'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int03.add(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Int03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 12), VoidStamp),
  (9, (BeginNode 13), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (AddNode 4 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (12, (ReturnNode (Some 11) None), VoidStamp),
  (13, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int03.sub(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (4, (ConstantNode (new_int 32 (-3))), IntegerStamp 32 (-3) (-3)),
  (5, (AddNode 1 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (LoadFieldNode 6 ''org.graalvm.compiler.jtt.optimize.VN_Int03::cond'' None 11), IntegerStamp 32 (0) (1)),
  (7, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (8, (IntegerEqualsNode 6 7), VoidStamp),
  (9, (BeginNode 12), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ReturnNode (Some 7) None), VoidStamp),
  (13, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int03.mul(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (4, (MulNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Int03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 12), VoidStamp),
  (9, (BeginNode 13), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (MulNode 4 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (12, (ReturnNode (Some 11) None), VoidStamp),
  (13, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int03.div(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (9))), IntegerStamp 32 (9) (9)),
  (4, (SignedDivNode 4 3 1 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Int03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 14), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (SignedDivNode 11 3 1 None None 12), IntegerStamp 32 (-2147483648) (2147483647)),
  (12, (SignedDivNode 12 4 11 None None 13), IntegerStamp 32 (-2147483648) (2147483647)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int03.mod(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (4, (SignedRemNode 4 3 1 None None 5), IntegerStamp 32 (0) (7)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Int03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 14), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (SignedRemNode 11 3 1 None None 12), IntegerStamp 32 (0) (7)),
  (12, (SignedRemNode 12 4 11 None None 13), IntegerStamp 32 (0) (6)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int03.and(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (4, (AndNode 1 3), IntegerStamp 32 (0) (7)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Int03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 12), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (ReturnNode (Some 4) None), VoidStamp),
  (12, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int03.or(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (4, (OrNode 1 3), IntegerStamp 32 (-2147483641) (2147483647)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Int03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 12), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (ReturnNode (Some 4) None), VoidStamp),
  (12, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Int03.xor(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (4, (XorNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Int03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 12), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (ReturnNode (Some 6) None), VoidStamp),
  (12, (ReturnNode (Some 3) None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Int03.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_VN_Int03_test ''org.graalvm.compiler.jtt.optimize.VN_Int03.test(I)I'' [(new_int 32 (0))] (new_int 32 (6))"

value "program_test unit_VN_Int03_test ''org.graalvm.compiler.jtt.optimize.VN_Int03.test(I)I'' [(new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_VN_Int03_test ''org.graalvm.compiler.jtt.optimize.VN_Int03.test(I)I'' [(new_int 32 (2))] (new_int 32 (36))"

value "program_test unit_VN_Int03_test ''org.graalvm.compiler.jtt.optimize.VN_Int03.test(I)I'' [(new_int 32 (3))] (new_int 32 (1))"

value "program_test unit_VN_Int03_test ''org.graalvm.compiler.jtt.optimize.VN_Int03.test(I)I'' [(new_int 32 (4))] (new_int 32 (0))"

value "program_test unit_VN_Int03_test ''org.graalvm.compiler.jtt.optimize.VN_Int03.test(I)I'' [(new_int 32 (5))] (new_int 32 (5))"

value "program_test unit_VN_Int03_test ''org.graalvm.compiler.jtt.optimize.VN_Int03.test(I)I'' [(new_int 32 (6))] (new_int 32 (7))"

value "program_test unit_VN_Int03_test ''org.graalvm.compiler.jtt.optimize.VN_Int03.test(I)I'' [(new_int 32 (7))] (new_int 32 (0))"

end
