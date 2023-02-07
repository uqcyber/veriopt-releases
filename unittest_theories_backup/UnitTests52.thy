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


(* Lorg/graalvm/compiler/jtt/optimize/VN_Long01;.VN_Long01_test*)
definition unit_VN_Long01_test :: Program where
  "unit_VN_Long01_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.VN_Long01.test(I)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 17), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (SignExtendNode 32 64 1), IntegerStamp 64 (-2147483648) (2147483647)),
  (9, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long01.add(J)J'' [8]), VoidStamp),
  (10, (InvokeNode 10 9 None None (Some 11) 12), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (ReturnNode (Some 10) None), VoidStamp),
  (13, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (14, (IntegerEqualsNode 1 13), VoidStamp),
  (15, (BeginNode 26), VoidStamp),
  (16, (BeginNode 19), VoidStamp),
  (17, (IfNode 14 16 15), VoidStamp),
  (18, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long01.sub(J)J'' [8]), VoidStamp),
  (19, (InvokeNode 19 18 None None (Some 20) 21), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (ReturnNode (Some 19) None), VoidStamp),
  (22, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (23, (IntegerEqualsNode 1 22), VoidStamp),
  (24, (BeginNode 35), VoidStamp),
  (25, (BeginNode 28), VoidStamp),
  (26, (IfNode 23 25 24), VoidStamp),
  (27, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long01.mul(J)J'' [8]), VoidStamp),
  (28, (InvokeNode 28 27 None None (Some 29) 30), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (29, (FrameState [] None None None), IllegalStamp),
  (30, (ReturnNode (Some 28) None), VoidStamp),
  (31, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (32, (IntegerEqualsNode 1 31), VoidStamp),
  (33, (BeginNode 44), VoidStamp),
  (34, (BeginNode 37), VoidStamp),
  (35, (IfNode 32 34 33), VoidStamp),
  (36, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long01.div(J)J'' [8]), VoidStamp),
  (37, (InvokeNode 37 36 None None (Some 38) 39), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (38, (FrameState [] None None None), IllegalStamp),
  (39, (ReturnNode (Some 37) None), VoidStamp),
  (40, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (41, (IntegerEqualsNode 1 40), VoidStamp),
  (42, (BeginNode 53), VoidStamp),
  (43, (BeginNode 46), VoidStamp),
  (44, (IfNode 41 43 42), VoidStamp),
  (45, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long01.mod(J)J'' [8]), VoidStamp),
  (46, (InvokeNode 46 45 None None (Some 47) 48), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (47, (FrameState [] None None None), IllegalStamp),
  (48, (ReturnNode (Some 46) None), VoidStamp),
  (49, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (50, (IntegerEqualsNode 1 49), VoidStamp),
  (51, (BeginNode 62), VoidStamp),
  (52, (BeginNode 55), VoidStamp),
  (53, (IfNode 50 52 51), VoidStamp),
  (54, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long01.and(J)J'' [8]), VoidStamp),
  (55, (InvokeNode 55 54 None None (Some 56) 57), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (56, (FrameState [] None None None), IllegalStamp),
  (57, (ReturnNode (Some 55) None), VoidStamp),
  (58, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (59, (IntegerEqualsNode 1 58), VoidStamp),
  (60, (BeginNode 71), VoidStamp),
  (61, (BeginNode 64), VoidStamp),
  (62, (IfNode 59 61 60), VoidStamp),
  (63, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long01.or(J)J'' [8]), VoidStamp),
  (64, (InvokeNode 64 63 None None (Some 65) 66), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (65, (FrameState [] None None None), IllegalStamp),
  (66, (ReturnNode (Some 64) None), VoidStamp),
  (67, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (68, (IntegerEqualsNode 1 67), VoidStamp),
  (69, (BeginNode 77), VoidStamp),
  (70, (BeginNode 73), VoidStamp),
  (71, (IfNode 68 70 69), VoidStamp),
  (72, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long01.xor(J)J'' [8]), VoidStamp),
  (73, (InvokeNode 73 72 None None (Some 74) 75), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (74, (FrameState [] None None None), IllegalStamp),
  (75, (ReturnNode (Some 73) None), VoidStamp),
  (76, (ConstantNode (IntVal 64 (0))), IntegerStamp 64 (0) (0)),
  (77, (ReturnNode (Some 76) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long01.add(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (3))), IntegerStamp 64 (3) (3)),
  (4, (AddNode 1 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (AddNode 4 4), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long01.sub(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (3))), IntegerStamp 64 (3) (3)),
  (4, (ConstantNode (IntVal 64 (-3))), IntegerStamp 64 (-3) (-3)),
  (5, (AddNode 1 4), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (6, (ConstantNode (IntVal 64 (0))), IntegerStamp 64 (0) (0)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long01.mul(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (3))), IntegerStamp 64 (3) (3)),
  (4, (MulNode 1 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (MulNode 4 4), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long01.div(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (9))), IntegerStamp 64 (9) (9)),
  (4, (SignedDivNode 4 3 1 None None 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (SignedDivNode 5 3 1 None None 6), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (6, (SignedDivNode 6 4 5 None None 7), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long01.mod(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (7))), IntegerStamp 64 (7) (7)),
  (4, (SignedRemNode 4 3 1 None None 5), IntegerStamp 64 (0) (7)),
  (5, (SignedRemNode 5 3 1 None None 6), IntegerStamp 64 (0) (7)),
  (6, (SignedRemNode 6 4 5 None None 7), IntegerStamp 64 (0) (6)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long01.and(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (7))), IntegerStamp 64 (7) (7)),
  (4, (AndNode 1 3), IntegerStamp 64 (0) (7)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long01.or(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (7))), IntegerStamp 64 (7) (7)),
  (4, (OrNode 1 3), IntegerStamp 64 (-9223372036854775801) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long01.xor(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (7))), IntegerStamp 64 (7) (7)),
  (4, (XorNode 1 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ConstantNode (IntVal 64 (0))), IntegerStamp 64 (0) (0)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]
  )"
value "program_test unit_VN_Long01_test ''org.graalvm.compiler.jtt.optimize.VN_Long01.test(I)J'' [(new_int 32 (0))] (IntVal 64 (6))"

value "program_test unit_VN_Long01_test ''org.graalvm.compiler.jtt.optimize.VN_Long01.test(I)J'' [(new_int 32 (1))] (IntVal 64 (0))"

value "program_test unit_VN_Long01_test ''org.graalvm.compiler.jtt.optimize.VN_Long01.test(I)J'' [(new_int 32 (2))] (IntVal 64 (36))"

value "program_test unit_VN_Long01_test ''org.graalvm.compiler.jtt.optimize.VN_Long01.test(I)J'' [(new_int 32 (3))] (IntVal 64 (1))"

value "program_test unit_VN_Long01_test ''org.graalvm.compiler.jtt.optimize.VN_Long01.test(I)J'' [(new_int 32 (4))] (IntVal 64 (0))"

value "program_test unit_VN_Long01_test ''org.graalvm.compiler.jtt.optimize.VN_Long01.test(I)J'' [(new_int 32 (5))] (IntVal 64 (5))"

value "program_test unit_VN_Long01_test ''org.graalvm.compiler.jtt.optimize.VN_Long01.test(I)J'' [(new_int 32 (6))] (IntVal 64 (7))"

value "program_test unit_VN_Long01_test ''org.graalvm.compiler.jtt.optimize.VN_Long01.test(I)J'' [(new_int 32 (7))] (IntVal 64 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/VN_Long02;.VN_Long02_test*)
definition unit_VN_Long02_test :: Program where
  "unit_VN_Long02_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.VN_Long02.test(I)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 19), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (9, (AddNode 1 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (SignExtendNode 32 64 9), IntegerStamp 64 (-2147483648) (2147483647)),
  (11, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long02.shift0(J)J'' [10]), VoidStamp),
  (12, (InvokeNode 12 11 None None (Some 13) 14), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (13, (FrameState [] None None None), IllegalStamp),
  (14, (ReturnNode (Some 12) None), VoidStamp),
  (15, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (16, (IntegerEqualsNode 1 15), VoidStamp),
  (17, (BeginNode 28), VoidStamp),
  (18, (BeginNode 21), VoidStamp),
  (19, (IfNode 16 18 17), VoidStamp),
  (20, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long02.shift1(J)J'' [10]), VoidStamp),
  (21, (InvokeNode 21 20 None None (Some 22) 23), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (ReturnNode (Some 21) None), VoidStamp),
  (24, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (25, (IntegerEqualsNode 1 24), VoidStamp),
  (26, (BeginNode 34), VoidStamp),
  (27, (BeginNode 30), VoidStamp),
  (28, (IfNode 25 27 26), VoidStamp),
  (29, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long02.shift2(J)J'' [10]), VoidStamp),
  (30, (InvokeNode 30 29 None None (Some 31) 32), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (31, (FrameState [] None None None), IllegalStamp),
  (32, (ReturnNode (Some 30) None), VoidStamp),
  (33, (ConstantNode (IntVal 64 (0))), IntegerStamp 64 (0) (0)),
  (34, (ReturnNode (Some 33) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long02.shift0(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (1))), IntegerStamp 64 (1) (1)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (RightShiftNode 1 4), IntegerStamp 64 (-4611686018427387904) (4611686018427387903)),
  (6, (AddNode 5 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775806)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long02.shift1(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (1))), IntegerStamp 64 (1) (1)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (UnsignedRightShiftNode 1 4), IntegerStamp 64 (0) (9223372036854775807)),
  (6, (AddNode 5 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long02.shift2(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (1))), IntegerStamp 64 (1) (1)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (LeftShiftNode 1 4), IntegerStamp 64 (-9223372036854775808) (9223372036854775806)),
  (6, (AddNode 5 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775806)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]
  )"
value "program_test unit_VN_Long02_test ''org.graalvm.compiler.jtt.optimize.VN_Long02.test(I)J'' [(new_int 32 (0))] (IntVal 64 (10))"

value "program_test unit_VN_Long02_test ''org.graalvm.compiler.jtt.optimize.VN_Long02.test(I)J'' [(new_int 32 (1))] (IntVal 64 (10))"

value "program_test unit_VN_Long02_test ''org.graalvm.compiler.jtt.optimize.VN_Long02.test(I)J'' [(new_int 32 (2))] (IntVal 64 (48))"


(* Lorg/graalvm/compiler/jtt/optimize/VN_Long03;.VN_Long03_test*)
definition unit_VN_Long03_test :: Program where
  "unit_VN_Long03_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.VN_Long03.test(I)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 17), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (SignExtendNode 32 64 1), IntegerStamp 64 (-2147483648) (2147483647)),
  (9, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long03.add(J)J'' [8]), VoidStamp),
  (10, (InvokeNode 10 9 None None (Some 11) 12), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (ReturnNode (Some 10) None), VoidStamp),
  (13, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (14, (IntegerEqualsNode 1 13), VoidStamp),
  (15, (BeginNode 26), VoidStamp),
  (16, (BeginNode 19), VoidStamp),
  (17, (IfNode 14 16 15), VoidStamp),
  (18, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long03.sub(J)J'' [8]), VoidStamp),
  (19, (InvokeNode 19 18 None None (Some 20) 21), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (ReturnNode (Some 19) None), VoidStamp),
  (22, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (23, (IntegerEqualsNode 1 22), VoidStamp),
  (24, (BeginNode 35), VoidStamp),
  (25, (BeginNode 28), VoidStamp),
  (26, (IfNode 23 25 24), VoidStamp),
  (27, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long03.mul(J)J'' [8]), VoidStamp),
  (28, (InvokeNode 28 27 None None (Some 29) 30), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (29, (FrameState [] None None None), IllegalStamp),
  (30, (ReturnNode (Some 28) None), VoidStamp),
  (31, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (32, (IntegerEqualsNode 1 31), VoidStamp),
  (33, (BeginNode 44), VoidStamp),
  (34, (BeginNode 37), VoidStamp),
  (35, (IfNode 32 34 33), VoidStamp),
  (36, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long03.div(J)J'' [8]), VoidStamp),
  (37, (InvokeNode 37 36 None None (Some 38) 39), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (38, (FrameState [] None None None), IllegalStamp),
  (39, (ReturnNode (Some 37) None), VoidStamp),
  (40, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (41, (IntegerEqualsNode 1 40), VoidStamp),
  (42, (BeginNode 53), VoidStamp),
  (43, (BeginNode 46), VoidStamp),
  (44, (IfNode 41 43 42), VoidStamp),
  (45, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long03.mod(J)J'' [8]), VoidStamp),
  (46, (InvokeNode 46 45 None None (Some 47) 48), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (47, (FrameState [] None None None), IllegalStamp),
  (48, (ReturnNode (Some 46) None), VoidStamp),
  (49, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (50, (IntegerEqualsNode 1 49), VoidStamp),
  (51, (BeginNode 62), VoidStamp),
  (52, (BeginNode 55), VoidStamp),
  (53, (IfNode 50 52 51), VoidStamp),
  (54, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long03.and(J)J'' [8]), VoidStamp),
  (55, (InvokeNode 55 54 None None (Some 56) 57), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (56, (FrameState [] None None None), IllegalStamp),
  (57, (ReturnNode (Some 55) None), VoidStamp),
  (58, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (59, (IntegerEqualsNode 1 58), VoidStamp),
  (60, (BeginNode 71), VoidStamp),
  (61, (BeginNode 64), VoidStamp),
  (62, (IfNode 59 61 60), VoidStamp),
  (63, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long03.or(J)J'' [8]), VoidStamp),
  (64, (InvokeNode 64 63 None None (Some 65) 66), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (65, (FrameState [] None None None), IllegalStamp),
  (66, (ReturnNode (Some 64) None), VoidStamp),
  (67, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (68, (IntegerEqualsNode 1 67), VoidStamp),
  (69, (BeginNode 77), VoidStamp),
  (70, (BeginNode 73), VoidStamp),
  (71, (IfNode 68 70 69), VoidStamp),
  (72, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long03.xor(J)J'' [8]), VoidStamp),
  (73, (InvokeNode 73 72 None None (Some 74) 75), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (74, (FrameState [] None None None), IllegalStamp),
  (75, (ReturnNode (Some 73) None), VoidStamp),
  (76, (ConstantNode (IntVal 64 (0))), IntegerStamp 64 (0) (0)),
  (77, (ReturnNode (Some 76) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long03.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ConstantNode (new_int 1 (1))), IntegerStamp 1 (-1) (-1)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.optimize.VN_Long03::cond'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long03.add(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (3))), IntegerStamp 64 (3) (3)),
  (4, (AddNode 1 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Long03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 12), VoidStamp),
  (9, (BeginNode 13), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (AddNode 4 4), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (12, (ReturnNode (Some 11) None), VoidStamp),
  (13, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long03.sub(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (3))), IntegerStamp 64 (3) (3)),
  (4, (ConstantNode (IntVal 64 (-3))), IntegerStamp 64 (-3) (-3)),
  (5, (AddNode 1 4), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (6, (LoadFieldNode 6 ''org.graalvm.compiler.jtt.optimize.VN_Long03::cond'' None 11), IntegerStamp 32 (0) (1)),
  (7, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (8, (IntegerEqualsNode 6 7), VoidStamp),
  (9, (BeginNode 13), VoidStamp),
  (10, (BeginNode 14), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (IntVal 64 (0))), IntegerStamp 64 (0) (0)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long03.mul(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (3))), IntegerStamp 64 (3) (3)),
  (4, (MulNode 1 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Long03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 12), VoidStamp),
  (9, (BeginNode 13), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (MulNode 4 4), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (12, (ReturnNode (Some 11) None), VoidStamp),
  (13, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long03.div(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (9))), IntegerStamp 64 (9) (9)),
  (4, (SignedDivNode 4 3 1 None None 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Long03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 14), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (SignedDivNode 11 3 1 None None 12), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (12, (SignedDivNode 12 4 11 None None 13), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long03.mod(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (7))), IntegerStamp 64 (7) (7)),
  (4, (SignedRemNode 4 3 1 None None 5), IntegerStamp 64 (0) (7)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Long03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 14), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (SignedRemNode 11 3 1 None None 12), IntegerStamp 64 (0) (7)),
  (12, (SignedRemNode 12 4 11 None None 13), IntegerStamp 64 (0) (6)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long03.and(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (7))), IntegerStamp 64 (7) (7)),
  (4, (AndNode 1 3), IntegerStamp 64 (0) (7)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Long03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 12), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (ReturnNode (Some 4) None), VoidStamp),
  (12, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long03.or(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (7))), IntegerStamp 64 (7) (7)),
  (4, (OrNode 1 3), IntegerStamp 64 (-9223372036854775801) (9223372036854775807)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Long03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 12), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (ReturnNode (Some 4) None), VoidStamp),
  (12, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Long03.xor(J)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (7))), IntegerStamp 64 (7) (7)),
  (4, (XorNode 1 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Long03::cond'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 12), VoidStamp),
  (9, (BeginNode 13), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (ConstantNode (IntVal 64 (0))), IntegerStamp 64 (0) (0)),
  (12, (ReturnNode (Some 11) None), VoidStamp),
  (13, (ReturnNode (Some 3) None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Long03.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_VN_Long03_test ''org.graalvm.compiler.jtt.optimize.VN_Long03.test(I)J'' [(new_int 32 (0))] (IntVal 64 (6))"

value "program_test unit_VN_Long03_test ''org.graalvm.compiler.jtt.optimize.VN_Long03.test(I)J'' [(new_int 32 (1))] (IntVal 64 (0))"

value "program_test unit_VN_Long03_test ''org.graalvm.compiler.jtt.optimize.VN_Long03.test(I)J'' [(new_int 32 (2))] (IntVal 64 (36))"

value "program_test unit_VN_Long03_test ''org.graalvm.compiler.jtt.optimize.VN_Long03.test(I)J'' [(new_int 32 (3))] (IntVal 64 (1))"

value "program_test unit_VN_Long03_test ''org.graalvm.compiler.jtt.optimize.VN_Long03.test(I)J'' [(new_int 32 (4))] (IntVal 64 (0))"

value "program_test unit_VN_Long03_test ''org.graalvm.compiler.jtt.optimize.VN_Long03.test(I)J'' [(new_int 32 (5))] (IntVal 64 (5))"

value "program_test unit_VN_Long03_test ''org.graalvm.compiler.jtt.optimize.VN_Long03.test(I)J'' [(new_int 32 (6))] (IntVal 64 (7))"

value "program_test unit_VN_Long03_test ''org.graalvm.compiler.jtt.optimize.VN_Long03.test(I)J'' [(new_int 32 (7))] (IntVal 64 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/VN_Loop01;.VN_Loop01_test*)
definition unit_VN_Loop01_test :: Program where
  "unit_VN_Loop01_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test1(I)I'' [1]), VoidStamp),
  (9, (InvokeNode 9 8 None None (Some 10) 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ReturnNode (Some 9) None), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (IntegerEqualsNode 1 12), VoidStamp),
  (14, (BeginNode 25), VoidStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 13 15 14), VoidStamp),
  (17, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test2(I)I'' [1]), VoidStamp),
  (18, (InvokeNode 18 17 None None (Some 19) 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (ReturnNode (Some 18) None), VoidStamp),
  (21, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (22, (IntegerEqualsNode 1 21), VoidStamp),
  (23, (BeginNode 34), VoidStamp),
  (24, (BeginNode 27), VoidStamp),
  (25, (IfNode 22 24 23), VoidStamp),
  (26, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test3(I)I'' [1]), VoidStamp),
  (27, (InvokeNode 27 26 None None (Some 28) 29), IntegerStamp 32 (-2147483648) (2147483647)),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode (Some 27) None), VoidStamp),
  (30, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (31, (IntegerEqualsNode 1 30), VoidStamp),
  (32, (BeginNode 39), VoidStamp),
  (33, (BeginNode 36), VoidStamp),
  (34, (IfNode 31 33 32), VoidStamp),
  (35, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test4(I)I'' [1]), VoidStamp),
  (36, (InvokeNode 36 35 None None (Some 37) 38), IntegerStamp 32 (-2147483648) (2147483647)),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (ReturnNode (Some 36) None), VoidStamp),
  (39, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Loop01.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ConstantNode (new_int 1 (1))), IntegerStamp 1 (-1) (-1)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.optimize.VN_Loop01::cond1'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.jtt.optimize.VN_Loop01::cond2'' 2 (Some 7) None 8), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (ReturnNode None None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test1(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (EndNode), VoidStamp),
  (7, (LoopBeginNode [6, 22] None (Some 8) 9), VoidStamp),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (LoadFieldNode 9 ''org.graalvm.compiler.jtt.optimize.VN_Loop01::cond1'' None 16), IntegerStamp 32 (0) (1)),
  (10, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (11, (IntegerEqualsNode 9 10), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (14, (LoopExitNode 7 (Some 15) 27), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (IfNode 11 14 12), VoidStamp),
  (17, (LoadFieldNode 17 ''org.graalvm.compiler.jtt.optimize.VN_Loop01::cond2'' None 24), IntegerStamp 32 (0) (1)),
  (18, (IntegerEqualsNode 17 10), VoidStamp),
  (20, (LoopExitNode 7 (Some 21) 26), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (LoopEndNode 7), VoidStamp),
  (23, (BeginNode 22), VoidStamp),
  (24, (IfNode 18 23 20), VoidStamp),
  (25, (AddNode 4 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (ReturnNode (Some 25) None), VoidStamp),
  (27, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test2(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 25] None (Some 7) 8), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (LoadFieldNode 8 ''org.graalvm.compiler.jtt.optimize.VN_Loop01::cond1'' None 15), IntegerStamp 32 (0) (1)),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (IntegerEqualsNode 8 9), VoidStamp),
  (11, (BeginNode 17), VoidStamp),
  (13, (LoopExitNode 6 (Some 14) 28), VoidStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (IfNode 10 13 11), VoidStamp),
  (16, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (17, (LoadFieldNode 17 ''org.graalvm.compiler.jtt.optimize.VN_Loop01::cond2'' None 24), IntegerStamp 32 (0) (1)),
  (18, (IntegerEqualsNode 17 9), VoidStamp),
  (20, (LoopExitNode 6 (Some 22) 27), VoidStamp),
  (21, (RefNode 16), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (BeginNode 25), VoidStamp),
  (24, (IfNode 18 23 20), VoidStamp),
  (25, (LoopEndNode 6), VoidStamp),
  (26, (AddNode 16 21), IntegerStamp 32 (-2147483648) (2147483647)),
  (27, (ReturnNode (Some 26) None), VoidStamp),
  (28, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test3(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Loop01::cond1'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 19), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (LoadFieldNode 11 ''org.graalvm.compiler.jtt.optimize.VN_Loop01::cond2'' None 15), IntegerStamp 32 (0) (1)),
  (12, (IntegerEqualsNode 11 6), VoidStamp),
  (13, (BeginNode 17), VoidStamp),
  (14, (BeginNode 18), VoidStamp),
  (15, (IfNode 12 14 13), VoidStamp),
  (16, (AddNode 4 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (17, (ReturnNode (Some 16) None), VoidStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp),
  (19, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test4(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.optimize.VN_Loop01::cond1'' None 10), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (IntegerEqualsNode 5 6), VoidStamp),
  (8, (BeginNode 11), VoidStamp),
  (9, (BeginNode 19), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (LoadFieldNode 11 ''org.graalvm.compiler.jtt.optimize.VN_Loop01::cond2'' None 15), IntegerStamp 32 (0) (1)),
  (12, (IntegerEqualsNode 11 6), VoidStamp),
  (13, (BeginNode 18), VoidStamp),
  (14, (BeginNode 17), VoidStamp),
  (15, (IfNode 12 14 13), VoidStamp),
  (16, (AddNode 4 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (17, (ReturnNode (Some 16) None), VoidStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp),
  (19, (ReturnNode (Some 3) None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.VN_Loop01.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_VN_Loop01_test ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test(I)I'' [(new_int 32 (0))] (new_int 32 (6))"

value "program_test unit_VN_Loop01_test ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test(I)I'' [(new_int 32 (1))] (new_int 32 (8))"

value "program_test unit_VN_Loop01_test ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test(I)I'' [(new_int 32 (2))] (new_int 32 (10))"

value "program_test unit_VN_Loop01_test ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test(I)I'' [(new_int 32 (3))] (new_int 32 (12))"

value "program_test unit_VN_Loop01_test ''org.graalvm.compiler.jtt.optimize.VN_Loop01.test(I)I'' [(new_int 32 (4))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/core/test/VeriOptFactorialTest;.VeriOptFactorialTest_fact*)
definition unit_VeriOptFactorialTest_fact :: Program where
  "unit_VeriOptFactorialTest_fact = Map.empty (
  ''org.graalvm.compiler.core.test.VeriOptFactorialTest.fact(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 21] None (Some 9) 17), VoidStamp),
  (7, (ValuePhiNode 7 [1, 20] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 18] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (IntegerLessThanNode 7 10), VoidStamp),
  (12, (BeginNode 21), VoidStamp),
  (14, (LoopExitNode 6 (Some 16) 22), VoidStamp),
  (15, (RefNode 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (IfNode 11 14 12), VoidStamp),
  (18, (MulNode 7 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (20, (AddNode 7 19), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (LoopEndNode 6), VoidStamp),
  (22, (ReturnNode (Some 15) None), VoidStamp)
  ],
  ''org.graalvm.compiler.core.test.VeriOptFactorialTest.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (3, (StoreFieldNode 3 ''org.graalvm.compiler.core.test.VeriOptFactorialTest::N'' 2 (Some 4) None 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.core.test.VeriOptFactorialTest.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_VeriOptFactorialTest_fact ''org.graalvm.compiler.core.test.VeriOptFactorialTest.fact(I)I'' [(new_int 32 (5))] (new_int 32 (120))"


(* Lorg/graalvm/compiler/core/test/VeriOptFactorialTest;.VeriOptFactorialTest_factAsAnObject*)
definition unit_VeriOptFactorialTest_factAsAnObject :: Program where
  "unit_VeriOptFactorialTest_factAsAnObject = Map.empty (
  ''org.graalvm.compiler.core.test.VeriOptFactorialTest.factAsAnObject(I)Lorg/graalvm/compiler/core/test/VeriOptFactorialTest$FactResult;'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NewInstanceNode 3 ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult'' None 6), ObjectStamp ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult'' True True False),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult::value'' 5 (Some 8) (Some 3) 10), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (FrameState [] (Some 7) None None), IllegalStamp),
  (10, (EndNode), VoidStamp),
  (11, (LoopBeginNode [10, 26] None (Some 13) 20), VoidStamp),
  (12, (ValuePhiNode 12 [1, 25] 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (13, (FrameState [] None None None), IllegalStamp),
  (14, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (15, (IntegerLessThanNode 12 14), VoidStamp),
  (16, (BeginNode 22), VoidStamp),
  (18, (LoopExitNode 11 (Some 19) 27), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (IfNode 15 18 16), VoidStamp),
  (21, (MethodCallTargetNode ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult.multiply(I)V'' [3, 12]), VoidStamp),
  (22, (InvokeNode 22 21 None None (Some 23) 26), VoidStamp),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (25, (AddNode 12 24), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (LoopEndNode 11), VoidStamp),
  (27, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.core.test.VeriOptFactorialTest.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (3, (StoreFieldNode 3 ''org.graalvm.compiler.core.test.VeriOptFactorialTest::N'' 2 (Some 4) None 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ],
  ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult.multiply(I)V'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), ObjectStamp ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult'' True True False),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (LoadFieldNode 4 ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult::value'' (Some 1) 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (MulNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult::value'' 5 (Some 7) (Some 1) 8), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.core.test.VeriOptFactorialTest.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
fun check_VeriOptFactorialTest_factAsAnObject_161 :: "Value \<Rightarrow> FieldRefHeap \<Rightarrow> bool" where
  "check_VeriOptFactorialTest_factAsAnObject_161 (ObjRef x) h = (True \<and> h_load_field ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult::value'' x h = (new_int 32 (120)))" |
  "check_VeriOptFactorialTest_factAsAnObject_161 _ _ = False"
value "object_test unit_VeriOptFactorialTest_factAsAnObject ''org.graalvm.compiler.core.test.VeriOptFactorialTest.factAsAnObject(I)Lorg/graalvm/compiler/core/test/VeriOptFactorialTest$FactResult;'' [(new_int 32 (5))] check_VeriOptFactorialTest_factAsAnObject_161"


(* Lorg/graalvm/compiler/core/test/VeriOptFactorialTest;.VeriOptFactorialTest_factStatic*)
definition unit_VeriOptFactorialTest_factStatic :: Program where
  "unit_VeriOptFactorialTest_factStatic = Map.empty (
  ''org.graalvm.compiler.core.test.VeriOptFactorialTest.factStatic()I'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (LoadFieldNode 3 ''org.graalvm.compiler.core.test.VeriOptFactorialTest::N'' None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 21] None (Some 9) 17), VoidStamp),
  (7, (ValuePhiNode 7 [2, 18] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 20] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (11, (IntegerLessThanNode 8 10), VoidStamp),
  (12, (BeginNode 21), VoidStamp),
  (14, (LoopExitNode 6 (Some 16) 22), VoidStamp),
  (15, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (IfNode 11 14 12), VoidStamp),
  (18, (MulNode 7 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (20, (AddNode 8 19), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (LoopEndNode 6), VoidStamp),
  (22, (ReturnNode (Some 15) None), VoidStamp)
  ],
  ''org.graalvm.compiler.core.test.VeriOptFactorialTest.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (3, (StoreFieldNode 3 ''org.graalvm.compiler.core.test.VeriOptFactorialTest::N'' 2 (Some 4) None 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.core.test.VeriOptFactorialTest.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_VeriOptFactorialTest_factStatic ''org.graalvm.compiler.core.test.VeriOptFactorialTest.factStatic()I'' [] (new_int 32 (120))"

end
