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


(* Lorg/graalvm/compiler/core/test/FloatingDivTest;.FloatingDivTest_snippet3*)
definition unit_FloatingDivTest_snippet3 :: IRGraph where
  "unit_FloatingDivTest_snippet3 = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (4, (NegateNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_FloatingDivTest_snippet3  [(new_int 32 (10))] (new_int 32 (-10))"

value "static_test unit_FloatingDivTest_snippet3  [(new_int 32 (-2147483648))] (new_int 32 (-2147483648))"


(* Lorg/graalvm/compiler/jtt/optimize/Fold_Convert01;.Fold_Convert01_test*)
definition unit_Fold_Convert01_test :: IRGraph where
  "unit_Fold_Convert01_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 17), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (ConstantNode (new_int 32 (128))), IntegerStamp 32 (128) (128)),
  (10, (ConstantNode (new_int 8 (-128))), IntegerStamp 8 (-128) (-128)),
  (11, (ConstantNode (new_int 32 (-128))), IntegerStamp 32 (-128) (-128)),
  (12, (ReturnNode (Some 11) None), VoidStamp),
  (13, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (14, (IntegerEqualsNode 1 13), VoidStamp),
  (15, (BeginNode 27), VoidStamp),
  (16, (BeginNode 22), VoidStamp),
  (17, (IfNode 14 16 15), VoidStamp),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ConstantNode (new_int 32 (32768))), IntegerStamp 32 (32768) (32768)),
  (20, (ConstantNode (new_int 16 (-32768))), IntegerStamp 16 (-32768) (-32768)),
  (21, (ConstantNode (new_int 32 (-32768))), IntegerStamp 32 (-32768) (-32768)),
  (22, (ReturnNode (Some 21) None), VoidStamp),
  (23, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (24, (IntegerEqualsNode 1 23), VoidStamp),
  (25, (BeginNode 33), VoidStamp),
  (26, (BeginNode 32), VoidStamp),
  (27, (IfNode 24 26 25), VoidStamp),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (30, (ConstantNode (new_int 16 (-1))), IntegerStamp 16 (-1) (-1)),
  (31, (ConstantNode (new_int 32 (65535))), IntegerStamp 32 (65535) (65535)),
  (32, (ReturnNode (Some 31) None), VoidStamp),
  (33, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Fold_Convert01_test  [(new_int 32 (0))] (new_int 32 (-128))"

value "static_test unit_Fold_Convert01_test  [(new_int 32 (1))] (new_int 32 (-32768))"

value "static_test unit_Fold_Convert01_test  [(new_int 32 (2))] (new_int 32 (65535))"


(* Lorg/graalvm/compiler/jtt/optimize/Fold_Int01;.Fold_Int01_test*)
definition unit_Fold_Int01_test :: IRGraph where
  "unit_Fold_Int01_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 17), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (10, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (11, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (12, (ReturnNode (Some 11) None), VoidStamp),
  (13, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (14, (IntegerEqualsNode 1 13), VoidStamp),
  (15, (BeginNode 27), VoidStamp),
  (16, (BeginNode 22), VoidStamp),
  (17, (IfNode 14 16 15), VoidStamp),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ConstantNode (new_int 32 (15))), IntegerStamp 32 (15) (15)),
  (20, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (21, (ConstantNode (new_int 32 (11))), IntegerStamp 32 (11) (11)),
  (22, (ReturnNode (Some 21) None), VoidStamp),
  (23, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (24, (IntegerEqualsNode 1 23), VoidStamp),
  (25, (BeginNode 35), VoidStamp),
  (26, (BeginNode 31), VoidStamp),
  (27, (IfNode 24 26 25), VoidStamp),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (30, (ConstantNode (new_int 32 (12))), IntegerStamp 32 (12) (12)),
  (31, (ReturnNode (Some 30) None), VoidStamp),
  (32, (IntegerEqualsNode 1 9), VoidStamp),
  (33, (BeginNode 43), VoidStamp),
  (34, (BeginNode 39), VoidStamp),
  (35, (IfNode 32 34 33), VoidStamp),
  (36, (FrameState [] None None None), IllegalStamp),
  (37, (ConstantNode (new_int 32 (26))), IntegerStamp 32 (26) (26)),
  (38, (ConstantNode (new_int 32 (13))), IntegerStamp 32 (13) (13)),
  (39, (ReturnNode (Some 38) None), VoidStamp),
  (40, (IntegerEqualsNode 1 20), VoidStamp),
  (41, (BeginNode 52), VoidStamp),
  (42, (BeginNode 47), VoidStamp),
  (43, (IfNode 40 42 41), VoidStamp),
  (44, (FrameState [] None None None), IllegalStamp),
  (45, (ConstantNode (new_int 32 (29))), IntegerStamp 32 (29) (29)),
  (46, (ConstantNode (new_int 32 (14))), IntegerStamp 32 (14) (14)),
  (47, (ReturnNode (Some 46) None), VoidStamp),
  (48, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (49, (IntegerEqualsNode 1 48), VoidStamp),
  (50, (BeginNode 59), VoidStamp),
  (51, (BeginNode 55), VoidStamp),
  (52, (IfNode 49 51 50), VoidStamp),
  (53, (FrameState [] None None None), IllegalStamp),
  (54, (ConstantNode (new_int 32 (31))), IntegerStamp 32 (31) (31)),
  (55, (ReturnNode (Some 19) None), VoidStamp),
  (56, (IntegerEqualsNode 1 29), VoidStamp),
  (57, (BeginNode 66), VoidStamp),
  (58, (BeginNode 62), VoidStamp),
  (59, (IfNode 56 58 57), VoidStamp),
  (60, (FrameState [] None None None), IllegalStamp),
  (61, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (62, (ReturnNode (Some 61) None), VoidStamp),
  (63, (IntegerEqualsNode 1 10), VoidStamp),
  (64, (BeginNode 70), VoidStamp),
  (65, (BeginNode 69), VoidStamp),
  (66, (IfNode 63 65 64), VoidStamp),
  (67, (FrameState [] None None None), IllegalStamp),
  (68, (ConstantNode (new_int 32 (17))), IntegerStamp 32 (17) (17)),
  (69, (ReturnNode (Some 68) None), VoidStamp),
  (70, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Fold_Int01_test  [(new_int 32 (0))] (new_int 32 (10))"

value "static_test unit_Fold_Int01_test  [(new_int 32 (1))] (new_int 32 (11))"

value "static_test unit_Fold_Int01_test  [(new_int 32 (2))] (new_int 32 (12))"

value "static_test unit_Fold_Int01_test  [(new_int 32 (3))] (new_int 32 (13))"

value "static_test unit_Fold_Int01_test  [(new_int 32 (4))] (new_int 32 (14))"

value "static_test unit_Fold_Int01_test  [(new_int 32 (5))] (new_int 32 (15))"

value "static_test unit_Fold_Int01_test  [(new_int 32 (6))] (new_int 32 (16))"

value "static_test unit_Fold_Int01_test  [(new_int 32 (7))] (new_int 32 (17))"


(* Lorg/graalvm/compiler/jtt/optimize/Fold_Int02;.Fold_Int02_test*)
definition unit_Fold_Int02_test :: Program where
  "unit_Fold_Int02_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.Fold_Int02.test(I)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Int02.equ()Z'' []), VoidStamp),
  (9, (InvokeNode 9 8 None None (Some 10) 11), IntegerStamp 32 (0) (1)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ReturnNode (Some 9) None), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (IntegerEqualsNode 1 12), VoidStamp),
  (14, (BeginNode 25), VoidStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 13 15 14), VoidStamp),
  (17, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Int02.neq()Z'' []), VoidStamp),
  (18, (InvokeNode 18 17 None None (Some 19) 20), IntegerStamp 32 (0) (1)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (ReturnNode (Some 18) None), VoidStamp),
  (21, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (22, (IntegerEqualsNode 1 21), VoidStamp),
  (23, (BeginNode 34), VoidStamp),
  (24, (BeginNode 27), VoidStamp),
  (25, (IfNode 22 24 23), VoidStamp),
  (26, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Int02.geq()Z'' []), VoidStamp),
  (27, (InvokeNode 27 26 None None (Some 28) 29), IntegerStamp 32 (0) (1)),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode (Some 27) None), VoidStamp),
  (30, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (31, (IntegerEqualsNode 1 30), VoidStamp),
  (32, (BeginNode 43), VoidStamp),
  (33, (BeginNode 36), VoidStamp),
  (34, (IfNode 31 33 32), VoidStamp),
  (35, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Int02.ge()Z'' []), VoidStamp),
  (36, (InvokeNode 36 35 None None (Some 37) 38), IntegerStamp 32 (0) (1)),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (ReturnNode (Some 36) None), VoidStamp),
  (39, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (40, (IntegerEqualsNode 1 39), VoidStamp),
  (41, (BeginNode 52), VoidStamp),
  (42, (BeginNode 45), VoidStamp),
  (43, (IfNode 40 42 41), VoidStamp),
  (44, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Int02.ltq()Z'' []), VoidStamp),
  (45, (InvokeNode 45 44 None None (Some 46) 47), IntegerStamp 32 (0) (1)),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (ReturnNode (Some 45) None), VoidStamp),
  (48, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (49, (IntegerEqualsNode 1 48), VoidStamp),
  (50, (BeginNode 57), VoidStamp),
  (51, (BeginNode 54), VoidStamp),
  (52, (IfNode 49 51 50), VoidStamp),
  (53, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Int02.lt()Z'' []), VoidStamp),
  (54, (InvokeNode 54 53 None None (Some 55) 56), IntegerStamp 32 (0) (1)),
  (55, (FrameState [] None None None), IllegalStamp),
  (56, (ReturnNode (Some 54) None), VoidStamp),
  (57, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Int02.equ()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (34))), IntegerStamp 32 (34) (34)),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Int02.neq()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (34))), IntegerStamp 32 (34) (34)),
  (3, (ConstantNode (new_int 32 (33))), IntegerStamp 32 (33) (33)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Int02.geq()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (34))), IntegerStamp 32 (34) (34)),
  (3, (ConstantNode (new_int 32 (33))), IntegerStamp 32 (33) (33)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Int02.ge()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (34))), IntegerStamp 32 (34) (34)),
  (3, (ConstantNode (new_int 32 (35))), IntegerStamp 32 (35) (35)),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Int02.ltq()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (34))), IntegerStamp 32 (34) (34)),
  (3, (ConstantNode (new_int 32 (32))), IntegerStamp 32 (32) (32)),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Int02.lt()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (34))), IntegerStamp 32 (34) (34)),
  (3, (ConstantNode (new_int 32 (31))), IntegerStamp 32 (31) (31)),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]
  )"
value "program_test unit_Fold_Int02_test ''org.graalvm.compiler.jtt.optimize.Fold_Int02.test(I)Z'' [(new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_Fold_Int02_test ''org.graalvm.compiler.jtt.optimize.Fold_Int02.test(I)Z'' [(new_int 32 (1))] (new_int 32 (1))"

value "program_test unit_Fold_Int02_test ''org.graalvm.compiler.jtt.optimize.Fold_Int02.test(I)Z'' [(new_int 32 (2))] (new_int 32 (1))"

value "program_test unit_Fold_Int02_test ''org.graalvm.compiler.jtt.optimize.Fold_Int02.test(I)Z'' [(new_int 32 (3))] (new_int 32 (0))"

value "program_test unit_Fold_Int02_test ''org.graalvm.compiler.jtt.optimize.Fold_Int02.test(I)Z'' [(new_int 32 (4))] (new_int 32 (0))"

value "program_test unit_Fold_Int02_test ''org.graalvm.compiler.jtt.optimize.Fold_Int02.test(I)Z'' [(new_int 32 (5))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/Fold_Long02;.Fold_Long02_test*)
definition unit_Fold_Long02_test :: Program where
  "unit_Fold_Long02_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.Fold_Long02.test(I)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Long02.equ()Z'' []), VoidStamp),
  (9, (InvokeNode 9 8 None None (Some 10) 11), IntegerStamp 32 (0) (1)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ReturnNode (Some 9) None), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (IntegerEqualsNode 1 12), VoidStamp),
  (14, (BeginNode 25), VoidStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 13 15 14), VoidStamp),
  (17, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Long02.neq()Z'' []), VoidStamp),
  (18, (InvokeNode 18 17 None None (Some 19) 20), IntegerStamp 32 (0) (1)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (ReturnNode (Some 18) None), VoidStamp),
  (21, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (22, (IntegerEqualsNode 1 21), VoidStamp),
  (23, (BeginNode 34), VoidStamp),
  (24, (BeginNode 27), VoidStamp),
  (25, (IfNode 22 24 23), VoidStamp),
  (26, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Long02.geq()Z'' []), VoidStamp),
  (27, (InvokeNode 27 26 None None (Some 28) 29), IntegerStamp 32 (0) (1)),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode (Some 27) None), VoidStamp),
  (30, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (31, (IntegerEqualsNode 1 30), VoidStamp),
  (32, (BeginNode 43), VoidStamp),
  (33, (BeginNode 36), VoidStamp),
  (34, (IfNode 31 33 32), VoidStamp),
  (35, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Long02.ge()Z'' []), VoidStamp),
  (36, (InvokeNode 36 35 None None (Some 37) 38), IntegerStamp 32 (0) (1)),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (ReturnNode (Some 36) None), VoidStamp),
  (39, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (40, (IntegerEqualsNode 1 39), VoidStamp),
  (41, (BeginNode 52), VoidStamp),
  (42, (BeginNode 45), VoidStamp),
  (43, (IfNode 40 42 41), VoidStamp),
  (44, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Long02.ltq()Z'' []), VoidStamp),
  (45, (InvokeNode 45 44 None None (Some 46) 47), IntegerStamp 32 (0) (1)),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (ReturnNode (Some 45) None), VoidStamp),
  (48, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (49, (IntegerEqualsNode 1 48), VoidStamp),
  (50, (BeginNode 57), VoidStamp),
  (51, (BeginNode 54), VoidStamp),
  (52, (IfNode 49 51 50), VoidStamp),
  (53, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Fold_Long02.lt()Z'' []), VoidStamp),
  (54, (InvokeNode 54 53 None None (Some 55) 56), IntegerStamp 32 (0) (1)),
  (55, (FrameState [] None None None), IllegalStamp),
  (56, (ReturnNode (Some 54) None), VoidStamp),
  (57, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Long02.equ()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (34))), IntegerStamp 64 (34) (34)),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Long02.neq()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 6), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (34))), IntegerStamp 64 (34) (34)),
  (3, (ConstantNode (IntVal 64 (33))), IntegerStamp 64 (33) (33)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Long02.geq()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 6), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (34))), IntegerStamp 64 (34) (34)),
  (3, (ConstantNode (IntVal 64 (33))), IntegerStamp 64 (33) (33)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Long02.ge()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 6), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (34))), IntegerStamp 64 (34) (34)),
  (3, (ConstantNode (IntVal 64 (35))), IntegerStamp 64 (35) (35)),
  (4, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Long02.ltq()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 6), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (34))), IntegerStamp 64 (34) (34)),
  (3, (ConstantNode (IntVal 64 (32))), IntegerStamp 64 (32) (32)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Fold_Long02.lt()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 6), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (34))), IntegerStamp 64 (34) (34)),
  (3, (ConstantNode (IntVal 64 (31))), IntegerStamp 64 (31) (31)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]
  )"
value "program_test unit_Fold_Long02_test ''org.graalvm.compiler.jtt.optimize.Fold_Long02.test(I)Z'' [(new_int 32 (0))] (new_int 32 (1))"

value "program_test unit_Fold_Long02_test ''org.graalvm.compiler.jtt.optimize.Fold_Long02.test(I)Z'' [(new_int 32 (1))] (new_int 32 (1))"

value "program_test unit_Fold_Long02_test ''org.graalvm.compiler.jtt.optimize.Fold_Long02.test(I)Z'' [(new_int 32 (2))] (new_int 32 (1))"

value "program_test unit_Fold_Long02_test ''org.graalvm.compiler.jtt.optimize.Fold_Long02.test(I)Z'' [(new_int 32 (3))] (new_int 32 (0))"

value "program_test unit_Fold_Long02_test ''org.graalvm.compiler.jtt.optimize.Fold_Long02.test(I)Z'' [(new_int 32 (4))] (new_int 32 (0))"

value "program_test unit_Fold_Long02_test ''org.graalvm.compiler.jtt.optimize.Fold_Long02.test(I)Z'' [(new_int 32 (5))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/core/test/FuzzTest36456;.FuzzTest36456_method0*)
definition unit_FuzzTest36456_method0 :: IRGraph where
  "unit_FuzzTest36456_method0 = irgraph [
  (0, (StartNode (Some 2) 9), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (15430))), IntegerStamp 32 (15430) (15430)),
  (4, (ConstantNode (new_int 32 (2147483646))), IntegerStamp 32 (2147483646) (2147483646)),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (IntegerLessThanNode 1 4), VoidStamp),
  (7, (BeginNode 18), VoidStamp),
  (8, (BeginNode 16), VoidStamp),
  (9, (IfNode 6 8 7), VoidStamp),
  (10, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (12, (IntegerEqualsNode 1 4), VoidStamp),
  (13, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (14, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ConditionalNode 12 13 14), IntegerStamp 32 (0) (1)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18] (Some 21) 26), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [10, 15] 17), IntegerStamp 32 (-1) (1)),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (FrameState [] (Some 20) None None), IllegalStamp),
  (22, (NarrowNode 32 16 19), IntegerStamp 16 (-1) (1)),
  (23, (ZeroExtendNode 16 32 22), IntegerStamp 32 (0) (65535)),
  (24, (IntegerBelowNode 23 3), VoidStamp),
  (25, (ConditionalNode 24 14 13), IntegerStamp 32 (0) (1)),
  (26, (ReturnNode (Some 25) None), VoidStamp)
  ]"
value "static_test unit_FuzzTest36456_method0  [(new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/core/test/FuzzTest36456;.FuzzTest36456_method1*)
definition unit_FuzzTest36456_method1 :: IRGraph where
  "unit_FuzzTest36456_method1 = irgraph [
  (0, (StartNode (Some 2) 9), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (15430))), IntegerStamp 32 (15430) (15430)),
  (4, (ConstantNode (new_int 32 (2147483646))), IntegerStamp 32 (2147483646) (2147483646)),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (IntegerLessThanNode 1 4), VoidStamp),
  (7, (BeginNode 18), VoidStamp),
  (8, (BeginNode 16), VoidStamp),
  (9, (IfNode 6 8 7), VoidStamp),
  (10, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (12, (IntegerEqualsNode 1 4), VoidStamp),
  (13, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (14, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ConditionalNode 12 13 14), IntegerStamp 32 (0) (1)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18] (Some 21) 28), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [10, 15] 17), IntegerStamp 32 (-1) (1)),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (FrameState [] (Some 20) None None), IllegalStamp),
  (22, (NarrowNode 32 16 19), IntegerStamp 16 (-1) (1)),
  (23, (ZeroExtendNode 16 32 22), IntegerStamp 32 (0) (65535)),
  (24, (NarrowNode 32 16 23), IntegerStamp 16 (-32768) (32767)),
  (25, (SignExtendNode 16 32 24), IntegerStamp 32 (-32768) (32767)),
  (26, (IntegerLessThanNode 25 3), VoidStamp),
  (27, (ConditionalNode 26 14 13), IntegerStamp 32 (0) (1)),
  (28, (ReturnNode (Some 27) None), VoidStamp)
  ]"
value "static_test unit_FuzzTest36456_method1  [(new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/hotpath/HP_allocate01;.HP_allocate01_test*)
definition unit_HP_allocate01_test :: IRGraph where
  "unit_HP_allocate01_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 20] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [3, 17] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 19] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 8 1), VoidStamp),
  (12, (LoopExitNode 6 (Some 14) 21), VoidStamp),
  (13, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 20), VoidStamp),
  (16, (IfNode 10 15 12), VoidStamp),
  (17, (AddNode 7 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (18, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (19, (AddNode 8 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (20, (LoopEndNode 6), VoidStamp),
  (21, (ReturnNode (Some 13) None), VoidStamp)
  ]"
value "static_test unit_HP_allocate01_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_HP_allocate01_test  [(new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_HP_allocate01_test  [(new_int 32 (2))] (new_int 32 (1))"

value "static_test unit_HP_allocate01_test  [(new_int 32 (3))] (new_int 32 (3))"

value "static_test unit_HP_allocate01_test  [(new_int 32 (80))] (new_int 32 (3160))"


(* Lorg/graalvm/compiler/jtt/hotpath/HP_control01;.HP_control01_test*)
definition unit_HP_control01_test :: IRGraph where
  "unit_HP_control01_test = irgraph [
  (0, (StartNode (Some 2) 9), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (5, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (6, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (7, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (9, (EndNode), VoidStamp),
  (10, (LoopBeginNode [9, 28] None (Some 16) 26), VoidStamp),
  (11, (ValuePhiNode 11 [3, 12] 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (12, (ValuePhiNode 12 [4, 13] 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (13, (ValuePhiNode 13 [5, 14] 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (ValuePhiNode 14 [6, 12] 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (ValuePhiNode 15 [7, 27] 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (IntegerLessThanNode 15 1), VoidStamp),
  (19, (LoopExitNode 10 (Some 24) 38), VoidStamp),
  (20, (RefNode 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (RefNode 12), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (RefNode 13), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (RefNode 14), IntegerStamp 32 (-2147483648) (2147483647)),
  (24, (FrameState [] None None None), IllegalStamp),
  (25, (BeginNode 28), VoidStamp),
  (26, (IfNode 17 25 19), VoidStamp),
  (27, (AddNode 15 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (28, (LoopEndNode 10), VoidStamp),
  (29, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (30, (MulNode 21 29), IntegerStamp 32 (-2147483648) (2147483647)),
  (31, (AddNode 20 30), IntegerStamp 32 (-2147483648) (2147483647)),
  (32, (ConstantNode (new_int 32 (100))), IntegerStamp 32 (100) (100)),
  (33, (MulNode 22 32), IntegerStamp 32 (-2147483648) (2147483647)),
  (34, (AddNode 31 33), IntegerStamp 32 (-2147483648) (2147483647)),
  (35, (ConstantNode (new_int 32 (1000))), IntegerStamp 32 (1000) (1000)),
  (36, (MulNode 23 35), IntegerStamp 32 (-2147483648) (2147483647)),
  (37, (AddNode 34 36), IntegerStamp 32 (-2147483648) (2147483647)),
  (38, (ReturnNode (Some 37) None), VoidStamp)
  ]"
value "static_test unit_HP_control01_test  [(new_int 32 (40))] (new_int 32 (2432))"

value "static_test unit_HP_control01_test  [(new_int 32 (80))] (new_int 32 (3243))"


(* Lorg/graalvm/compiler/jtt/hotpath/HP_dead01;.HP_dead01_test*)
definition unit_HP_dead01_test :: IRGraph where
  "unit_HP_dead01_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 32] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [3, 30] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 31] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 1 8), VoidStamp),
  (11, (BeginNode 32), VoidStamp),
  (13, (LoopExitNode 6 (Some 15) 33), VoidStamp),
  (14, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (IfNode 10 13 11), VoidStamp),
  (17, (AddNode 8 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (18, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (19, (ConstantNode (new_int 32 (31))), IntegerStamp 32 (31) (31)),
  (20, (RightShiftNode 8 19), IntegerStamp 32 (-1) (0)),
  (21, (UnsignedRightShiftNode 20 19), IntegerStamp 32 (0) (1)),
  (22, (AddNode 21 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (24, (RightShiftNode 22 23), IntegerStamp 32 (-1073741824) (1073741823)),
  (25, (MulNode 8 24), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (27, (ConstantNode (new_int 32 (-10))), IntegerStamp 32 (-10) (-10)),
  (28, (AddNode 25 27), IntegerStamp 32 (-2147483648) (2147483647)),
  (29, (AddNode 17 28), IntegerStamp 32 (-2147483648) (2147483647)),
  (30, (AddNode 7 17), IntegerStamp 32 (-2147483648) (2147483647)),
  (31, (AddNode 8 23), IntegerStamp 32 (-2147483648) (2147483647)),
  (32, (LoopEndNode 6), VoidStamp),
  (33, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_HP_dead01_test  [(new_int 32 (10))] (new_int 32 (110))"

value "static_test unit_HP_dead01_test  [(new_int 32 (20))] (new_int 32 (420))"

value "static_test unit_HP_dead01_test  [(new_int 32 (30))] (new_int 32 (930))"

value "static_test unit_HP_dead01_test  [(new_int 32 (40))] (new_int 32 (1640))"


(* Lorg/graalvm/compiler/jtt/hotpath/HP_field01;.HP_field01_test*)
definition unit_HP_field01_test :: IRGraph where
  "unit_HP_field01_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 47] None (Some 8) 14), VoidStamp),
  (7, (ValuePhiNode 7 [3, 46] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (IntegerLessThanNode 1 7), VoidStamp),
  (10, (BeginNode 20), VoidStamp),
  (12, (LoopExitNode 6 (Some 13) 48), VoidStamp),
  (13, (FrameState [] None None None), IllegalStamp),
  (14, (IfNode 9 12 10), VoidStamp),
  (15, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (16, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (17, (IntegerLessThanNode 7 16), VoidStamp),
  (18, (BeginNode 21), VoidStamp),
  (19, (BeginNode 31), VoidStamp),
  (20, (IfNode 17 19 18), VoidStamp),
  (21, (LoadFieldNode 21 ''org.graalvm.compiler.jtt.hotpath.HP_field01::a'' None 23), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (AddNode 7 21), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (StoreFieldNode 23 ''org.graalvm.compiler.jtt.hotpath.HP_field01::a'' 22 (Some 24) None 36), VoidStamp),
  (24, (FrameState [] None None None), IllegalStamp),
  (26, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (27, (ConstantNode (new_int 32 (8))), IntegerStamp 32 (8) (8)),
  (28, (IntegerLessThanNode 7 27), VoidStamp),
  (29, (BeginNode 32), VoidStamp),
  (30, (BeginNode 39), VoidStamp),
  (31, (IfNode 28 30 29), VoidStamp),
  (32, (LoadFieldNode 32 ''org.graalvm.compiler.jtt.hotpath.HP_field01::b'' None 34), IntegerStamp 32 (-2147483648) (2147483647)),
  (33, (AddNode 7 32), IntegerStamp 32 (-2147483648) (2147483647)),
  (34, (StoreFieldNode 34 ''org.graalvm.compiler.jtt.hotpath.HP_field01::b'' 33 (Some 35) None 38), VoidStamp),
  (35, (FrameState [] None None None), IllegalStamp),
  (36, (EndNode), VoidStamp),
  (37, (MergeNode [36, 38, 43] (Some 44) 47), VoidStamp),
  (38, (EndNode), VoidStamp),
  (39, (LoadFieldNode 39 ''org.graalvm.compiler.jtt.hotpath.HP_field01::c'' None 41), IntegerStamp 32 (-2147483648) (2147483647)),
  (40, (AddNode 7 39), IntegerStamp 32 (-2147483648) (2147483647)),
  (41, (StoreFieldNode 41 ''org.graalvm.compiler.jtt.hotpath.HP_field01::c'' 40 (Some 42) None 43), VoidStamp),
  (42, (FrameState [] None None None), IllegalStamp),
  (43, (EndNode), VoidStamp),
  (44, (FrameState [] None None None), IllegalStamp),
  (45, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (46, (AddNode 7 45), IntegerStamp 32 (-2147483648) (2147483647)),
  (47, (LoopEndNode 6), VoidStamp),
  (48, (LoadFieldNode 48 ''org.graalvm.compiler.jtt.hotpath.HP_field01::a'' None 49), IntegerStamp 32 (-2147483648) (2147483647)),
  (49, (LoadFieldNode 49 ''org.graalvm.compiler.jtt.hotpath.HP_field01::b'' None 51), IntegerStamp 32 (-2147483648) (2147483647)),
  (50, (AddNode 48 49), IntegerStamp 32 (-2147483648) (2147483647)),
  (51, (LoadFieldNode 51 ''org.graalvm.compiler.jtt.hotpath.HP_field01::c'' None 53), IntegerStamp 32 (-2147483648) (2147483647)),
  (52, (AddNode 50 51), IntegerStamp 32 (-2147483648) (2147483647)),
  (53, (ReturnNode (Some 52) None), VoidStamp)
  ]"
value "static_test unit_HP_field01_test  [(new_int 32 (40))] (new_int 32 (820))"


(* Lorg/graalvm/compiler/jtt/hotpath/HP_field02;.HP_field02_test*)
definition unit_HP_field02_test :: Program where
  "unit_HP_field02_test = Map.empty (
  ''org.graalvm.compiler.jtt.hotpath.HP_field02.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NewInstanceNode 3 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass'' None 6), ObjectStamp ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass'' True True False),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (MethodCallTargetNode ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass.run(I)I'' [3, 1]), VoidStamp),
  (6, (InvokeNode 6 5 None None (Some 7) 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass.run(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 6), VoidStamp),
  (1, (ParameterNode 0), ObjectStamp ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass'' True True False),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (EndNode), VoidStamp),
  (7, (LoopBeginNode [6, 48] None (Some 9) 15), VoidStamp),
  (8, (ValuePhiNode 8 [4, 47] 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 2 8), VoidStamp),
  (11, (BeginNode 21), VoidStamp),
  (13, (LoopExitNode 7 (Some 14) 49), VoidStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (IfNode 10 13 11), VoidStamp),
  (16, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (17, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (18, (IntegerLessThanNode 8 17), VoidStamp),
  (19, (BeginNode 22), VoidStamp),
  (20, (BeginNode 32), VoidStamp),
  (21, (IfNode 18 20 19), VoidStamp),
  (22, (LoadFieldNode 22 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::a'' (Some 1) 24), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (AddNode 8 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (24, (StoreFieldNode 24 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::a'' 23 (Some 25) (Some 1) 37), VoidStamp),
  (25, (FrameState [] None None None), IllegalStamp),
  (27, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (28, (ConstantNode (new_int 32 (8))), IntegerStamp 32 (8) (8)),
  (29, (IntegerLessThanNode 8 28), VoidStamp),
  (30, (BeginNode 33), VoidStamp),
  (31, (BeginNode 40), VoidStamp),
  (32, (IfNode 29 31 30), VoidStamp),
  (33, (LoadFieldNode 33 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::b'' (Some 1) 35), IntegerStamp 32 (-2147483648) (2147483647)),
  (34, (AddNode 8 33), IntegerStamp 32 (-2147483648) (2147483647)),
  (35, (StoreFieldNode 35 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::b'' 34 (Some 36) (Some 1) 39), VoidStamp),
  (36, (FrameState [] None None None), IllegalStamp),
  (37, (EndNode), VoidStamp),
  (38, (MergeNode [37, 39, 44] (Some 45) 48), VoidStamp),
  (39, (EndNode), VoidStamp),
  (40, (LoadFieldNode 40 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::c'' (Some 1) 42), IntegerStamp 32 (-2147483648) (2147483647)),
  (41, (AddNode 8 40), IntegerStamp 32 (-2147483648) (2147483647)),
  (42, (StoreFieldNode 42 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::c'' 41 (Some 43) (Some 1) 44), VoidStamp),
  (43, (FrameState [] None None None), IllegalStamp),
  (44, (EndNode), VoidStamp),
  (45, (FrameState [] None None None), IllegalStamp),
  (46, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (47, (AddNode 8 46), IntegerStamp 32 (-2147483648) (2147483647)),
  (48, (LoopEndNode 7), VoidStamp),
  (49, (LoadFieldNode 49 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::a'' (Some 1) 50), IntegerStamp 32 (-2147483648) (2147483647)),
  (50, (LoadFieldNode 50 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::b'' (Some 1) 52), IntegerStamp 32 (-2147483648) (2147483647)),
  (51, (AddNode 49 50), IntegerStamp 32 (-2147483648) (2147483647)),
  (52, (LoadFieldNode 52 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::c'' (Some 1) 54), IntegerStamp 32 (-2147483648) (2147483647)),
  (53, (AddNode 51 52), IntegerStamp 32 (-2147483648) (2147483647)),
  (54, (ReturnNode (Some 53) None), VoidStamp)
  ]
  )"
value "program_test unit_HP_field02_test ''org.graalvm.compiler.jtt.hotpath.HP_field02.test(I)I'' [(new_int 32 (40))] (new_int 32 (820))"


(* Lorg/graalvm/compiler/jtt/hotpath/HP_inline01;.HP_inline01_test*)
definition unit_HP_inline01_test :: Program where
  "unit_HP_inline01_test = Map.empty (
  ''org.graalvm.compiler.jtt.hotpath.HP_inline01.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 23] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [3, 20] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 22] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 8 1), VoidStamp),
  (12, (LoopExitNode 6 (Some 14) 24), VoidStamp),
  (13, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 10 15 12), VoidStamp),
  (17, (MethodCallTargetNode ''org.graalvm.compiler.jtt.hotpath.HP_inline01.foo(I)I'' [8]), VoidStamp),
  (18, (InvokeNode 18 17 None None (Some 19) 23), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (AddNode 7 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (22, (AddNode 8 21), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (LoopEndNode 6), VoidStamp),
  (24, (ReturnNode (Some 13) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.hotpath.HP_inline01.foo(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (15))), IntegerStamp 32 (15) (15)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (AddNode 1 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (ReturnNode (Some 10) None), VoidStamp),
  (12, (FrameState [] None None None), IllegalStamp),
  (13, (AddNode 10 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (ReturnNode (Some 13) None), VoidStamp)
  ]
  )"
value "program_test unit_HP_inline01_test ''org.graalvm.compiler.jtt.hotpath.HP_inline01.test(I)I'' [(new_int 32 (20))] (new_int 32 (215))"


(* Lorg/graalvm/compiler/jtt/hotpath/HP_inline02;.HP_inline02_test*)
definition unit_HP_inline02_test :: Program where
  "unit_HP_inline02_test = Map.empty (
  ''org.graalvm.compiler.jtt.hotpath.HP_inline02.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 23] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [3, 20] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 22] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 8 1), VoidStamp),
  (12, (LoopExitNode 6 (Some 14) 24), VoidStamp),
  (13, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 10 15 12), VoidStamp),
  (17, (MethodCallTargetNode ''org.graalvm.compiler.jtt.hotpath.HP_inline02.foo(II)I'' [8, 7]), VoidStamp),
  (18, (InvokeNode 18 17 None None (Some 19) 23), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (AddNode 7 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (22, (AddNode 8 21), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (LoopEndNode 6), VoidStamp),
  (24, (ReturnNode (Some 13) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.hotpath.HP_inline02.foo(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (18))), IntegerStamp 32 (18) (18)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
  (7, (BeginNode 11), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (SubNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (MethodCallTargetNode ''org.graalvm.compiler.jtt.hotpath.HP_inline02.bar(II)I'' [1, 9]), VoidStamp),
  (11, (InvokeNode 11 10 None None (Some 12) 13), IntegerStamp 32 (-2147483648) (2147483647)),
  (12, (FrameState [] None None None), IllegalStamp),
  (13, (ReturnNode (Some 11) None), VoidStamp),
  (14, (AddNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (MethodCallTargetNode ''org.graalvm.compiler.jtt.hotpath.HP_inline02.bar(II)I'' [1, 14]), VoidStamp),
  (16, (InvokeNode 16 15 None None (Some 17) 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.hotpath.HP_inline02.bar(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (15))), IntegerStamp 32 (15) (15)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 17), VoidStamp),
  (7, (BeginNode 11), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (AddNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (MethodCallTargetNode ''org.graalvm.compiler.jtt.hotpath.HP_inline02.car(II)I'' [1, 9]), VoidStamp),
  (11, (InvokeNode 11 10 None None (Some 12) 13), IntegerStamp 32 (-2147483648) (2147483647)),
  (12, (FrameState [] None None None), IllegalStamp),
  (13, (ReturnNode (Some 11) None), VoidStamp),
  (14, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (16, (AddNode 1 15), IntegerStamp 32 (-2147483648) (2147483647)),
  (17, (ReturnNode (Some 16) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.hotpath.HP_inline02.car(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (13))), IntegerStamp 32 (13) (13)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (BeginNode 11), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (AddNode 1 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (ReturnNode (Some 10) None), VoidStamp),
  (12, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (13, (AddNode 1 12), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (ReturnNode (Some 13) None), VoidStamp)
  ]
  )"
value "program_test unit_HP_inline02_test ''org.graalvm.compiler.jtt.hotpath.HP_inline02.test(I)I'' [(new_int 32 (20))] (new_int 32 (196))"


(* Lorg/graalvm/compiler/jtt/hotpath/HP_nest01;.HP_nest01_test*)
definition unit_HP_nest01_test :: IRGraph where
  "unit_HP_nest01_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 52] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [3, 44] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 51] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 8 1), VoidStamp),
  (12, (LoopExitNode 6 (Some 14) 53), VoidStamp),
  (13, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 19), VoidStamp),
  (16, (IfNode 10 15 12), VoidStamp),
  (17, (AddNode 7 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (EndNode), VoidStamp),
  (20, (LoopBeginNode [19, 34] None (Some 23) 30), VoidStamp),
  (21, (ValuePhiNode 21 [17, 31] 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (ValuePhiNode 22 [3, 33] 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (IntegerLessThanNode 22 1), VoidStamp),
  (26, (LoopExitNode 20 (Some 28) 36), VoidStamp),
  (27, (RefNode 21), IntegerStamp 32 (-2147483648) (2147483647)),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (BeginNode 34), VoidStamp),
  (30, (IfNode 24 29 26), VoidStamp),
  (31, (AddNode 21 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (32, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (33, (AddNode 22 32), IntegerStamp 32 (-2147483648) (2147483647)),
  (34, (LoopEndNode 20), VoidStamp),
  (36, (EndNode), VoidStamp),
  (37, (LoopBeginNode [36, 50] None (Some 40) 47), VoidStamp),
  (38, (ValuePhiNode 38 [27, 48] 37), IntegerStamp 32 (-2147483648) (2147483647)),
  (39, (ValuePhiNode 39 [3, 49] 37), IntegerStamp 32 (-2147483648) (2147483647)),
  (40, (FrameState [] None None None), IllegalStamp),
  (41, (IntegerLessThanNode 39 1), VoidStamp),
  (43, (LoopExitNode 37 (Some 45) 52), VoidStamp),
  (44, (RefNode 38), IntegerStamp 32 (-2147483648) (2147483647)),
  (45, (FrameState [] None None None), IllegalStamp),
  (46, (BeginNode 50), VoidStamp),
  (47, (IfNode 41 46 43), VoidStamp),
  (48, (AddNode 38 39), IntegerStamp 32 (-2147483648) (2147483647)),
  (49, (AddNode 39 32), IntegerStamp 32 (-2147483648) (2147483647)),
  (50, (LoopEndNode 37), VoidStamp),
  (51, (AddNode 8 32), IntegerStamp 32 (-2147483648) (2147483647)),
  (52, (LoopEndNode 6), VoidStamp),
  (53, (ReturnNode (Some 13) None), VoidStamp)
  ]"
value "static_test unit_HP_nest01_test  [(new_int 32 (15))] (new_int 32 (3255))"

end
