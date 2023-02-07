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


(* Lorg/graalvm/compiler/jtt/optimize/Reduce_IntShift02;.Reduce_IntShift02_test*)
definition unit_Reduce_IntShift02_test :: IRGraph where
  "unit_Reduce_IntShift02_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 20), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (80))), IntegerStamp 32 (80) (80)),
  (9, (AddNode 1 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (12, (UnsignedRightShiftNode 9 11), IntegerStamp 32 (0) (536870911)),
  (13, (ConstantNode (new_int 32 (-8))), IntegerStamp 32 (-8) (-8)),
  (14, (AndNode 9 13), IntegerStamp 32 (-2147483648) (2147483640)),
  (15, (ReturnNode (Some 14) None), VoidStamp),
  (16, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (17, (IntegerEqualsNode 1 16), VoidStamp),
  (18, (BeginNode 32), VoidStamp),
  (19, (BeginNode 27), VoidStamp),
  (20, (IfNode 17 19 18), VoidStamp),
  (21, (ConstantNode (new_int 32 (-2147483638))), IntegerStamp 32 (-2147483638) (-2147483638)),
  (22, (AddNode 1 21), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (LeftShiftNode 22 11), IntegerStamp 32 (-2147483648) (2147483640)),
  (25, (ConstantNode (new_int 32 (536870911))), IntegerStamp 32 (536870911) (536870911)),
  (26, (AndNode 22 25), IntegerStamp 32 (0) (536870911)),
  (27, (ReturnNode (Some 26) None), VoidStamp),
  (28, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (29, (IntegerEqualsNode 1 28), VoidStamp),
  (30, (BeginNode 43), VoidStamp),
  (31, (BeginNode 39), VoidStamp),
  (32, (IfNode 29 31 30), VoidStamp),
  (33, (ConstantNode (new_int 32 (192))), IntegerStamp 32 (192) (192)),
  (34, (AddNode 1 33), IntegerStamp 32 (-2147483648) (2147483647)),
  (35, (FrameState [] None None None), IllegalStamp),
  (36, (RightShiftNode 34 11), IntegerStamp 32 (-268435456) (268435455)),
  (37, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (38, (RightShiftNode 34 37), IntegerStamp 32 (-134217728) (134217727)),
  (39, (ReturnNode (Some 38) None), VoidStamp),
  (40, (IntegerEqualsNode 1 11), VoidStamp),
  (41, (BeginNode 53), VoidStamp),
  (42, (BeginNode 49), VoidStamp),
  (43, (IfNode 40 42 41), VoidStamp),
  (44, (ConstantNode (new_int 32 (208))), IntegerStamp 32 (208) (208)),
  (45, (AddNode 1 44), IntegerStamp 32 (-2147483648) (2147483647)),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (UnsignedRightShiftNode 45 11), IntegerStamp 32 (0) (536870911)),
  (48, (UnsignedRightShiftNode 45 37), IntegerStamp 32 (0) (268435455)),
  (49, (ReturnNode (Some 48) None), VoidStamp),
  (50, (IntegerEqualsNode 1 37), VoidStamp),
  (51, (BeginNode 62), VoidStamp),
  (52, (BeginNode 57), VoidStamp),
  (53, (IfNode 50 52 51), VoidStamp),
  (54, (FrameState [] None None None), IllegalStamp),
  (55, (LeftShiftNode 1 11), IntegerStamp 32 (-2147483648) (2147483640)),
  (56, (LeftShiftNode 1 37), IntegerStamp 32 (-2147483648) (2147483632)),
  (57, (ReturnNode (Some 56) None), VoidStamp),
  (58, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (59, (IntegerEqualsNode 1 58), VoidStamp),
  (60, (BeginNode 68), VoidStamp),
  (61, (BeginNode 67), VoidStamp),
  (62, (IfNode 59 61 60), VoidStamp),
  (63, (FrameState [] None None None), IllegalStamp),
  (64, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (65, (LeftShiftNode 1 64), IntegerStamp 32 (-2147483648) (2147418112)),
  (66, (ConstantNode (new_int 32 (17))), IntegerStamp 32 (17) (17)),
  (67, (ReturnNode (Some 3) None), VoidStamp),
  (68, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Reduce_IntShift02_test  [(new_int 32 (0))] (new_int 32 (80))"

value "static_test unit_Reduce_IntShift02_test  [(new_int 32 (1))] (new_int 32 (11))"

value "static_test unit_Reduce_IntShift02_test  [(new_int 32 (2))] (new_int 32 (12))"

value "static_test unit_Reduce_IntShift02_test  [(new_int 32 (3))] (new_int 32 (13))"

value "static_test unit_Reduce_IntShift02_test  [(new_int 32 (4))] (new_int 32 (64))"

value "static_test unit_Reduce_IntShift02_test  [(new_int 32 (5))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/micro/StrangeFrames;.StrangeFrames_test*)
definition unit_StrangeFrames_test :: Program where
  "unit_StrangeFrames_test = Map.empty (
  ''org.graalvm.compiler.jtt.micro.StrangeFrames.test(I)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (NewInstanceNode 5 ''org.graalvm.compiler.jtt.JTTTest$DummyTestClass'' None 9), ObjectStamp ''org.graalvm.compiler.jtt.JTTTest$DummyTestClass'' True True False),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (FrameState [] (Some 6) None None), IllegalStamp),
  (8, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.StrangeFrames.twoOperandStackSlots()V'' []), VoidStamp),
  (9, (InvokeNode 9 8 None None (Some 10) 13), VoidStamp),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ReturnNode (Some 12) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.StrangeFrames.twoOperandStackSlots()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.JTTTest$DummyTestClass'' None 4), ObjectStamp ''org.graalvm.compiler.jtt.JTTTest$DummyTestClass'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (NewInstanceNode 4 ''org.graalvm.compiler.jtt.JTTTest$DummyTestClass'' None 7), ObjectStamp ''org.graalvm.compiler.jtt.JTTTest$DummyTestClass'' True True False),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_StrangeFrames_test ''org.graalvm.compiler.jtt.micro.StrangeFrames.test(I)Z'' [(new_int 32 (0))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/nodes/test/SubCanonicalizationTest;.SubCanonicalizationTest_snippet0*)
definition unit_SubCanonicalizationTest_snippet0 :: IRGraph where
  "unit_SubCanonicalizationTest_snippet0 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (OrNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (XorNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (AndNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_SubCanonicalizationTest_snippet0  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_SubCanonicalizationTest_snippet0  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_SubCanonicalizationTest_snippet0  [(new_int 32 (-65536)), (new_int 32 (-1))] (new_int 32 (-65536))"

value "static_test unit_SubCanonicalizationTest_snippet0  [(new_int 32 (-65536)), (new_int 32 (65535))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/nodes/test/SubCanonicalizationTest;.SubCanonicalizationTest_snippet1*)
definition unit_SubCanonicalizationTest_snippet1 :: IRGraph where
  "unit_SubCanonicalizationTest_snippet1 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (OrNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (XorNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (6, (AndNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_SubCanonicalizationTest_snippet1  [(IntVal 64 (0)), (IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_SubCanonicalizationTest_snippet1  [(IntVal 64 (0)), (IntVal 64 (-1))] (IntVal 64 (0))"

value "static_test unit_SubCanonicalizationTest_snippet1  [(IntVal 64 (-4294967296)), (IntVal 64 (-1))] (IntVal 64 (-4294967296))"

value "static_test unit_SubCanonicalizationTest_snippet1  [(IntVal 64 (-4294967296)), (IntVal 64 (68719476735))] (IntVal 64 (64424509440))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$booleanGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (-65536))), IntegerStamp 32 (-65536) (-65536)),
  (3, (ConstantNode (new_int 1 (0))), IntegerStamp 1 (0) (0)),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$booleanGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$booleanGetter::field'' None 12), IntegerStamp 32 (0) (1)),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (IntegerEqualsNode 7 4), VoidStamp),
  (10, (BeginNode 14), VoidStamp),
  (11, (BeginNode 13), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ReturnNode (Some 8) None), VoidStamp),
  (14, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$byteGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__10 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__10 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (65535))), IntegerStamp 32 (65535) (65535)),
  (3, (ConstantNode (new_int 8 (-1))), IntegerStamp 8 (-1) (-1)),
  (4, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$byteGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$byteGetter::field'' None 11), IntegerStamp 32 (-128) (127)),
  (8, (IntegerEqualsNode 7 4), VoidStamp),
  (9, (BeginNode 15), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (15, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__10  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$shortGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__11 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__11 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (65535))), IntegerStamp 32 (65535) (65535)),
  (3, (ConstantNode (new_int 16 (-1))), IntegerStamp 16 (-1) (-1)),
  (4, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$shortGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$shortGetter::field'' None 11), IntegerStamp 32 (-32768) (32767)),
  (8, (IntegerEqualsNode 7 4), VoidStamp),
  (9, (BeginNode 15), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (15, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__11  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$charGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__12 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__12 = irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (65535))), IntegerStamp 32 (65535) (65535)),
  (3, (ConstantNode (new_int 16 (-1))), IntegerStamp 16 (-1) (-1)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$charGetter::field'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (LoadFieldNode 6 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$charGetter::field'' None 10), IntegerStamp 32 (0) (65535)),
  (7, (IntegerEqualsNode 6 2), VoidStamp),
  (8, (BeginNode 14), VoidStamp),
  (9, (BeginNode 12), VoidStamp),
  (10, (IfNode 7 9 8), VoidStamp),
  (11, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (12, (ReturnNode (Some 11) None), VoidStamp),
  (13, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (14, (ReturnNode (Some 13) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__12  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$booleanGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__13 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__13 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (16909060))), IntegerStamp 32 (16909060) (16909060)),
  (3, (ConstantNode (new_int 1 (0))), IntegerStamp 1 (0) (0)),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$booleanGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$booleanGetter::field'' None 12), IntegerStamp 32 (0) (1)),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (IntegerEqualsNode 7 4), VoidStamp),
  (10, (BeginNode 14), VoidStamp),
  (11, (BeginNode 13), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ReturnNode (Some 8) None), VoidStamp),
  (14, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__13  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$byteGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__14 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__14 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (16909060))), IntegerStamp 32 (16909060) (16909060)),
  (3, (ConstantNode (new_int 8 (4))), IntegerStamp 8 (4) (4)),
  (4, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$byteGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$byteGetter::field'' None 11), IntegerStamp 32 (-128) (127)),
  (8, (IntegerEqualsNode 7 4), VoidStamp),
  (9, (BeginNode 15), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (15, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__14  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$shortGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__15 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__15 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (16909060))), IntegerStamp 32 (16909060) (16909060)),
  (3, (ConstantNode (new_int 16 (772))), IntegerStamp 16 (772) (772)),
  (4, (ConstantNode (new_int 32 (772))), IntegerStamp 32 (772) (772)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$shortGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$shortGetter::field'' None 11), IntegerStamp 32 (-32768) (32767)),
  (8, (IntegerEqualsNode 7 4), VoidStamp),
  (9, (BeginNode 15), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (15, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__15  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$charGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__16 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__16 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (16909060))), IntegerStamp 32 (16909060) (16909060)),
  (3, (ConstantNode (new_int 16 (772))), IntegerStamp 16 (772) (772)),
  (4, (ConstantNode (new_int 32 (772))), IntegerStamp 32 (772) (772)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$charGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$charGetter::field'' None 11), IntegerStamp 32 (0) (65535)),
  (8, (IntegerEqualsNode 7 4), VoidStamp),
  (9, (BeginNode 15), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (15, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__16  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$byteGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__2 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__2 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (-65536))), IntegerStamp 32 (-65536) (-65536)),
  (3, (ConstantNode (new_int 8 (0))), IntegerStamp 8 (0) (0)),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$byteGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$byteGetter::field'' None 11), IntegerStamp 32 (-128) (127)),
  (8, (IntegerEqualsNode 7 4), VoidStamp),
  (9, (BeginNode 14), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__2  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$shortGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__3 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__3 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (-65536))), IntegerStamp 32 (-65536) (-65536)),
  (3, (ConstantNode (new_int 16 (0))), IntegerStamp 16 (0) (0)),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$shortGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$shortGetter::field'' None 11), IntegerStamp 32 (-32768) (32767)),
  (8, (IntegerEqualsNode 7 4), VoidStamp),
  (9, (BeginNode 14), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__3  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$charGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__4 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__4 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (-65536))), IntegerStamp 32 (-65536) (-65536)),
  (3, (ConstantNode (new_int 16 (0))), IntegerStamp 16 (0) (0)),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$charGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$charGetter::field'' None 11), IntegerStamp 32 (0) (65535)),
  (8, (IntegerEqualsNode 7 4), VoidStamp),
  (9, (BeginNode 14), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__4  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$booleanGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__5 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__5 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (-65535))), IntegerStamp 32 (-65535) (-65535)),
  (3, (ConstantNode (new_int 1 (1))), IntegerStamp 1 (-1) (-1)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$booleanGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$booleanGetter::field'' None 12), IntegerStamp 32 (0) (1)),
  (8, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (9, (IntegerEqualsNode 7 8), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ReturnNode (Some 4) None), VoidStamp),
  (14, (ReturnNode (Some 8) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__5  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$byteGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__6 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__6 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (-65535))), IntegerStamp 32 (-65535) (-65535)),
  (3, (ConstantNode (new_int 8 (1))), IntegerStamp 8 (1) (1)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$byteGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$byteGetter::field'' None 11), IntegerStamp 32 (-128) (127)),
  (8, (IntegerEqualsNode 7 4), VoidStamp),
  (9, (BeginNode 14), VoidStamp),
  (10, (BeginNode 12), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ReturnNode (Some 4) None), VoidStamp),
  (13, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (14, (ReturnNode (Some 13) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__6  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$shortGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__7 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__7 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (-65535))), IntegerStamp 32 (-65535) (-65535)),
  (3, (ConstantNode (new_int 16 (1))), IntegerStamp 16 (1) (1)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$shortGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$shortGetter::field'' None 11), IntegerStamp 32 (-32768) (32767)),
  (8, (IntegerEqualsNode 7 4), VoidStamp),
  (9, (BeginNode 14), VoidStamp),
  (10, (BeginNode 12), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ReturnNode (Some 4) None), VoidStamp),
  (13, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (14, (ReturnNode (Some 13) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__7  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$charGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__8 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__8 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (-65535))), IntegerStamp 32 (-65535) (-65535)),
  (3, (ConstantNode (new_int 16 (1))), IntegerStamp 16 (1) (1)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$charGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$charGetter::field'' None 11), IntegerStamp 32 (0) (65535)),
  (8, (IntegerEqualsNode 7 4), VoidStamp),
  (9, (BeginNode 14), VoidStamp),
  (10, (BeginNode 12), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ReturnNode (Some 4) None), VoidStamp),
  (13, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (14, (ReturnNode (Some 13) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__8  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordFieldStoreTest$booleanGetter;.SubWordFieldStoreTest_snippet*)
definition unit_SubWordFieldStoreTest_snippet__9 :: IRGraph where
  "unit_SubWordFieldStoreTest_snippet__9 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (65535))), IntegerStamp 32 (65535) (65535)),
  (3, (ConstantNode (new_int 1 (1))), IntegerStamp 1 (-1) (-1)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$booleanGetter::field'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.SubWordFieldStoreTest$booleanGetter::field'' None 12), IntegerStamp 32 (0) (1)),
  (8, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (9, (IntegerEqualsNode 7 8), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ReturnNode (Some 4) None), VoidStamp),
  (14, (ReturnNode (Some 8) None), VoidStamp)
  ]"
value "static_test unit_SubWordFieldStoreTest_snippet__9  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordInputTest2$byteGetter;.SubWordInputTest2_wrapper*)
definition unit_SubWordInputTest2_wrapper :: IRGraph where
  "unit_SubWordInputTest2_wrapper = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (ConditionalNode 5 4 6), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_SubWordInputTest2_wrapper  [(new_int 32 (-65536))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper  [(new_int 32 (-65536))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper  [(new_int 32 (-65535))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper  [(new_int 32 (-65535))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper  [(new_int 32 (65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest2_wrapper  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordInputTest2$shortGetter;.SubWordInputTest2_wrapper*)
definition unit_SubWordInputTest2_wrapper__2 :: IRGraph where
  "unit_SubWordInputTest2_wrapper__2 = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (ConditionalNode 5 4 6), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_SubWordInputTest2_wrapper__2  [(new_int 32 (-65536))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper__2  [(new_int 32 (-65536))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper__2  [(new_int 32 (-65535))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper__2  [(new_int 32 (-65535))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper__2  [(new_int 32 (65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest2_wrapper__2  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordInputTest2$charGetter;.SubWordInputTest2_wrapper*)
definition unit_SubWordInputTest2_wrapper__3 :: IRGraph where
  "unit_SubWordInputTest2_wrapper__3 = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (ConditionalNode 5 4 6), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_SubWordInputTest2_wrapper__3  [(new_int 32 (-65536))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper__3  [(new_int 32 (-65536))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper__3  [(new_int 32 (-65535))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper__3  [(new_int 32 (-65535))] (new_int 32 (0))"

value "static_test unit_SubWordInputTest2_wrapper__3  [(new_int 32 (65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest2_wrapper__3  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordInputTest$booleanGetter;.SubWordInputTest_wrapper*)
definition unit_SubWordInputTest_wrapper :: IRGraph where
  "unit_SubWordInputTest_wrapper = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (NarrowNode 32 1 1), IntegerStamp 1 (-1) (0)),
  (5, (ZeroExtendNode 1 32 4), IntegerStamp 32 (0) (1)),
  (6, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (AndNode 1 6), IntegerStamp 32 (0) (1)),
  (8, (IntegerEqualsNode 5 7), VoidStamp),
  (9, (BeginNode 14), VoidStamp),
  (10, (BeginNode 12), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ReturnNode (Some 6) None), VoidStamp),
  (13, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (14, (ReturnNode (Some 13) None), VoidStamp)
  ]"
value "static_test unit_SubWordInputTest_wrapper  [(new_int 32 (-65536))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper  [(new_int 32 (-65536))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper  [(new_int 32 (-65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper  [(new_int 32 (-65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper  [(new_int 32 (65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordInputTest$byteGetter;.SubWordInputTest_wrapper*)
definition unit_SubWordInputTest_wrapper__2 :: IRGraph where
  "unit_SubWordInputTest_wrapper__2 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (5, (SignExtendNode 8 32 4), IntegerStamp 32 (-128) (127)),
  (6, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_SubWordInputTest_wrapper__2  [(new_int 32 (-65536))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__2  [(new_int 32 (-65536))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__2  [(new_int 32 (-65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__2  [(new_int 32 (-65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__2  [(new_int 32 (65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__2  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordInputTest$shortGetter;.SubWordInputTest_wrapper*)
definition unit_SubWordInputTest_wrapper__3 :: IRGraph where
  "unit_SubWordInputTest_wrapper__3 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (5, (SignExtendNode 16 32 4), IntegerStamp 32 (-32768) (32767)),
  (6, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_SubWordInputTest_wrapper__3  [(new_int 32 (-65536))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__3  [(new_int 32 (-65536))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__3  [(new_int 32 (-65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__3  [(new_int 32 (-65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__3  [(new_int 32 (65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__3  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/SubWordInputTest$charGetter;.SubWordInputTest_wrapper*)
definition unit_SubWordInputTest_wrapper__4 :: IRGraph where
  "unit_SubWordInputTest_wrapper__4 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (5, (ZeroExtendNode 16 32 4), IntegerStamp 32 (0) (65535)),
  (6, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_SubWordInputTest_wrapper__4  [(new_int 32 (-65536))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__4  [(new_int 32 (-65536))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__4  [(new_int 32 (-65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__4  [(new_int 32 (-65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__4  [(new_int 32 (65535))] (new_int 32 (1))"

value "static_test unit_SubWordInputTest_wrapper__4  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testAlwaysFalse1*)
definition unit_TrichotomyTest_testAlwaysFalse1 :: Program where
  "unit_TrichotomyTest_testAlwaysFalse1 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse1(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerLessThanNode 1 2), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
  (7, (BeginNode 14), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (IntegerLessThanNode 2 1), VoidStamp),
  (12, (BeginNode 21), VoidStamp),
  (13, (BeginNode 18), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 27), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [9, 15, 20] 17), IntegerStamp 32 (-1) (2)),
  (20, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 15), VoidStamp),
  (25, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (26, (ConditionalNode 24 9 25), IntegerStamp 32 (0) (1)),
  (27, (ReturnNode (Some 26) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compareAlwaysFalse1(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 2 1), VoidStamp),
  (11, (BeginNode 20), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [8, 14, 19] 16), IntegerStamp 32 (-1) (2)),
  (19, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testAlwaysFalse1 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse1(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testAlwaysFalse1 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse1(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testAlwaysFalse1 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse1(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testAlwaysFalse10*)
definition unit_TrichotomyTest_testAlwaysFalse10 :: Program where
  "unit_TrichotomyTest_testAlwaysFalse10 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse10(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerEqualsNode 1 2), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
  (7, (BeginNode 14), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (IntegerLessThanNode 1 2), VoidStamp),
  (12, (BeginNode 21), VoidStamp),
  (13, (BeginNode 18), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 27), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [9, 15, 20] 17), IntegerStamp 32 (-1) (2)),
  (20, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 15), VoidStamp),
  (25, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (26, (ConditionalNode 24 9 25), IntegerStamp 32 (0) (1)),
  (27, (ReturnNode (Some 26) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compareAlwaysFalse4(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 1 2), VoidStamp),
  (11, (BeginNode 20), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [8, 14, 19] 16), IntegerStamp 32 (-1) (2)),
  (19, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testAlwaysFalse10 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse10(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testAlwaysFalse10 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse10(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testAlwaysFalse10 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse10(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/TrichotomyTest;.TrichotomyTest_testAlwaysFalse11*)
definition unit_TrichotomyTest_testAlwaysFalse11 :: Program where
  "unit_TrichotomyTest_testAlwaysFalse11 = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse11(II)Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (IntegerEqualsNode 1 2), VoidStamp),
  (6, (BeginNode 16), VoidStamp),
  (7, (BeginNode 14), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (IntegerLessThanNode 1 2), VoidStamp),
  (12, (BeginNode 21), VoidStamp),
  (13, (BeginNode 18), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18, 21] (Some 23) 27), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [9, 15, 20] 17), IntegerStamp 32 (-1) (2)),
  (20, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (21, (EndNode), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerLessThanNode 19 15), VoidStamp),
  (25, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (26, (ConditionalNode 24 25 9), IntegerStamp 32 (0) (1)),
  (27, (ReturnNode (Some 26) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.compareAlwaysFalse4(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerEqualsNode 1 2), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerLessThanNode 1 2), VoidStamp),
  (11, (BeginNode 20), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode [15, 17, 20] (Some 21) 22), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18 [8, 14, 19] 16), IntegerStamp 32 (-1) (2)),
  (19, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (20, (EndNode), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 18) None), VoidStamp)
  ]
  )"
value "program_test unit_TrichotomyTest_testAlwaysFalse11 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse11(II)Z'' [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testAlwaysFalse11 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse11(II)Z'' [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "program_test unit_TrichotomyTest_testAlwaysFalse11 ''org.graalvm.compiler.jtt.optimize.TrichotomyTest.testAlwaysFalse11(II)Z'' [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"

end
