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


(* Lorg/graalvm/compiler/jtt/except/BC_putfield;.BC_putfield_test*)
definition unit_BC_putfield_test :: Program where
  "unit_BC_putfield_test = Map.empty (
  ''org.graalvm.compiler.jtt.except.BC_putfield.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 10), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (ObjRef None)), ObjectStamp ''null'' False False True),
  (10, (LoadFieldNode 10 ''org.graalvm.compiler.jtt.except.BC_putfield::object'' None 13), ObjectStamp ''org.graalvm.compiler.jtt.except.BC_putfield$TestClass'' True False False),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 16), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), ObjectStamp ''org.graalvm.compiler.jtt.except.BC_putfield$TestClass'' True False False),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (StoreFieldNode 16 ''org.graalvm.compiler.jtt.except.BC_putfield$TestClass::field'' 1 (Some 17) (Some 14) 18), VoidStamp),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (LoadFieldNode 18 ''org.graalvm.compiler.jtt.except.BC_putfield$TestClass::field'' (Some 14) 19), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (ReturnNode (Some 18) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.except.BC_putfield.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.except.BC_putfield$TestClass'' None 4), ObjectStamp ''org.graalvm.compiler.jtt.except.BC_putfield$TestClass'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.except.BC_putfield::object'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.except.BC_putfield.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_BC_putfield_test ''org.graalvm.compiler.jtt.except.BC_putfield.test(I)I'' [(new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_putstatic;.BC_putstatic_test*)
definition unit_BC_putstatic_test :: IRGraph where
  "unit_BC_putstatic_test = irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (StoreFieldNode 3 ''org.graalvm.compiler.jtt.bytecode.BC_putstatic::field'' 1 (Some 4) None 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (LoadFieldNode 5 ''org.graalvm.compiler.jtt.bytecode.BC_putstatic::field'' None 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]"
value "static_test unit_BC_putstatic_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_putstatic_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_BC_putstatic_test  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_putstatic_test  [(new_int 32 (3))] (new_int 32 (3))"

value "static_test unit_BC_putstatic_test  [(new_int 32 (-4))] (new_int 32 (-4))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_wide01;.BC_wide01_test*)
definition unit_BC_wide01_test :: IRGraph where
  "unit_BC_wide01_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (AddNode 4 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_BC_wide01_test  [(new_int 32 (0))] (new_int 32 (11))"

value "static_test unit_BC_wide01_test  [(new_int 32 (1))] (new_int 32 (12))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_wide02;.BC_wide02_test*)
definition unit_BC_wide02_test :: IRGraph where
  "unit_BC_wide02_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (9))), IntegerStamp 32 (9) (9)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (6, (AddNode 1 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (AddNode 6 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_BC_wide02_test  [(new_int 32 (0))] (new_int 32 (11))"

value "static_test unit_BC_wide02_test  [(new_int 32 (1))] (new_int 32 (12))"


(* Lorg/graalvm/compiler/api/directives/test/BlackholeDirectiveTest;.BlackholeDirectiveTest_booleanSnippet*)
definition unit_BlackholeDirectiveTest_booleanSnippet :: IRGraph where
  "unit_BlackholeDirectiveTest_booleanSnippet = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (4, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (8, (ConditionalNode 5 6 7), IntegerStamp 32 (0) (1)),
  (9, (BeginNode 12), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 5 10 9), VoidStamp),
  (12, (ReturnNode (Some 7) None), VoidStamp),
  (13, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_BlackholeDirectiveTest_booleanSnippet  [(new_int 32 (5))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/api/directives/test/BlackholeDirectiveTest;.BlackholeDirectiveTest_intSnippet*)
definition unit_BlackholeDirectiveTest_intSnippet :: IRGraph where
  "unit_BlackholeDirectiveTest_intSnippet = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (42))), IntegerStamp 32 (42) (42)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_BlackholeDirectiveTest_intSnippet  [(new_int 32 (17))] (new_int 32 (42))"


(* Lorg/graalvm/compiler/jtt/optimize/BlockSkip01;.BlockSkip01_test*)
definition unit_BlockSkip01_test :: IRGraph where
  "unit_BlockSkip01_test = irgraph [
  (0, (StartNode (Some 2) 9), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (5, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (6, (IntegerLessThanNode 1 5), VoidStamp),
  (7, (BeginNode 11), VoidStamp),
  (8, (BeginNode 13), VoidStamp),
  (9, (IfNode 6 8 7), VoidStamp),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 22), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [4, 3] 12), IntegerStamp 32 (1) (2)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (AddNode 14 3), IntegerStamp 32 (2) (3)),
  (18, (IntegerEqualsNode 14 3), VoidStamp),
  (19, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (20, (ConditionalNode 18 3 19), IntegerStamp 32 (0) (1)),
  (22, (ReturnNode (Some 20) None), VoidStamp)
  ]"
value "static_test unit_BlockSkip01_test  [(new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_BlockSkip01_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_BlockSkip01_test  [(new_int 32 (2))] (new_int 32 (1))"

value "static_test unit_BlockSkip01_test  [(new_int 32 (3))] (new_int 32 (0))"

value "static_test unit_BlockSkip01_test  [(new_int 32 (4))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/Cmov01;.Cmov01_test*)
definition unit_Cmov01_test :: IRGraph where
  "unit_Cmov01_test = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerEqualsNode 1 2), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (11, (ConditionalNode 8 9 10), IntegerStamp 32 (0) (1)),
  (13, (EndNode), VoidStamp),
  (14, (MergeNode [13, 15] (Some 17) 18), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (ValuePhiNode 16 [11, 9] 14), IntegerStamp 32 (0) (1)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_Cmov01_test  [(new_int 32 (-1)), (new_int 32 (-1))] (new_int 32 (1))"

value "static_test unit_Cmov01_test  [(new_int 32 (1)), (new_int 32 (10))] (new_int 32 (1))"

value "static_test unit_Cmov01_test  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/core/test/CompilationWatchDogTest;.CompilationWatchDogTest_snippet*)
definition unit_CompilationWatchDogTest_snippet :: IRGraph where
  "unit_CompilationWatchDogTest_snippet = irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ReturnNode (Some 1) None), VoidStamp)
  ]"
value "static_test unit_CompilationWatchDogTest_snippet  [(new_int 32 (42))] (new_int 32 (42))"


(* Lorg/graalvm/compiler/core/test/ConditionalNodeTest;.ConditionalNodeTest_conditionalTest0*)
definition unit_ConditionalNodeTest_conditionalTest0 :: IRGraph where
  "unit_ConditionalNodeTest_conditionalTest0 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (StoreFieldNode 10 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink1'' 9 (Some 11) None 16), VoidStamp),
  (11, (FrameState [] None None None), IllegalStamp),
  (13, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink1'' 3 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18] (Some 20) 21), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [8, 13] 17), IntegerStamp 32 (-1) (6)),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink0'' 3 (Some 22) None 27), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (IntegerLessThanNode 19 13), VoidStamp),
  (25, (BeginNode 29), VoidStamp),
  (26, (BeginNode 31), VoidStamp),
  (27, (IfNode 24 26 25), VoidStamp),
  (29, (EndNode), VoidStamp),
  (30, (MergeNode [29, 31] (Some 34) 35), VoidStamp),
  (31, (EndNode), VoidStamp),
  (32, (ValuePhiNode 32 [19, 13] 30), IntegerStamp 32 (-1) (6)),
  (33, (FrameState [] None None None), IllegalStamp),
  (34, (FrameState [] (Some 33) None None), IllegalStamp),
  (35, (ReturnNode (Some 32) None), VoidStamp)
  ]"
value "static_test unit_ConditionalNodeTest_conditionalTest0  [(new_int 32 (0))] (new_int 32 (6))"

value "static_test unit_ConditionalNodeTest_conditionalTest0  [(new_int 32 (1))] (new_int 32 (6))"


(* Lorg/graalvm/compiler/core/test/ConditionalNodeTest;.ConditionalNodeTest_conditionalTest1*)
definition unit_ConditionalNodeTest_conditionalTest1 :: IRGraph where
  "unit_ConditionalNodeTest_conditionalTest1 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (StoreFieldNode 10 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink1'' 9 (Some 11) None 16), VoidStamp),
  (11, (FrameState [] None None None), IllegalStamp),
  (13, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink1'' 3 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18] (Some 20) 21), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [8, 13] 17), IntegerStamp 32 (-1) (6)),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink0'' 3 (Some 22) None 24), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (ReturnNode (Some 13) None), VoidStamp)
  ]"
value "static_test unit_ConditionalNodeTest_conditionalTest1  [(new_int 32 (0))] (new_int 32 (6))"

value "static_test unit_ConditionalNodeTest_conditionalTest1  [(new_int 32 (1))] (new_int 32 (6))"


(* Lorg/graalvm/compiler/core/test/ConditionalNodeTest;.ConditionalNodeTest_conditionalTest2*)
definition unit_ConditionalNodeTest_conditionalTest2 :: IRGraph where
  "unit_ConditionalNodeTest_conditionalTest2 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (StoreFieldNode 10 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink1'' 9 (Some 11) None 16), VoidStamp),
  (11, (FrameState [] None None None), IllegalStamp),
  (13, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink1'' 3 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18] (Some 20) 21), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [8, 13] 17), IntegerStamp 32 (-1) (6)),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink0'' 3 (Some 22) None 27), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (IntegerEqualsNode 19 8), VoidStamp),
  (25, (BeginNode 31), VoidStamp),
  (26, (BeginNode 29), VoidStamp),
  (27, (IfNode 24 26 25), VoidStamp),
  (29, (EndNode), VoidStamp),
  (30, (MergeNode [29, 31] (Some 34) 35), VoidStamp),
  (31, (EndNode), VoidStamp),
  (32, (ValuePhiNode 32 [19, 8] 30), IntegerStamp 32 (-1) (6)),
  (33, (FrameState [] None None None), IllegalStamp),
  (34, (FrameState [] (Some 33) None None), IllegalStamp),
  (35, (ReturnNode (Some 32) None), VoidStamp)
  ]"
value "static_test unit_ConditionalNodeTest_conditionalTest2  [(new_int 32 (0))] (new_int 32 (-1))"

value "static_test unit_ConditionalNodeTest_conditionalTest2  [(new_int 32 (1))] (new_int 32 (-1))"


(* Lorg/graalvm/compiler/core/test/ConditionalNodeTest;.ConditionalNodeTest_conditionalTest3*)
definition unit_ConditionalNodeTest_conditionalTest3 :: IRGraph where
  "unit_ConditionalNodeTest_conditionalTest3 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (StoreFieldNode 10 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink1'' 9 (Some 11) None 16), VoidStamp),
  (11, (FrameState [] None None None), IllegalStamp),
  (13, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink1'' 3 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18] (Some 20) 21), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [8, 13] 17), IntegerStamp 32 (-1) (6)),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink0'' 3 (Some 22) None 24), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (ReturnNode (Some 8) None), VoidStamp)
  ]"
value "static_test unit_ConditionalNodeTest_conditionalTest3  [(new_int 32 (0))] (new_int 32 (-1))"

value "static_test unit_ConditionalNodeTest_conditionalTest3  [(new_int 32 (1))] (new_int 32 (-1))"


(* Lorg/graalvm/compiler/api/directives/test/ControlFlowAnchorDirectiveTest;.ControlFlowAnchorDirectiveTest_verifyFullUnrollSnippet*)
definition unit_ControlFlowAnchorDirectiveTest_verifyFullUnrollSnippet :: IRGraph where
  "unit_ControlFlowAnchorDirectiveTest_verifyFullUnrollSnippet = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 23] None (Some 9) 17), VoidStamp),
  (7, (ValuePhiNode 7 [1, 21] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 22] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (11, (IntegerLessThanNode 8 10), VoidStamp),
  (13, (LoopExitNode 6 (Some 15) 24), VoidStamp),
  (14, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 23), VoidStamp),
  (17, (IfNode 11 16 13), VoidStamp),
  (18, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (19, (MulNode 7 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (20, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (21, (AddNode 19 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (AddNode 8 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (LoopEndNode 6), VoidStamp),
  (24, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_ControlFlowAnchorDirectiveTest_verifyFullUnrollSnippet  [(new_int 32 (42))] (new_int 32 (10327))"


(* Lorg/graalvm/compiler/api/directives/test/ControlFlowAnchorDirectiveTest;.ControlFlowAnchorDirectiveTest_verifyMergeSnippet*)
definition unit_ControlFlowAnchorDirectiveTest_verifyMergeSnippet :: IRGraph where
  "unit_ControlFlowAnchorDirectiveTest_verifyMergeSnippet = irgraph [
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
  (11, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (12, (ReturnNode (Some 11) None), VoidStamp)
  ]"
value "static_test unit_ControlFlowAnchorDirectiveTest_verifyMergeSnippet  [(new_int 32 (42))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/ConvertCompare;.ConvertCompare_testChar42*)
definition unit_ConvertCompare_testChar42 :: IRGraph where
  "unit_ConvertCompare_testChar42 = irgraph [
  (0, (StartNode (Some 2) 10), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (5, (ConstantNode (new_int 32 (42))), IntegerStamp 32 (42) (42)),
  (6, (IntegerEqualsNode 4 5), VoidStamp),
  (7, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (8, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (9, (ConditionalNode 6 7 8), IntegerStamp 32 (0) (1)),
  (10, (ReturnNode (Some 9) None), VoidStamp)
  ]"
value "static_test unit_ConvertCompare_testChar42  [(new_int 32 (42))] (new_int 32 (1))"

value "static_test unit_ConvertCompare_testChar42  [(new_int 32 (65535))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/ConvertCompare;.ConvertCompare_testCharMax*)
definition unit_ConvertCompare_testCharMax :: IRGraph where
  "unit_ConvertCompare_testCharMax = irgraph [
  (0, (StartNode (Some 2) 10), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (5, (ConstantNode (new_int 32 (65535))), IntegerStamp 32 (65535) (65535)),
  (6, (IntegerEqualsNode 4 5), VoidStamp),
  (7, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (8, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (9, (ConditionalNode 6 7 8), IntegerStamp 32 (0) (1)),
  (10, (ReturnNode (Some 9) None), VoidStamp)
  ]"
value "static_test unit_ConvertCompare_testCharMax  [(new_int 32 (42))] (new_int 32 (0))"

value "static_test unit_ConvertCompare_testCharMax  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/optimize/DeadCode01;.DeadCode01_test*)
definition unit_DeadCode01_test :: IRGraph where
  "unit_DeadCode01_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (4, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 31), VoidStamp),
  (7, (BeginNode 21), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (AddNode 1 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (12, (AddNode 1 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (ConstantNode (new_int 32 (20))), IntegerStamp 32 (20) (20)),
  (16, (AddNode 1 15), IntegerStamp 32 (-2147483648) (2147483647)),
  (17, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (18, (IntegerLessThanNode 14 17), VoidStamp),
  (19, (BeginNode 28), VoidStamp),
  (20, (BeginNode 40), VoidStamp),
  (21, (IfNode 18 20 19), VoidStamp),
  (22, (AddNode 14 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (AddNode 16 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (24, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (25, (IntegerLessThanNode 22 24), VoidStamp),
  (26, (BeginNode 33), VoidStamp),
  (27, (BeginNode 37), VoidStamp),
  (28, (IfNode 25 27 26), VoidStamp),
  (29, (AddNode 22 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (30, (AddNode 23 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (31, (EndNode), VoidStamp),
  (32, (MergeNode [31, 33, 37, 40] (Some 41) 42), VoidStamp),
  (33, (EndNode), VoidStamp),
  (34, (ValuePhiNode 34 [10, 29, 35, 38] 32), IntegerStamp 32 (-2147483648) (2147483647)),
  (35, (AddNode 22 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (36, (AddNode 23 15), IntegerStamp 32 (-2147483648) (2147483647)),
  (37, (EndNode), VoidStamp),
  (38, (AddNode 14 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (39, (AddNode 16 15), IntegerStamp 32 (-2147483648) (2147483647)),
  (40, (EndNode), VoidStamp),
  (41, (FrameState [] None None None), IllegalStamp),
  (42, (ReturnNode (Some 34) None), VoidStamp)
  ]"
value "static_test unit_DeadCode01_test  [(new_int 32 (0))] (new_int 32 (4))"

value "static_test unit_DeadCode01_test  [(new_int 32 (1))] (new_int 32 (5))"

value "static_test unit_DeadCode01_test  [(new_int 32 (2))] (new_int 32 (6))"

value "static_test unit_DeadCode01_test  [(new_int 32 (3))] (new_int 32 (4))"

value "static_test unit_DeadCode01_test  [(new_int 32 (4))] (new_int 32 (5))"

value "static_test unit_DeadCode01_test  [(new_int 32 (6))] (new_int 32 (7))"


(* Lorg/graalvm/compiler/jtt/optimize/DeadCode02;.DeadCode02_test*)
definition unit_DeadCode02_test :: IRGraph where
  "unit_DeadCode02_test = irgraph [
  (0, (StartNode (Some 1) 15), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (AddNode 2 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (15, (ReturnNode (Some 9) None), VoidStamp)
  ]"
value "static_test unit_DeadCode02_test  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/DontReuseArgumentSpaceTest;.DontReuseArgumentSpaceTest_callTwice*)
definition unit_DontReuseArgumentSpaceTest_callTwice :: Program where
  "unit_DontReuseArgumentSpaceTest_callTwice = Map.empty (
  ''org.graalvm.compiler.core.test.DontReuseArgumentSpaceTest.callTwice(IIIIIIIIII)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 11) 13), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (ParameterNode 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (4, (ParameterNode 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ParameterNode 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (ParameterNode 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (ParameterNode 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ParameterNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (ParameterNode 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (ParameterNode 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (MethodCallTargetNode ''org.graalvm.compiler.core.test.DontReuseArgumentSpaceTest.killArguments(IIIIIIIIII)I'' [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]), VoidStamp),
  (13, (InvokeNode 13 12 None None (Some 14) 16), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (MethodCallTargetNode ''org.graalvm.compiler.core.test.DontReuseArgumentSpaceTest.killArguments(IIIIIIIIII)I'' [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]), VoidStamp),
  (16, (InvokeNode 16 15 None None (Some 17) 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ],
  ''org.graalvm.compiler.core.test.DontReuseArgumentSpaceTest.killArguments(IIIIIIIIII)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 11) 21), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (ParameterNode 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (4, (ParameterNode 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ParameterNode 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (ParameterNode 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (ParameterNode 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ParameterNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (ParameterNode 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (ParameterNode 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (AddNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (13, (AddNode 3 12), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (AddNode 4 13), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (AddNode 5 14), IntegerStamp 32 (-2147483648) (2147483647)),
  (16, (AddNode 6 15), IntegerStamp 32 (-2147483648) (2147483647)),
  (17, (AddNode 7 16), IntegerStamp 32 (-2147483648) (2147483647)),
  (18, (AddNode 8 17), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (AddNode 9 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (20, (AddNode 10 19), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (ReturnNode (Some 20) None), VoidStamp)
  ]
  )"
value "program_test unit_DontReuseArgumentSpaceTest_callTwice ''org.graalvm.compiler.core.test.DontReuseArgumentSpaceTest.callTwice(IIIIIIIIII)I'' [(new_int 32 (1)), (new_int 32 (2)), (new_int 32 (3)), (new_int 32 (4)), (new_int 32 (5)), (new_int 32 (6)), (new_int 32 (7)), (new_int 32 (8)), (new_int 32 (9)), (new_int 32 (10))] (new_int 32 (55))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$boolean_CALL_DIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run :: IRGraph where
  "unit_DynamicConstantTest_run = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$char_CALL_DIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__10 :: IRGraph where
  "unit_DynamicConstantTest_run__10 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (42))), IntegerStamp 32 (42) (42)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__10  [] (new_int 32 (42))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$char_CALL_INDIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__11 :: IRGraph where
  "unit_DynamicConstantTest_run__11 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (42))), IntegerStamp 32 (42) (42)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__11  [] (new_int 32 (42))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$char_CALL_INDIRECT_WITH_ARGS_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__12 :: IRGraph where
  "unit_DynamicConstantTest_run__12 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__12  [] (new_int 32 (0))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$int_CALL_DIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__13 :: IRGraph where
  "unit_DynamicConstantTest_run__13 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (2147483647))), IntegerStamp 32 (2147483647) (2147483647)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__13  [] (new_int 32 (2147483647))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$int_CALL_INDIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__14 :: IRGraph where
  "unit_DynamicConstantTest_run__14 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (2147483647))), IntegerStamp 32 (2147483647) (2147483647)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__14  [] (new_int 32 (2147483647))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$int_CALL_INDIRECT_WITH_ARGS_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__15 :: IRGraph where
  "unit_DynamicConstantTest_run__15 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__15  [] (new_int 32 (0))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$long_CALL_DIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__16 :: IRGraph where
  "unit_DynamicConstantTest_run__16 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (9223372036854775807))), IntegerStamp 64 (9223372036854775807) (9223372036854775807)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__16  [] (IntVal 64 (9223372036854775807))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$long_CALL_INDIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__17 :: IRGraph where
  "unit_DynamicConstantTest_run__17 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (9223372036854775807))), IntegerStamp 64 (9223372036854775807) (9223372036854775807)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__17  [] (IntVal 64 (9223372036854775807))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$long_CALL_INDIRECT_WITH_ARGS_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__18 :: IRGraph where
  "unit_DynamicConstantTest_run__18 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (0))), IntegerStamp 64 (0) (0)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__18  [] (IntVal 64 (0))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$boolean_CALL_INDIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__2 :: IRGraph where
  "unit_DynamicConstantTest_run__2 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__2  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$boolean_CALL_INDIRECT_WITH_ARGS_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__3 :: IRGraph where
  "unit_DynamicConstantTest_run__3 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__3  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$byte_CALL_DIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__4 :: IRGraph where
  "unit_DynamicConstantTest_run__4 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (127))), IntegerStamp 32 (127) (127)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__4  [] (new_int 32 (127))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$byte_CALL_INDIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__5 :: IRGraph where
  "unit_DynamicConstantTest_run__5 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (127))), IntegerStamp 32 (127) (127)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__5  [] (new_int 32 (127))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$byte_CALL_INDIRECT_WITH_ARGS_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__6 :: IRGraph where
  "unit_DynamicConstantTest_run__6 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__6  [] (new_int 32 (0))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$short_CALL_DIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__7 :: IRGraph where
  "unit_DynamicConstantTest_run__7 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (32767))), IntegerStamp 32 (32767) (32767)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__7  [] (new_int 32 (32767))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$short_CALL_INDIRECT_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__8 :: IRGraph where
  "unit_DynamicConstantTest_run__8 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (32767))), IntegerStamp 32 (32767) (32767)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__8  [] (new_int 32 (32767))"


(* Lorg/graalvm/compiler/core/test/DynamicConstantTest$short_CALL_INDIRECT_WITH_ARGS_BSM;.DynamicConstantTest_run*)
definition unit_DynamicConstantTest_run__9 :: IRGraph where
  "unit_DynamicConstantTest_run__9 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_DynamicConstantTest_run__9  [] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/micro/Fibonacci;.Fibonacci_test*)
definition unit_Fibonacci_test :: IRGraph where
  "unit_Fibonacci_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (BeginNode 9), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ReturnNode (Some 3) None), VoidStamp),
  (11, (EndNode), VoidStamp),
  (12, (LoopBeginNode [11, 26] None (Some 16) 23), VoidStamp),
  (13, (ValuePhiNode 13 [3, 14] 12), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (ValuePhiNode 14 [4, 24] 12), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (ValuePhiNode 15 [4, 25] 12), IntegerStamp 32 (-2147483648) (2147483647)),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (IntegerLessThanNode 15 1), VoidStamp),
  (19, (LoopExitNode 12 (Some 21) 27), VoidStamp),
  (20, (RefNode 14), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (BeginNode 26), VoidStamp),
  (23, (IfNode 17 22 19), VoidStamp),
  (24, (AddNode 13 14), IntegerStamp 32 (-2147483648) (2147483647)),
  (25, (AddNode 15 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (LoopEndNode 12), VoidStamp),
  (27, (ReturnNode (Some 20) None), VoidStamp)
  ]"
value "static_test unit_Fibonacci_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Fibonacci_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_Fibonacci_test  [(new_int 32 (2))] (new_int 32 (1))"

value "static_test unit_Fibonacci_test  [(new_int 32 (3))] (new_int 32 (2))"

value "static_test unit_Fibonacci_test  [(new_int 32 (4))] (new_int 32 (3))"

value "static_test unit_Fibonacci_test  [(new_int 32 (5))] (new_int 32 (5))"

value "static_test unit_Fibonacci_test  [(new_int 32 (6))] (new_int 32 (8))"

value "static_test unit_Fibonacci_test  [(new_int 32 (7))] (new_int 32 (13))"


(* Lorg/graalvm/compiler/jtt/except/Finally01;.Finally01_test*)
definition unit_Finally01_test :: IRGraph where
  "unit_Finally01_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_Finally01_test  [(new_int 32 (0))] (new_int 32 (-1))"

value "static_test unit_Finally01_test  [(new_int 32 (1))] (new_int 32 (-1))"


(* Lorg/graalvm/compiler/jtt/except/Finally02;.Finally02_test*)
definition unit_Finally02_test :: IRGraph where
  "unit_Finally02_test = irgraph [
  (0, (StartNode (Some 1) 8), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ConstantNode (new_int 32 (-3))), IntegerStamp 32 (-3) (-3)),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_Finally02_test  [] (new_int 32 (-1))"


(* Lorg/graalvm/compiler/core/test/FloatingDivTest;.FloatingDivTest_snippet*)
definition unit_FloatingDivTest_snippet :: IRGraph where
  "unit_FloatingDivTest_snippet = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 59] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [3, 46] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 58] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 8 1), VoidStamp),
  (12, (LoopExitNode 6 (Some 14) 60), VoidStamp),
  (13, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 10 15 12), VoidStamp),
  (17, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (18, (SignedRemNode 18 8 17 None None 22), IntegerStamp 32 (-4) (4)),
  (19, (IntegerEqualsNode 18 3), VoidStamp),
  (20, (BeginNode 26), VoidStamp),
  (21, (BeginNode 24), VoidStamp),
  (22, (IfNode 19 21 20), VoidStamp),
  (23, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (24, (SignedRemNode 24 8 23 None None 31), IntegerStamp 32 (-2) (2)),
  (25, (IntegerEqualsNode 24 3), VoidStamp),
  (26, (EndNode), VoidStamp),
  (27, (MergeNode [26, 28] (Some 35) 36), VoidStamp),
  (28, (EndNode), VoidStamp),
  (29, (BeginNode 43), VoidStamp),
  (30, (BeginNode 28), VoidStamp),
  (31, (IfNode 25 29 30), VoidStamp),
  (32, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (33, (AddNode 7 32), IntegerStamp 32 (-2147483648) (2147483647)),
  (35, (FrameState [] None None None), IllegalStamp),
  (36, (SignedRemNode 36 8 17 None None 40), IntegerStamp 32 (-4) (4)),
  (37, (IntegerEqualsNode 36 3), VoidStamp),
  (38, (BeginNode 47), VoidStamp),
  (39, (BeginNode 45), VoidStamp),
  (40, (IfNode 37 39 38), VoidStamp),
  (41, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (42, (AddNode 7 41), IntegerStamp 32 (-2147483648) (2147483647)),
  (43, (EndNode), VoidStamp),
  (44, (MergeNode [43, 45, 53, 56] (Some 57) 59), VoidStamp),
  (45, (EndNode), VoidStamp),
  (46, (ValuePhiNode 46 [33, 42, 52, 55] 44), IntegerStamp 32 (-2147483648) (2147483647)),
  (47, (SignedRemNode 47 8 23 None None 51), IntegerStamp 32 (-2) (2)),
  (48, (IntegerEqualsNode 47 3), VoidStamp),
  (49, (BeginNode 56), VoidStamp),
  (50, (BeginNode 53), VoidStamp),
  (51, (IfNode 48 50 49), VoidStamp),
  (52, (AddNode 7 23), IntegerStamp 32 (-2147483648) (2147483647)),
  (53, (EndNode), VoidStamp),
  (54, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (55, (AddNode 7 54), IntegerStamp 32 (-2147483648) (2147483647)),
  (56, (EndNode), VoidStamp),
  (57, (FrameState [] None None None), IllegalStamp),
  (58, (AddNode 8 32), IntegerStamp 32 (-2147483648) (2147483647)),
  (59, (LoopEndNode 6), VoidStamp),
  (60, (ReturnNode (Some 13) None), VoidStamp)
  ]"
value "static_test unit_FloatingDivTest_snippet  [(new_int 32 (100))] (new_int 32 (326))"

end
