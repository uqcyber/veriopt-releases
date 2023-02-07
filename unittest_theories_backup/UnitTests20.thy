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


(* Lorg/graalvm/compiler/jtt/optimize/Narrow_short02;.Narrow_short02_test*)
definition unit_Narrow_short02_test :: Program where
  "unit_Narrow_short02_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.Narrow_short02.test(S)S'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (LoadFieldNode 3 ''org.graalvm.compiler.jtt.optimize.Narrow_short02::val'' None 6), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Narrow_short02$Short'' True False False),
  (4, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (5, (SignExtendNode 16 32 4), IntegerStamp 32 (-32768) (32767)),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.jtt.optimize.Narrow_short02$Short::foo'' 5 (Some 7) (Some 3) 8), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (LoadFieldNode 8 ''org.graalvm.compiler.jtt.optimize.Narrow_short02::val'' None 9), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Narrow_short02$Short'' True False False),
  (9, (LoadFieldNode 9 ''org.graalvm.compiler.jtt.optimize.Narrow_short02$Short::foo'' (Some 8) 10), IntegerStamp 32 (-32768) (32767)),
  (10, (ReturnNode (Some 9) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Narrow_short02.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.optimize.Narrow_short02$Short'' None 4), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Narrow_short02$Short'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.optimize.Narrow_short02::val'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Narrow_short02.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_Narrow_short02_test ''org.graalvm.compiler.jtt.optimize.Narrow_short02.test(S)S'' [(new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_Narrow_short02_test ''org.graalvm.compiler.jtt.optimize.Narrow_short02.test(S)S'' [(new_int 32 (1))] (new_int 32 (1))"

value "program_test unit_Narrow_short02_test ''org.graalvm.compiler.jtt.optimize.Narrow_short02.test(S)S'' [(new_int 32 (-1))] (new_int 32 (-1))"

value "program_test unit_Narrow_short02_test ''org.graalvm.compiler.jtt.optimize.Narrow_short02.test(S)S'' [(new_int 32 (23110))] (new_int 32 (23110))"


(* Lorg/graalvm/compiler/replacements/test/NewInstanceTest;.NewInstanceTest_newBigObject*)
definition unit_NewInstanceTest_newBigObject :: Program where
  "unit_NewInstanceTest_newBigObject = Map.empty (
  ''org.graalvm.compiler.replacements.test.NewInstanceTest.newBigObject()Lorg/graalvm/compiler/replacements/test/NewInstanceTest$BigObject;'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject'' None 4), ObjectStamp ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ReturnNode (Some 2) None), VoidStamp)
  ]
  )"
fun check_NewInstanceTest_newBigObject_189 :: "Value \<Rightarrow> FieldRefHeap \<Rightarrow> bool" where
  "check_NewInstanceTest_newBigObject_189 (ObjRef x) h = (True \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f01'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f02'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f03'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f04'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f05'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f06'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f07'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f08'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f09'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f10'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f12'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f13'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f14'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f15'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f16'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f17'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f18'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f19'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f20'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f21'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f22'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f23'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f24'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f25'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f26'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f27'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f28'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f29'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f30'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f31'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f32'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f33'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f34'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f35'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f36'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f37'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f38'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f39'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f40'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f41'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f42'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f43'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f44'' x h = (ObjRef None) \<and> h_load_field ''org.graalvm.compiler.replacements.test.NewInstanceTest$BigObject::f45'' x h = (ObjRef None))" |
  "check_NewInstanceTest_newBigObject_189 _ _ = False"
value "object_test unit_NewInstanceTest_newBigObject ''org.graalvm.compiler.replacements.test.NewInstanceTest.newBigObject()Lorg/graalvm/compiler/replacements/test/NewInstanceTest$BigObject;'' [] check_NewInstanceTest_newBigObject_189"


(* Lorg/graalvm/compiler/replacements/test/NewInstanceTest;.NewInstanceTest_newObject*)
definition unit_NewInstanceTest_newObject :: Program where
  "unit_NewInstanceTest_newObject = Map.empty (
  ''org.graalvm.compiler.replacements.test.NewInstanceTest.newObject()Ljava/lang/Object;'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''java.lang.Object'' None 3), ObjectStamp ''java.lang.Object'' True True False),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]
  )"
fun check_NewInstanceTest_newObject_75 :: "Value \<Rightarrow> FieldRefHeap \<Rightarrow> bool" where
  "check_NewInstanceTest_newObject_75 (ObjRef x) h = (True)" |
  "check_NewInstanceTest_newObject_75 _ _ = False"
value "object_test unit_NewInstanceTest_newObject ''org.graalvm.compiler.replacements.test.NewInstanceTest.newObject()Ljava/lang/Object;'' [] check_NewInstanceTest_newObject_75"


(* Lorg/graalvm/compiler/hotspot/amd64/test/NumberOfTrailingZeroings003;.NumberOfTrailingZeroings003_numberOfTrailingZeros0*)
definition unit_NumberOfTrailingZeroings003_numberOfTrailingZeros0 :: IRGraph where
  "unit_NumberOfTrailingZeroings003_numberOfTrailingZeros0 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (3, (ConstantNode (new_int 32 (32))), IntegerStamp 32 (32) (32)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_NumberOfTrailingZeroings003_numberOfTrailingZeros0  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/hotspot/amd64/test/NumberOfTrailingZeroings003;.NumberOfTrailingZeroings003_numberOfTrailingZeros1*)
definition unit_NumberOfTrailingZeroings003_numberOfTrailingZeros1 :: IRGraph where
  "unit_NumberOfTrailingZeroings003_numberOfTrailingZeros1 = irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_NumberOfTrailingZeroings003_numberOfTrailingZeros1  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/hotspot/amd64/test/NumberOfTrailingZeroings003;.NumberOfTrailingZeroings003_numberOfTrailingZerosM1*)
definition unit_NumberOfTrailingZeroings003_numberOfTrailingZerosM1 :: IRGraph where
  "unit_NumberOfTrailingZeroings003_numberOfTrailingZerosM1 = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_NumberOfTrailingZeroings003_numberOfTrailingZerosM1  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/hotspot/amd64/test/NumberOfTrailingZeroings003;.NumberOfTrailingZeroings003_numberOfTrailingZerosMax*)
definition unit_NumberOfTrailingZeroings003_numberOfTrailingZerosMax :: IRGraph where
  "unit_NumberOfTrailingZeroings003_numberOfTrailingZerosMax = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (2147483647))), IntegerStamp 32 (2147483647) (2147483647)),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_NumberOfTrailingZeroings003_numberOfTrailingZerosMax  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/hotspot/amd64/test/NumberOfTrailingZeroings003;.NumberOfTrailingZeroings003_numberOfTrailingZerosMin*)
definition unit_NumberOfTrailingZeroings003_numberOfTrailingZerosMin :: IRGraph where
  "unit_NumberOfTrailingZeroings003_numberOfTrailingZerosMin = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (-2147483648))), IntegerStamp 32 (-2147483648) (-2147483648)),
  (3, (ConstantNode (new_int 32 (31))), IntegerStamp 32 (31) (31)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_NumberOfTrailingZeroings003_numberOfTrailingZerosMin  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/api/directives/test/OpaqueDirectiveTest;.OpaqueDirectiveTest_booleanSnippet*)
definition unit_OpaqueDirectiveTest_booleanSnippet :: IRGraph where
  "unit_OpaqueDirectiveTest_booleanSnippet = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_OpaqueDirectiveTest_booleanSnippet  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/api/directives/test/OpaqueDirectiveTest;.OpaqueDirectiveTest_intSnippet*)
definition unit_OpaqueDirectiveTest_intSnippet :: IRGraph where
  "unit_OpaqueDirectiveTest_intSnippet = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (8))), IntegerStamp 32 (8) (8)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_OpaqueDirectiveTest_intSnippet  [] (new_int 32 (8))"


(* Lorg/graalvm/compiler/api/directives/test/OpaqueDirectiveTest;.OpaqueDirectiveTest_objectSnippet*)
definition unit_OpaqueDirectiveTest_objectSnippet :: IRGraph where
  "unit_OpaqueDirectiveTest_objectSnippet = irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.api.directives.test.OpaqueDirectiveTest$Dummy'' None 6), ObjectStamp ''org.graalvm.compiler.api.directives.test.OpaqueDirectiveTest$Dummy'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (ObjRef None)), ObjectStamp ''null'' False False True),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]"
value "static_test unit_OpaqueDirectiveTest_objectSnippet  [] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/Phi01;.Phi01_test*)
definition unit_Phi01_test :: Program where
  "unit_Phi01_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.Phi01.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NewInstanceNode 3 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi'' None 5), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Phi01$Phi'' True True False),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' 1 (Some 7) (Some 3) 9), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (FrameState [] (Some 6) None None), IllegalStamp),
  (8, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Phi01.test2(Lorg/graalvm/compiler/jtt/optimize/Phi01$Phi;I)I'' [3, 1]), VoidStamp),
  (9, (InvokeNode 9 8 None None (Some 10) 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ReturnNode (Some 9) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Phi01.test2(Lorg/graalvm/compiler/jtt/optimize/Phi01$Phi;I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 9), VoidStamp),
  (1, (ParameterNode 0), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Phi01$Phi'' True False False),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (5, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (6, (IntegerLessThanNode 2 5), VoidStamp),
  (7, (BeginNode 10), VoidStamp),
  (8, (BeginNode 17), VoidStamp),
  (9, (IfNode 6 8 7), VoidStamp),
  (10, (LoadFieldNode 10 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' (Some 1) 13), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (12, (AddNode 10 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (13, (StoreFieldNode 13 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' 12 (Some 14) (Some 1) 42), VoidStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (AddNode 2 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (17, (LoadFieldNode 17 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' (Some 1) 19), IntegerStamp 32 (-2147483648) (2147483647)),
  (18, (AddNode 17 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (StoreFieldNode 19 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' 18 (Some 20) (Some 1) 26), VoidStamp),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (AddNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (23, (IntegerLessThanNode 21 22), VoidStamp),
  (24, (BeginNode 27), VoidStamp),
  (25, (BeginNode 52), VoidStamp),
  (26, (IfNode 23 25 24), VoidStamp),
  (27, (LoadFieldNode 27 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' (Some 1) 29), IntegerStamp 32 (-2147483648) (2147483647)),
  (28, (AddNode 27 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (29, (StoreFieldNode 29 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' 28 (Some 30) (Some 1) 36), VoidStamp),
  (30, (FrameState [] None None None), IllegalStamp),
  (31, (AddNode 21 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (32, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (33, (IntegerLessThanNode 31 32), VoidStamp),
  (34, (BeginNode 37), VoidStamp),
  (35, (BeginNode 46), VoidStamp),
  (36, (IfNode 33 35 34), VoidStamp),
  (37, (LoadFieldNode 37 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' (Some 1) 39), IntegerStamp 32 (-2147483648) (2147483647)),
  (38, (AddNode 37 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (39, (StoreFieldNode 39 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' 38 (Some 40) (Some 1) 44), VoidStamp),
  (40, (FrameState [] None None None), IllegalStamp),
  (41, (AddNode 31 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (42, (EndNode), VoidStamp),
  (43, (MergeNode [42, 44, 51, 57] (Some 58) 59), VoidStamp),
  (44, (EndNode), VoidStamp),
  (45, (ValuePhiNode 45 [15, 41, 50, 56] 43), IntegerStamp 32 (-2147483648) (2147483647)),
  (46, (LoadFieldNode 46 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' (Some 1) 48), IntegerStamp 32 (-2147483648) (2147483647)),
  (47, (AddNode 46 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (48, (StoreFieldNode 48 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' 47 (Some 49) (Some 1) 51), VoidStamp),
  (49, (FrameState [] None None None), IllegalStamp),
  (50, (AddNode 31 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (51, (EndNode), VoidStamp),
  (52, (LoadFieldNode 52 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' (Some 1) 54), IntegerStamp 32 (-2147483648) (2147483647)),
  (53, (AddNode 52 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (54, (StoreFieldNode 54 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' 53 (Some 55) (Some 1) 57), VoidStamp),
  (55, (FrameState [] None None None), IllegalStamp),
  (56, (AddNode 21 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (57, (EndNode), VoidStamp),
  (58, (FrameState [] None None None), IllegalStamp),
  (59, (LoadFieldNode 59 ''org.graalvm.compiler.jtt.optimize.Phi01$Phi::f'' (Some 1) 61), IntegerStamp 32 (-2147483648) (2147483647)),
  (60, (AddNode 45 59), IntegerStamp 32 (-2147483648) (2147483647)),
  (61, (ReturnNode (Some 60) None), VoidStamp)
  ]
  )"
value "program_test unit_Phi01_test ''org.graalvm.compiler.jtt.optimize.Phi01.test(I)I'' [(new_int 32 (0))] (new_int 32 (8))"

value "program_test unit_Phi01_test ''org.graalvm.compiler.jtt.optimize.Phi01.test(I)I'' [(new_int 32 (1))] (new_int 32 (10))"

value "program_test unit_Phi01_test ''org.graalvm.compiler.jtt.optimize.Phi01.test(I)I'' [(new_int 32 (2))] (new_int 32 (12))"

value "program_test unit_Phi01_test ''org.graalvm.compiler.jtt.optimize.Phi01.test(I)I'' [(new_int 32 (3))] (new_int 32 (8))"

value "program_test unit_Phi01_test ''org.graalvm.compiler.jtt.optimize.Phi01.test(I)I'' [(new_int 32 (4))] (new_int 32 (10))"

value "program_test unit_Phi01_test ''org.graalvm.compiler.jtt.optimize.Phi01.test(I)I'' [(new_int 32 (6))] (new_int 32 (14))"


(* Lorg/graalvm/compiler/jtt/optimize/Phi02;.Phi02_test*)
definition unit_Phi02_test :: Program where
  "unit_Phi02_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.Phi02.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NewInstanceNode 3 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi'' None 5), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Phi02$Phi'' True True False),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' 1 (Some 7) (Some 3) 9), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (FrameState [] (Some 6) None None), IllegalStamp),
  (8, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Phi02.test2(Lorg/graalvm/compiler/jtt/optimize/Phi02$Phi;I)I'' [3, 1]), VoidStamp),
  (9, (InvokeNode 9 8 None None (Some 10) 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ReturnNode (Some 9) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Phi02.test2(Lorg/graalvm/compiler/jtt/optimize/Phi02$Phi;I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 9), VoidStamp),
  (1, (ParameterNode 0), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Phi02$Phi'' True False False),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (5, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (6, (IntegerLessThanNode 2 5), VoidStamp),
  (7, (BeginNode 12), VoidStamp),
  (8, (BeginNode 20), VoidStamp),
  (9, (IfNode 6 8 7), VoidStamp),
  (10, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (LoadFieldNode 12 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' (Some 1) 14), IntegerStamp 32 (-2147483648) (2147483647)),
  (13, (AddNode 12 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' 13 (Some 16) (Some 1) 50), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (FrameState [] (Some 15) None None), IllegalStamp),
  (17, (AddNode 2 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (LoadFieldNode 20 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' (Some 1) 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (AddNode 20 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (StoreFieldNode 22 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' 21 (Some 24) (Some 1) 30), VoidStamp),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (FrameState [] (Some 23) None None), IllegalStamp),
  (25, (AddNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (27, (IntegerLessThanNode 25 26), VoidStamp),
  (28, (BeginNode 32), VoidStamp),
  (29, (BeginNode 63), VoidStamp),
  (30, (IfNode 27 29 28), VoidStamp),
  (31, (FrameState [] None None None), IllegalStamp),
  (32, (LoadFieldNode 32 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' (Some 1) 34), IntegerStamp 32 (-2147483648) (2147483647)),
  (33, (AddNode 32 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (34, (StoreFieldNode 34 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' 33 (Some 36) (Some 1) 42), VoidStamp),
  (35, (FrameState [] None None None), IllegalStamp),
  (36, (FrameState [] (Some 35) None None), IllegalStamp),
  (37, (AddNode 25 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (38, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (39, (IntegerLessThanNode 37 38), VoidStamp),
  (40, (BeginNode 44), VoidStamp),
  (41, (BeginNode 55), VoidStamp),
  (42, (IfNode 39 41 40), VoidStamp),
  (43, (FrameState [] None None None), IllegalStamp),
  (44, (LoadFieldNode 44 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' (Some 1) 46), IntegerStamp 32 (-2147483648) (2147483647)),
  (45, (AddNode 44 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (46, (StoreFieldNode 46 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' 45 (Some 48) (Some 1) 52), VoidStamp),
  (47, (FrameState [] None None None), IllegalStamp),
  (48, (FrameState [] (Some 47) None None), IllegalStamp),
  (49, (AddNode 37 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (50, (EndNode), VoidStamp),
  (51, (MergeNode [50, 52, 61, 69] (Some 70) 71), VoidStamp),
  (52, (EndNode), VoidStamp),
  (53, (ValuePhiNode 53 [17, 49, 60, 68] 51), IntegerStamp 32 (-2147483648) (2147483647)),
  (54, (FrameState [] None None None), IllegalStamp),
  (55, (LoadFieldNode 55 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' (Some 1) 57), IntegerStamp 32 (-2147483648) (2147483647)),
  (56, (AddNode 55 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (57, (StoreFieldNode 57 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' 56 (Some 59) (Some 1) 61), VoidStamp),
  (58, (FrameState [] None None None), IllegalStamp),
  (59, (FrameState [] (Some 58) None None), IllegalStamp),
  (60, (AddNode 37 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (61, (EndNode), VoidStamp),
  (62, (FrameState [] None None None), IllegalStamp),
  (63, (LoadFieldNode 63 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' (Some 1) 65), IntegerStamp 32 (-2147483648) (2147483647)),
  (64, (AddNode 63 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (65, (StoreFieldNode 65 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' 64 (Some 67) (Some 1) 69), VoidStamp),
  (66, (FrameState [] None None None), IllegalStamp),
  (67, (FrameState [] (Some 66) None None), IllegalStamp),
  (68, (AddNode 25 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (69, (EndNode), VoidStamp),
  (70, (FrameState [] None None None), IllegalStamp),
  (71, (LoadFieldNode 71 ''org.graalvm.compiler.jtt.optimize.Phi02$Phi::f'' (Some 1) 73), IntegerStamp 32 (-2147483648) (2147483647)),
  (72, (AddNode 53 71), IntegerStamp 32 (-2147483648) (2147483647)),
  (73, (ReturnNode (Some 72) None), VoidStamp)
  ]
  )"
value "program_test unit_Phi02_test ''org.graalvm.compiler.jtt.optimize.Phi02.test(I)I'' [(new_int 32 (0))] (new_int 32 (8))"

value "program_test unit_Phi02_test ''org.graalvm.compiler.jtt.optimize.Phi02.test(I)I'' [(new_int 32 (1))] (new_int 32 (10))"

value "program_test unit_Phi02_test ''org.graalvm.compiler.jtt.optimize.Phi02.test(I)I'' [(new_int 32 (2))] (new_int 32 (12))"

value "program_test unit_Phi02_test ''org.graalvm.compiler.jtt.optimize.Phi02.test(I)I'' [(new_int 32 (3))] (new_int 32 (8))"

value "program_test unit_Phi02_test ''org.graalvm.compiler.jtt.optimize.Phi02.test(I)I'' [(new_int 32 (4))] (new_int 32 (10))"

value "program_test unit_Phi02_test ''org.graalvm.compiler.jtt.optimize.Phi02.test(I)I'' [(new_int 32 (6))] (new_int 32 (14))"


(* Lorg/graalvm/compiler/jtt/optimize/Phi03;.Phi03_test*)
definition unit_Phi03_test :: Program where
  "unit_Phi03_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.Phi03.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NewInstanceNode 3 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi'' None 5), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Phi03$Phi'' True True False),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' 1 (Some 7) (Some 3) 9), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (FrameState [] (Some 6) None None), IllegalStamp),
  (8, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Phi03.test2(Lorg/graalvm/compiler/jtt/optimize/Phi03$Phi;I)I'' [3, 1]), VoidStamp),
  (9, (InvokeNode 9 8 None None (Some 10) 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ReturnNode (Some 9) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Phi03.test2(Lorg/graalvm/compiler/jtt/optimize/Phi03$Phi;I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 9), VoidStamp),
  (1, (ParameterNode 0), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Phi03$Phi'' True False False),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (5, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (6, (IntegerLessThanNode 2 5), VoidStamp),
  (7, (BeginNode 12), VoidStamp),
  (8, (BeginNode 20), VoidStamp),
  (9, (IfNode 6 8 7), VoidStamp),
  (10, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (LoadFieldNode 12 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' (Some 1) 14), IntegerStamp 32 (-2147483648) (2147483647)),
  (13, (AddNode 12 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' 13 (Some 16) (Some 1) 50), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (FrameState [] (Some 15) None None), IllegalStamp),
  (17, (AddNode 2 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (LoadFieldNode 20 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' (Some 1) 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (AddNode 20 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (StoreFieldNode 22 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' 21 (Some 24) (Some 1) 30), VoidStamp),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (FrameState [] (Some 23) None None), IllegalStamp),
  (25, (AddNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (27, (IntegerLessThanNode 25 26), VoidStamp),
  (28, (BeginNode 32), VoidStamp),
  (29, (BeginNode 62), VoidStamp),
  (30, (IfNode 27 29 28), VoidStamp),
  (31, (FrameState [] None None None), IllegalStamp),
  (32, (LoadFieldNode 32 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' (Some 1) 34), IntegerStamp 32 (-2147483648) (2147483647)),
  (33, (AddNode 32 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (34, (StoreFieldNode 34 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' 33 (Some 36) (Some 1) 42), VoidStamp),
  (35, (FrameState [] None None None), IllegalStamp),
  (36, (FrameState [] (Some 35) None None), IllegalStamp),
  (37, (AddNode 25 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (38, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (39, (IntegerLessThanNode 37 38), VoidStamp),
  (40, (BeginNode 44), VoidStamp),
  (41, (BeginNode 54), VoidStamp),
  (42, (IfNode 39 41 40), VoidStamp),
  (43, (FrameState [] None None None), IllegalStamp),
  (44, (LoadFieldNode 44 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' (Some 1) 46), IntegerStamp 32 (-2147483648) (2147483647)),
  (45, (AddNode 44 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (46, (StoreFieldNode 46 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' 45 (Some 48) (Some 1) 52), VoidStamp),
  (47, (FrameState [] None None None), IllegalStamp),
  (48, (FrameState [] (Some 47) None None), IllegalStamp),
  (49, (AddNode 37 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (50, (EndNode), VoidStamp),
  (51, (MergeNode [50, 52, 60, 68] (Some 69) 70), VoidStamp),
  (52, (EndNode), VoidStamp),
  (53, (FrameState [] None None None), IllegalStamp),
  (54, (LoadFieldNode 54 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' (Some 1) 56), IntegerStamp 32 (-2147483648) (2147483647)),
  (55, (AddNode 54 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (56, (StoreFieldNode 56 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' 55 (Some 58) (Some 1) 60), VoidStamp),
  (57, (FrameState [] None None None), IllegalStamp),
  (58, (FrameState [] (Some 57) None None), IllegalStamp),
  (59, (AddNode 37 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (60, (EndNode), VoidStamp),
  (61, (FrameState [] None None None), IllegalStamp),
  (62, (LoadFieldNode 62 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' (Some 1) 64), IntegerStamp 32 (-2147483648) (2147483647)),
  (63, (AddNode 62 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (64, (StoreFieldNode 64 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' 63 (Some 66) (Some 1) 68), VoidStamp),
  (65, (FrameState [] None None None), IllegalStamp),
  (66, (FrameState [] (Some 65) None None), IllegalStamp),
  (67, (AddNode 25 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (68, (EndNode), VoidStamp),
  (69, (FrameState [] None None None), IllegalStamp),
  (70, (LoadFieldNode 70 ''org.graalvm.compiler.jtt.optimize.Phi03$Phi::f'' (Some 1) 71), IntegerStamp 32 (-2147483648) (2147483647)),
  (71, (ReturnNode (Some 70) None), VoidStamp)
  ]
  )"
value "program_test unit_Phi03_test ''org.graalvm.compiler.jtt.optimize.Phi03.test(I)I'' [(new_int 32 (0))] (new_int 32 (4))"

value "program_test unit_Phi03_test ''org.graalvm.compiler.jtt.optimize.Phi03.test(I)I'' [(new_int 32 (1))] (new_int 32 (5))"

value "program_test unit_Phi03_test ''org.graalvm.compiler.jtt.optimize.Phi03.test(I)I'' [(new_int 32 (2))] (new_int 32 (6))"

value "program_test unit_Phi03_test ''org.graalvm.compiler.jtt.optimize.Phi03.test(I)I'' [(new_int 32 (3))] (new_int 32 (4))"

value "program_test unit_Phi03_test ''org.graalvm.compiler.jtt.optimize.Phi03.test(I)I'' [(new_int 32 (4))] (new_int 32 (5))"

value "program_test unit_Phi03_test ''org.graalvm.compiler.jtt.optimize.Phi03.test(I)I'' [(new_int 32 (6))] (new_int 32 (7))"


(* Lorg/graalvm/compiler/jtt/optimize/Reduce_Convert01;.Reduce_Convert01_test*)
definition unit_Reduce_Convert01_test :: IRGraph where
  "unit_Reduce_Convert01_test = irgraph [
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
  (13, (NarrowNode 32 8 12), IntegerStamp 8 (-128) (127)),
  (14, (ReturnNode (Some 12) None), VoidStamp),
  (15, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (16, (IntegerEqualsNode 1 15), VoidStamp),
  (17, (BeginNode 29), VoidStamp),
  (18, (BeginNode 24), VoidStamp),
  (19, (IfNode 16 18 17), VoidStamp),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (NarrowNode 32 16 9), IntegerStamp 16 (-32768) (32767)),
  (22, (SignExtendNode 16 32 21), IntegerStamp 32 (-32768) (32767)),
  (23, (NarrowNode 32 16 22), IntegerStamp 16 (-32768) (32767)),
  (24, (ReturnNode (Some 22) None), VoidStamp),
  (25, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (26, (IntegerEqualsNode 1 25), VoidStamp),
  (27, (BeginNode 34), VoidStamp),
  (28, (BeginNode 33), VoidStamp),
  (29, (IfNode 26 28 27), VoidStamp),
  (30, (FrameState [] None None None), IllegalStamp),
  (31, (ZeroExtendNode 16 32 21), IntegerStamp 32 (0) (65535)),
  (32, (NarrowNode 32 16 31), IntegerStamp 16 (-32768) (32767)),
  (33, (ReturnNode (Some 31) None), VoidStamp),
  (34, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Reduce_Convert01_test  [(new_int 32 (0))] (new_int 32 (10))"

value "static_test unit_Reduce_Convert01_test  [(new_int 32 (1))] (new_int 32 (11))"

value "static_test unit_Reduce_Convert01_test  [(new_int 32 (2))] (new_int 32 (12))"


(* Lorg/graalvm/compiler/jtt/optimize/Reduce_Int01;.Reduce_Int01_test*)
definition unit_Reduce_Int01_test :: IRGraph where
  "unit_Reduce_Int01_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ReturnNode (Some 8) None), VoidStamp),
  (11, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (12, (IntegerEqualsNode 1 11), VoidStamp),
  (13, (BeginNode 23), VoidStamp),
  (14, (BeginNode 18), VoidStamp),
  (15, (IfNode 12 14 13), VoidStamp),
  (16, (ConstantNode (new_int 32 (11))), IntegerStamp 32 (11) (11)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp),
  (19, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (20, (IntegerEqualsNode 1 19), VoidStamp),
  (21, (BeginNode 31), VoidStamp),
  (22, (BeginNode 26), VoidStamp),
  (23, (IfNode 20 22 21), VoidStamp),
  (24, (ConstantNode (new_int 32 (12))), IntegerStamp 32 (12) (12)),
  (25, (FrameState [] None None None), IllegalStamp),
  (26, (ReturnNode (Some 24) None), VoidStamp),
  (27, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (28, (IntegerEqualsNode 1 27), VoidStamp),
  (29, (BeginNode 39), VoidStamp),
  (30, (BeginNode 34), VoidStamp),
  (31, (IfNode 28 30 29), VoidStamp),
  (32, (ConstantNode (new_int 32 (13))), IntegerStamp 32 (13) (13)),
  (33, (FrameState [] None None None), IllegalStamp),
  (34, (ReturnNode (Some 32) None), VoidStamp),
  (35, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (36, (IntegerEqualsNode 1 35), VoidStamp),
  (37, (BeginNode 47), VoidStamp),
  (38, (BeginNode 42), VoidStamp),
  (39, (IfNode 36 38 37), VoidStamp),
  (40, (FrameState [] None None None), IllegalStamp),
  (41, (ConstantNode (new_int 32 (14))), IntegerStamp 32 (14) (14)),
  (42, (ReturnNode (Some 41) None), VoidStamp),
  (43, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (44, (IntegerEqualsNode 1 43), VoidStamp),
  (45, (BeginNode 56), VoidStamp),
  (46, (BeginNode 51), VoidStamp),
  (47, (IfNode 44 46 45), VoidStamp),
  (48, (ConstantNode (new_int 32 (15))), IntegerStamp 32 (15) (15)),
  (49, (FrameState [] None None None), IllegalStamp),
  (50, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (51, (ReturnNode (Some 48) None), VoidStamp),
  (52, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (53, (IntegerEqualsNode 1 52), VoidStamp),
  (54, (BeginNode 64), VoidStamp),
  (55, (BeginNode 59), VoidStamp),
  (56, (IfNode 53 55 54), VoidStamp),
  (57, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (58, (FrameState [] None None None), IllegalStamp),
  (59, (ReturnNode (Some 57) None), VoidStamp),
  (60, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (61, (IntegerEqualsNode 1 60), VoidStamp),
  (62, (BeginNode 68), VoidStamp),
  (63, (BeginNode 67), VoidStamp),
  (64, (IfNode 61 63 62), VoidStamp),
  (65, (ConstantNode (new_int 32 (17))), IntegerStamp 32 (17) (17)),
  (66, (FrameState [] None None None), IllegalStamp),
  (67, (ReturnNode (Some 65) None), VoidStamp),
  (68, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Reduce_Int01_test  [(new_int 32 (0))] (new_int 32 (10))"

value "static_test unit_Reduce_Int01_test  [(new_int 32 (1))] (new_int 32 (11))"

value "static_test unit_Reduce_Int01_test  [(new_int 32 (2))] (new_int 32 (12))"

value "static_test unit_Reduce_Int01_test  [(new_int 32 (3))] (new_int 32 (13))"

value "static_test unit_Reduce_Int01_test  [(new_int 32 (4))] (new_int 32 (14))"

value "static_test unit_Reduce_Int01_test  [(new_int 32 (5))] (new_int 32 (15))"

value "static_test unit_Reduce_Int01_test  [(new_int 32 (6))] (new_int 32 (16))"

value "static_test unit_Reduce_Int01_test  [(new_int 32 (7))] (new_int 32 (17))"


(* Lorg/graalvm/compiler/jtt/optimize/Reduce_Int02;.Reduce_Int02_test*)
definition unit_Reduce_Int02_test :: IRGraph where
  "unit_Reduce_Int02_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 15), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ReturnNode (Some 8) None), VoidStamp),
  (11, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (12, (IntegerEqualsNode 1 11), VoidStamp),
  (13, (BeginNode 23), VoidStamp),
  (14, (BeginNode 18), VoidStamp),
  (15, (IfNode 12 14 13), VoidStamp),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (ConstantNode (new_int 32 (11))), IntegerStamp 32 (11) (11)),
  (18, (ReturnNode (Some 17) None), VoidStamp),
  (19, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (20, (IntegerEqualsNode 1 19), VoidStamp),
  (21, (BeginNode 31), VoidStamp),
  (22, (BeginNode 26), VoidStamp),
  (23, (IfNode 20 22 21), VoidStamp),
  (24, (ConstantNode (new_int 32 (12))), IntegerStamp 32 (12) (12)),
  (25, (FrameState [] None None None), IllegalStamp),
  (26, (ReturnNode (Some 24) None), VoidStamp),
  (27, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (28, (IntegerEqualsNode 1 27), VoidStamp),
  (29, (BeginNode 39), VoidStamp),
  (30, (BeginNode 34), VoidStamp),
  (31, (IfNode 28 30 29), VoidStamp),
  (32, (FrameState [] None None None), IllegalStamp),
  (33, (ConstantNode (new_int 32 (13))), IntegerStamp 32 (13) (13)),
  (34, (ReturnNode (Some 33) None), VoidStamp),
  (35, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (36, (IntegerEqualsNode 1 35), VoidStamp),
  (37, (BeginNode 47), VoidStamp),
  (38, (BeginNode 42), VoidStamp),
  (39, (IfNode 36 38 37), VoidStamp),
  (40, (FrameState [] None None None), IllegalStamp),
  (41, (ConstantNode (new_int 32 (14))), IntegerStamp 32 (14) (14)),
  (42, (ReturnNode (Some 41) None), VoidStamp),
  (43, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (44, (IntegerEqualsNode 1 43), VoidStamp),
  (45, (BeginNode 56), VoidStamp),
  (46, (BeginNode 51), VoidStamp),
  (47, (IfNode 44 46 45), VoidStamp),
  (48, (ConstantNode (new_int 32 (15))), IntegerStamp 32 (15) (15)),
  (49, (FrameState [] None None None), IllegalStamp),
  (50, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (51, (ReturnNode (Some 48) None), VoidStamp),
  (52, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (53, (IntegerEqualsNode 1 52), VoidStamp),
  (54, (BeginNode 64), VoidStamp),
  (55, (BeginNode 59), VoidStamp),
  (56, (IfNode 53 55 54), VoidStamp),
  (57, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (58, (FrameState [] None None None), IllegalStamp),
  (59, (ReturnNode (Some 57) None), VoidStamp),
  (60, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (61, (IntegerEqualsNode 1 60), VoidStamp),
  (62, (BeginNode 68), VoidStamp),
  (63, (BeginNode 67), VoidStamp),
  (64, (IfNode 61 63 62), VoidStamp),
  (65, (ConstantNode (new_int 32 (17))), IntegerStamp 32 (17) (17)),
  (66, (FrameState [] None None None), IllegalStamp),
  (67, (ReturnNode (Some 65) None), VoidStamp),
  (68, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Reduce_Int02_test  [(new_int 32 (0))] (new_int 32 (10))"

value "static_test unit_Reduce_Int02_test  [(new_int 32 (1))] (new_int 32 (11))"

value "static_test unit_Reduce_Int02_test  [(new_int 32 (2))] (new_int 32 (12))"

value "static_test unit_Reduce_Int02_test  [(new_int 32 (3))] (new_int 32 (13))"

value "static_test unit_Reduce_Int02_test  [(new_int 32 (4))] (new_int 32 (14))"

value "static_test unit_Reduce_Int02_test  [(new_int 32 (5))] (new_int 32 (15))"

value "static_test unit_Reduce_Int02_test  [(new_int 32 (6))] (new_int 32 (16))"

value "static_test unit_Reduce_Int02_test  [(new_int 32 (7))] (new_int 32 (17))"


(* Lorg/graalvm/compiler/jtt/optimize/Reduce_Int03;.Reduce_Int03_test*)
definition unit_Reduce_Int03_test :: IRGraph where
  "unit_Reduce_Int03_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (11, (ReturnNode (Some 10) None), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (IntegerEqualsNode 1 12), VoidStamp),
  (14, (BeginNode 23), VoidStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 13 15 14), VoidStamp),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 3) None), VoidStamp),
  (19, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (20, (IntegerEqualsNode 1 19), VoidStamp),
  (21, (BeginNode 31), VoidStamp),
  (22, (BeginNode 26), VoidStamp),
  (23, (IfNode 20 22 21), VoidStamp),
  (24, (FrameState [] None None None), IllegalStamp),
  (25, (ConstantNode (new_int 32 (25))), IntegerStamp 32 (25) (25)),
  (26, (ReturnNode (Some 25) None), VoidStamp),
  (27, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (28, (IntegerEqualsNode 1 27), VoidStamp),
  (29, (BeginNode 38), VoidStamp),
  (30, (BeginNode 33), VoidStamp),
  (31, (IfNode 28 30 29), VoidStamp),
  (32, (FrameState [] None None None), IllegalStamp),
  (33, (ReturnNode (Some 12) None), VoidStamp),
  (34, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (35, (IntegerEqualsNode 1 34), VoidStamp),
  (36, (BeginNode 44), VoidStamp),
  (37, (BeginNode 40), VoidStamp),
  (38, (IfNode 35 37 36), VoidStamp),
  (39, (FrameState [] None None None), IllegalStamp),
  (40, (ReturnNode (Some 3) None), VoidStamp),
  (41, (IntegerEqualsNode 1 8), VoidStamp),
  (42, (BeginNode 52), VoidStamp),
  (43, (BeginNode 47), VoidStamp),
  (44, (IfNode 41 43 42), VoidStamp),
  (45, (ConstantNode (new_int 32 (15))), IntegerStamp 32 (15) (15)),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (ReturnNode (Some 45) None), VoidStamp),
  (48, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (49, (IntegerEqualsNode 1 48), VoidStamp),
  (50, (BeginNode 60), VoidStamp),
  (51, (BeginNode 55), VoidStamp),
  (52, (IfNode 49 51 50), VoidStamp),
  (53, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (54, (FrameState [] None None None), IllegalStamp),
  (55, (ReturnNode (Some 53) None), VoidStamp),
  (56, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (57, (IntegerEqualsNode 1 56), VoidStamp),
  (58, (BeginNode 64), VoidStamp),
  (59, (BeginNode 63), VoidStamp),
  (60, (IfNode 57 59 58), VoidStamp),
  (61, (ConstantNode (new_int 32 (17))), IntegerStamp 32 (17) (17)),
  (62, (FrameState [] None None None), IllegalStamp),
  (63, (ReturnNode (Some 3) None), VoidStamp),
  (64, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Reduce_Int03_test  [(new_int 32 (0))] (new_int 32 (10))"

value "static_test unit_Reduce_Int03_test  [(new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_Reduce_Int03_test  [(new_int 32 (2))] (new_int 32 (25))"

value "static_test unit_Reduce_Int03_test  [(new_int 32 (3))] (new_int 32 (1))"

value "static_test unit_Reduce_Int03_test  [(new_int 32 (4))] (new_int 32 (0))"

value "static_test unit_Reduce_Int03_test  [(new_int 32 (5))] (new_int 32 (15))"

value "static_test unit_Reduce_Int03_test  [(new_int 32 (6))] (new_int 32 (16))"

value "static_test unit_Reduce_Int03_test  [(new_int 32 (7))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/Reduce_Int04;.Reduce_Int04_test*)
definition unit_Reduce_Int04_test :: IRGraph where
  "unit_Reduce_Int04_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 18), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (9, (AddNode 1 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (12, (MulNode 9 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (13, (ReturnNode (Some 12) None), VoidStamp),
  (14, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (IntegerEqualsNode 1 14), VoidStamp),
  (16, (BeginNode 25), VoidStamp),
  (17, (BeginNode 24), VoidStamp),
  (18, (IfNode 15 17 16), VoidStamp),
  (19, (ConstantNode (new_int 32 (9))), IntegerStamp 32 (9) (9)),
  (20, (AddNode 1 19), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ConstantNode (new_int 32 (65536))), IntegerStamp 32 (65536) (65536)),
  (23, (MulNode 20 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (24, (ReturnNode (Some 23) None), VoidStamp),
  (25, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Reduce_Int04_test  [(new_int 32 (0))] (new_int 32 (40))"

value "static_test unit_Reduce_Int04_test  [(new_int 32 (1))] (new_int 32 (655360))"


(* Lorg/graalvm/compiler/jtt/optimize/Reduce_IntShift01;.Reduce_IntShift01_test*)
definition unit_Reduce_IntShift01_test :: IRGraph where
  "unit_Reduce_IntShift01_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (9, (AddNode 1 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ReturnNode (Some 9) None), VoidStamp),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (IntegerEqualsNode 1 12), VoidStamp),
  (14, (BeginNode 23), VoidStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 13 15 14), VoidStamp),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode (Some 9) None), VoidStamp),
  (19, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (20, (IntegerEqualsNode 1 19), VoidStamp),
  (21, (BeginNode 30), VoidStamp),
  (22, (BeginNode 25), VoidStamp),
  (23, (IfNode 20 22 21), VoidStamp),
  (24, (FrameState [] None None None), IllegalStamp),
  (25, (ReturnNode (Some 9) None), VoidStamp),
  (26, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (27, (IntegerEqualsNode 1 26), VoidStamp),
  (28, (BeginNode 38), VoidStamp),
  (29, (BeginNode 33), VoidStamp),
  (30, (IfNode 27 29 28), VoidStamp),
  (31, (FrameState [] None None None), IllegalStamp),
  (32, (ConstantNode (new_int 32 (64))), IntegerStamp 32 (64) (64)),
  (33, (ReturnNode (Some 9) None), VoidStamp),
  (34, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (35, (IntegerEqualsNode 1 34), VoidStamp),
  (36, (BeginNode 45), VoidStamp),
  (37, (BeginNode 40), VoidStamp),
  (38, (IfNode 35 37 36), VoidStamp),
  (39, (FrameState [] None None None), IllegalStamp),
  (40, (ReturnNode (Some 9) None), VoidStamp),
  (41, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (42, (IntegerEqualsNode 1 41), VoidStamp),
  (43, (BeginNode 48), VoidStamp),
  (44, (BeginNode 47), VoidStamp),
  (45, (IfNode 42 44 43), VoidStamp),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (ReturnNode (Some 9) None), VoidStamp),
  (48, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Reduce_IntShift01_test  [(new_int 32 (0))] (new_int 32 (10))"

value "static_test unit_Reduce_IntShift01_test  [(new_int 32 (1))] (new_int 32 (11))"

value "static_test unit_Reduce_IntShift01_test  [(new_int 32 (2))] (new_int 32 (12))"

value "static_test unit_Reduce_IntShift01_test  [(new_int 32 (3))] (new_int 32 (13))"

value "static_test unit_Reduce_IntShift01_test  [(new_int 32 (4))] (new_int 32 (14))"

value "static_test unit_Reduce_IntShift01_test  [(new_int 32 (5))] (new_int 32 (15))"

end
