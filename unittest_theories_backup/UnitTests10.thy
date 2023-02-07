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


(* Lorg/graalvm/compiler/core/aarch64/test/AArch64PairLoadStoreTest;.AArch64PairLoadStoreTest_pairStoreStaticFields*)
definition unit_AArch64PairLoadStoreTest_pairStoreStaticFields :: IRGraph where
  "unit_AArch64PairLoadStoreTest_pairStoreStaticFields = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.core.aarch64.test.AArch64PairLoadStoreTest$A::c'' 1 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.core.aarch64.test.AArch64PairLoadStoreTest$A::d'' 2 (Some 7) None 8), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (LoadFieldNode 8 ''org.graalvm.compiler.core.aarch64.test.AArch64PairLoadStoreTest$A::c'' None 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (LoadFieldNode 9 ''org.graalvm.compiler.core.aarch64.test.AArch64PairLoadStoreTest$A::d'' None 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (AddNode 8 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_AArch64PairLoadStoreTest_pairStoreStaticFields  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (3))"


(* Lorg/graalvm/compiler/core/aarch64/test/AArch64PairLoadStoreTest;.AArch64PairLoadStoreTest_parameterSpill*)
definition unit_AArch64PairLoadStoreTest_parameterSpill :: IRGraph where
  "unit_AArch64PairLoadStoreTest_parameterSpill = irgraph [
  (0, (StartNode (Some 11) 21), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (ParameterNode 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (4, (ParameterNode 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ParameterNode 4), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (6, (ParameterNode 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (7, (ParameterNode 6), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (8, (ParameterNode 7), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (9, (ParameterNode 8), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (10, (ParameterNode 9), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (AddNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (13, (AddNode 3 12), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (14, (AddNode 4 13), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (15, (AddNode 5 14), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (16, (AddNode 6 15), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (17, (AddNode 7 16), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (18, (AddNode 8 17), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (19, (AddNode 9 10), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (20, (AddNode 18 19), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (21, (ReturnNode (Some 20) None), VoidStamp)
  ]"
value "static_test unit_AArch64PairLoadStoreTest_parameterSpill  [(IntVal 64 (1)), (IntVal 64 (2)), (IntVal 64 (3)), (IntVal 64 (4)), (IntVal 64 (5)), (IntVal 64 (6)), (IntVal 64 (7)), (IntVal 64 (8)), (IntVal 64 (9)), (IntVal 64 (10))] (IntVal 64 (55))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_b;.BC_getstatic_b_test*)
definition unit_BC_getstatic_b_test :: Program where
  "unit_BC_getstatic_b_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b.test()B'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b::field'' None 3), IntegerStamp 32 (-128) (127)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (11))), IntegerStamp 32 (11) (11)),
  (3, (ConstantNode (new_int 8 (11))), IntegerStamp 8 (11) (11)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b::field'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_BC_getstatic_b_test ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_b.test()B'' [] (new_int 32 (11))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_c;.BC_getstatic_c_test*)
definition unit_BC_getstatic_c_test :: Program where
  "unit_BC_getstatic_c_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c.test()C'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c::field'' None 3), IntegerStamp 32 (0) (65535)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (11))), IntegerStamp 32 (11) (11)),
  (3, (ConstantNode (new_int 16 (11))), IntegerStamp 16 (11) (11)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c::field'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_BC_getstatic_c_test ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_c.test()C'' [] (new_int 32 (11))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_i;.BC_getstatic_i_test*)
definition unit_BC_getstatic_i_test :: Program where
  "unit_BC_getstatic_i_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i.test()I'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i::field'' None 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (11))), IntegerStamp 32 (11) (11)),
  (3, (StoreFieldNode 3 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i::field'' 2 (Some 4) None 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_BC_getstatic_i_test ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_i.test()I'' [] (new_int 32 (11))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_l;.BC_getstatic_l_test*)
definition unit_BC_getstatic_l_test :: Program where
  "unit_BC_getstatic_l_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l.test()J'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l::field'' None 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (11))), IntegerStamp 64 (11) (11)),
  (3, (StoreFieldNode 3 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l::field'' 2 (Some 4) None 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_BC_getstatic_l_test ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_l.test()J'' [] (IntVal 64 (11))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_s;.BC_getstatic_s_test*)
definition unit_BC_getstatic_s_test :: Program where
  "unit_BC_getstatic_s_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s.test()S'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s::field'' None 3), IntegerStamp 32 (-32768) (32767)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (11))), IntegerStamp 32 (11) (11)),
  (3, (ConstantNode (new_int 16 (11))), IntegerStamp 16 (11) (11)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s::field'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_BC_getstatic_s_test ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_s.test()S'' [] (new_int 32 (11))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_getstatic_z;.BC_getstatic_z_test*)
definition unit_BC_getstatic_z_test :: Program where
  "unit_BC_getstatic_z_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z.test()Z'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (LoadFieldNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z::field'' None 3), IntegerStamp 32 (0) (1)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 4), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ConstantNode (new_int 1 (1))), IntegerStamp 1 (-1) (-1)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z::field'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_BC_getstatic_z_test ''org.graalvm.compiler.jtt.bytecode.BC_getstatic_z.test()Z'' [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2b;.BC_i2b_test*)
definition unit_BC_i2b_test :: IRGraph where
  "unit_BC_i2b_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (4, (SignExtendNode 8 32 3), IntegerStamp 32 (-128) (127)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2b_test  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_i2b_test  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_i2b_test  [(new_int 32 (255))] (new_int 32 (-1))"

value "static_test unit_BC_i2b_test  [(new_int 32 (128))] (new_int 32 (-128))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2b;.BC_i2b_testInt*)
definition unit_BC_i2b_testInt :: IRGraph where
  "unit_BC_i2b_testInt = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (4, (SignExtendNode 8 32 3), IntegerStamp 32 (-128) (127)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2b_testInt  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_i2b_testInt  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_i2b_testInt  [(new_int 32 (255))] (new_int 32 (-1))"

value "static_test unit_BC_i2b_testInt  [(new_int 32 (128))] (new_int 32 (-128))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2b;.BC_i2b_testLong*)
definition unit_BC_i2b_testLong :: IRGraph where
  "unit_BC_i2b_testLong = irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (4, (SignExtendNode 8 32 3), IntegerStamp 32 (-128) (127)),
  (5, (SignExtendNode 8 64 3), IntegerStamp 64 (-128) (127)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]"
value "static_test unit_BC_i2b_testLong  [(new_int 32 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_i2b_testLong  [(new_int 32 (2))] (IntVal 64 (2))"

value "static_test unit_BC_i2b_testLong  [(new_int 32 (255))] (IntVal 64 (-1))"

value "static_test unit_BC_i2b_testLong  [(new_int 32 (128))] (IntVal 64 (-128))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2c;.BC_i2c_test*)
definition unit_BC_i2c_test :: IRGraph where
  "unit_BC_i2c_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2c_test  [(new_int 32 (-1))] (new_int 32 (65535))"

value "static_test unit_BC_i2c_test  [(new_int 32 (645))] (new_int 32 (645))"

value "static_test unit_BC_i2c_test  [(new_int 32 (65535))] (new_int 32 (65535))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2c;.BC_i2c_testInt*)
definition unit_BC_i2c_testInt :: IRGraph where
  "unit_BC_i2c_testInt = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2c_testInt  [(new_int 32 (-1))] (new_int 32 (65535))"

value "static_test unit_BC_i2c_testInt  [(new_int 32 (645))] (new_int 32 (645))"

value "static_test unit_BC_i2c_testInt  [(new_int 32 (65535))] (new_int 32 (65535))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2c;.BC_i2c_testLong*)
definition unit_BC_i2c_testLong :: IRGraph where
  "unit_BC_i2c_testLong = irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (5, (ZeroExtendNode 16 64 3), IntegerStamp 64 (0) (65535)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]"
value "static_test unit_BC_i2c_testLong  [(new_int 32 (-1))] (IntVal 64 (65535))"

value "static_test unit_BC_i2c_testLong  [(new_int 32 (645))] (IntVal 64 (645))"

value "static_test unit_BC_i2c_testLong  [(new_int 32 (65535))] (IntVal 64 (65535))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2l;.BC_i2l_test*)
definition unit_BC_i2l_test :: IRGraph where
  "unit_BC_i2l_test = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (SignExtendNode 32 64 1), IntegerStamp 64 (-2147483648) (2147483647)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_BC_i2l_test  [(new_int 32 (1))] (IntVal 64 (1))"

value "static_test unit_BC_i2l_test  [(new_int 32 (2))] (IntVal 64 (2))"

value "static_test unit_BC_i2l_test  [(new_int 32 (3))] (IntVal 64 (3))"

value "static_test unit_BC_i2l_test  [(new_int 32 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_i2l_test  [(new_int 32 (-2147483647))] (IntVal 64 (-2147483647))"

value "static_test unit_BC_i2l_test  [(new_int 32 (-2147483648))] (IntVal 64 (-2147483648))"

value "static_test unit_BC_i2l_test  [(new_int 32 (2147483647))] (IntVal 64 (2147483647))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2s;.BC_i2s_test*)
definition unit_BC_i2s_test :: IRGraph where
  "unit_BC_i2s_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (SignExtendNode 16 32 3), IntegerStamp 32 (-32768) (32767)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2s_test  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_i2s_test  [(new_int 32 (34))] (new_int 32 (34))"

value "static_test unit_BC_i2s_test  [(new_int 32 (65535))] (new_int 32 (-1))"

value "static_test unit_BC_i2s_test  [(new_int 32 (32768))] (new_int 32 (-32768))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2s;.BC_i2s_testInt*)
definition unit_BC_i2s_testInt :: IRGraph where
  "unit_BC_i2s_testInt = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (SignExtendNode 16 32 3), IntegerStamp 32 (-32768) (32767)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_i2s_testInt  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_i2s_testInt  [(new_int 32 (34))] (new_int 32 (34))"

value "static_test unit_BC_i2s_testInt  [(new_int 32 (65535))] (new_int 32 (-1))"

value "static_test unit_BC_i2s_testInt  [(new_int 32 (32768))] (new_int 32 (-32768))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_i2s;.BC_i2s_testLong*)
definition unit_BC_i2s_testLong :: IRGraph where
  "unit_BC_i2s_testLong = irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (SignExtendNode 16 32 3), IntegerStamp 32 (-32768) (32767)),
  (5, (SignExtendNode 16 64 3), IntegerStamp 64 (-32768) (32767)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]"
value "static_test unit_BC_i2s_testLong  [(new_int 32 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_i2s_testLong  [(new_int 32 (34))] (IntVal 64 (34))"

value "static_test unit_BC_i2s_testLong  [(new_int 32 (65535))] (IntVal 64 (-1))"

value "static_test unit_BC_i2s_testLong  [(new_int 32 (32768))] (IntVal 64 (-32768))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iadd2;.BC_iadd2_test*)
definition unit_BC_iadd2_test :: IRGraph where
  "unit_BC_iadd2_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (AddNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iadd2_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (3))"

value "static_test unit_BC_iadd2_test  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iadd2_test  [(new_int 32 (33)), (new_int 32 (67))] (new_int 32 (100))"

value "static_test unit_BC_iadd2_test  [(new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_iadd2_test  [(new_int 32 (-128)), (new_int 32 (1))] (new_int 32 (-127))"

value "static_test unit_BC_iadd2_test  [(new_int 32 (127)), (new_int 32 (1))] (new_int 32 (128))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iadd3;.BC_iadd3_test*)
definition unit_BC_iadd3_test :: IRGraph where
  "unit_BC_iadd3_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (AddNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iadd3_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (3))"

value "static_test unit_BC_iadd3_test  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iadd3_test  [(new_int 32 (33)), (new_int 32 (67))] (new_int 32 (100))"

value "static_test unit_BC_iadd3_test  [(new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_iadd3_test  [(new_int 32 (-128)), (new_int 32 (1))] (new_int 32 (-127))"

value "static_test unit_BC_iadd3_test  [(new_int 32 (127)), (new_int 32 (1))] (new_int 32 (128))"

value "static_test unit_BC_iadd3_test  [(new_int 32 (-32768)), (new_int 32 (1))] (new_int 32 (-32767))"

value "static_test unit_BC_iadd3_test  [(new_int 32 (32767)), (new_int 32 (1))] (new_int 32 (32768))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iadd;.BC_iadd_test*)
definition unit_BC_iadd_test :: IRGraph where
  "unit_BC_iadd_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (AddNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iadd_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (3))"

value "static_test unit_BC_iadd_test  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iadd_test  [(new_int 32 (33)), (new_int 32 (67))] (new_int 32 (100))"

value "static_test unit_BC_iadd_test  [(new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_iadd_test  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (-2147483647))"

value "static_test unit_BC_iadd_test  [(new_int 32 (2147483647)), (new_int 32 (1))] (new_int 32 (-2147483648))"

value "static_test unit_BC_iadd_test  [(new_int 32 (-2147483647)), (new_int 32 (-2))] (new_int 32 (2147483647))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iand;.BC_iand_test*)
definition unit_BC_iand_test :: IRGraph where
  "unit_BC_iand_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (AndNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iand_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (0))"

value "static_test unit_BC_iand_test  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_iand_test  [(new_int 32 (31)), (new_int 32 (63))] (new_int 32 (31))"

value "static_test unit_BC_iand_test  [(new_int 32 (6)), (new_int 32 (4))] (new_int 32 (4))"

value "static_test unit_BC_iand_test  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iconst;.BC_iconst_test*)
definition unit_BC_iconst_test :: IRGraph where
  "unit_BC_iconst_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 8), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ReturnNode (Some 3) None), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (IntegerEqualsNode 1 9), VoidStamp),
  (11, (BeginNode 19), VoidStamp),
  (12, (BeginNode 14), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ReturnNode (Some 9) None), VoidStamp),
  (15, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (16, (IntegerEqualsNode 1 15), VoidStamp),
  (17, (BeginNode 25), VoidStamp),
  (18, (BeginNode 20), VoidStamp),
  (19, (IfNode 16 18 17), VoidStamp),
  (20, (ReturnNode (Some 15) None), VoidStamp),
  (21, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (22, (IntegerEqualsNode 1 21), VoidStamp),
  (23, (BeginNode 31), VoidStamp),
  (24, (BeginNode 26), VoidStamp),
  (25, (IfNode 22 24 23), VoidStamp),
  (26, (ReturnNode (Some 21) None), VoidStamp),
  (27, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (28, (IntegerEqualsNode 1 27), VoidStamp),
  (29, (BeginNode 37), VoidStamp),
  (30, (BeginNode 32), VoidStamp),
  (31, (IfNode 28 30 29), VoidStamp),
  (32, (ReturnNode (Some 27) None), VoidStamp),
  (33, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (34, (IntegerEqualsNode 1 33), VoidStamp),
  (35, (BeginNode 40), VoidStamp),
  (36, (BeginNode 38), VoidStamp),
  (37, (IfNode 34 36 35), VoidStamp),
  (38, (ReturnNode (Some 33) None), VoidStamp),
  (39, (ConstantNode (new_int 32 (375))), IntegerStamp 32 (375) (375)),
  (40, (ReturnNode (Some 39) None), VoidStamp)
  ]"
value "static_test unit_BC_iconst_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_iconst_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_BC_iconst_test  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_iconst_test  [(new_int 32 (3))] (new_int 32 (3))"

value "static_test unit_BC_iconst_test  [(new_int 32 (4))] (new_int 32 (4))"

value "static_test unit_BC_iconst_test  [(new_int 32 (5))] (new_int 32 (5))"

value "static_test unit_BC_iconst_test  [(new_int 32 (6))] (new_int 32 (375))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_idiv2;.BC_idiv2_test*)
definition unit_BC_idiv2_test :: IRGraph where
  "unit_BC_idiv2_test = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv2_test  [(new_int 32 (-2147483648)), (new_int 32 (-1))] (new_int 32 (-2147483648))"

value "static_test unit_BC_idiv2_test  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (-2147483648))"


(* Lorg/graalvm/compiler/jtt/except/BC_idiv2;.BC_idiv2_test*)
definition unit_BC_idiv2_test__2 :: IRGraph where
  "unit_BC_idiv2_test__2 = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv2_test__2  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_idiv_16;.BC_idiv_16_test*)
definition unit_BC_idiv_16_test :: IRGraph where
  "unit_BC_idiv_16_test = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (IntegerEqualsNode 1 4), VoidStamp),
  (6, (BeginNode 18), VoidStamp),
  (7, (BeginNode 17), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (10, (ConstantNode (new_int 32 (31))), IntegerStamp 32 (31) (31)),
  (11, (RightShiftNode 2 10), IntegerStamp 32 (-1) (0)),
  (12, (ConstantNode (new_int 32 (28))), IntegerStamp 32 (28) (28)),
  (13, (UnsignedRightShiftNode 11 12), IntegerStamp 32 (0) (15)),
  (14, (AddNode 13 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (15, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (16, (RightShiftNode 14 15), IntegerStamp 32 (-134217728) (134217727)),
  (17, (ReturnNode (Some 16) None), VoidStamp),
  (18, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_16_test  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (0)), (new_int 32 (16))] (new_int 32 (1))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (0)), (new_int 32 (17))] (new_int 32 (1))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (0)), (new_int 32 (-16))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (0)), (new_int 32 (-17))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (0)), (new_int 32 (-1024))] (new_int 32 (-64))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (1)), (new_int 32 (16))] (new_int 32 (1))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (1)), (new_int 32 (17))] (new_int 32 (1))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (1)), (new_int 32 (-16))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (1)), (new_int 32 (-17))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_16_test  [(new_int 32 (1)), (new_int 32 (-1024))] (new_int 32 (-64))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_idiv_4;.BC_idiv_4_test*)
definition unit_BC_idiv_4_test :: IRGraph where
  "unit_BC_idiv_4_test = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (4, (ConstantNode (new_int 32 (31))), IntegerStamp 32 (31) (31)),
  (5, (RightShiftNode 1 4), IntegerStamp 32 (-1) (0)),
  (6, (ConstantNode (new_int 32 (30))), IntegerStamp 32 (30) (30)),
  (7, (UnsignedRightShiftNode 5 6), IntegerStamp 32 (0) (3)),
  (8, (AddNode 7 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (10, (RightShiftNode 8 9), IntegerStamp 32 (-536870912) (536870911)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_4_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_idiv_4_test  [(new_int 32 (4))] (new_int 32 (1))"

value "static_test unit_BC_idiv_4_test  [(new_int 32 (5))] (new_int 32 (1))"

value "static_test unit_BC_idiv_4_test  [(new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_idiv_4_test  [(new_int 32 (-4))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_4_test  [(new_int 32 (-5))] (new_int 32 (-1))"

value "static_test unit_BC_idiv_4_test  [(new_int 32 (-256))] (new_int 32 (-64))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_idiv_overflow;.BC_idiv_overflow_test*)
definition unit_BC_idiv_overflow_test :: IRGraph where
  "unit_BC_idiv_overflow_test = irgraph [
  (0, (StartNode (Some 3) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (OrNode 2 4), IntegerStamp 32 (-2147483647) (2147483647)),
  (6, (SignedDivNode 6 1 5 None None 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_overflow_test  [(new_int 32 (-2147483648)), (new_int 32 (-1))] (new_int 32 (-2147483648))"

value "static_test unit_BC_idiv_overflow_test  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (-2147483648))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_idiv;.BC_idiv_test*)
definition unit_BC_idiv_test :: IRGraph where
  "unit_BC_idiv_test = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (0))"

value "static_test unit_BC_idiv_test  [(new_int 32 (2)), (new_int 32 (-1))] (new_int 32 (-2))"

value "static_test unit_BC_idiv_test  [(new_int 32 (256)), (new_int 32 (4))] (new_int 32 (64))"

value "static_test unit_BC_idiv_test  [(new_int 32 (135)), (new_int 32 (7))] (new_int 32 (19))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_idiv;.BC_idiv_testStrictlyPositive*)
definition unit_BC_idiv_testStrictlyPositive :: IRGraph where
  "unit_BC_idiv_testStrictlyPositive = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (64))), IntegerStamp 32 (64) (64)),
  (4, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (5, (AndNode 1 4), IntegerStamp 32 (0) (7)),
  (6, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (AddNode 5 6), IntegerStamp 32 (1) (8)),
  (8, (SignedDivNode 8 3 7 None None 9), IntegerStamp 32 (8) (64)),
  (9, (ReturnNode (Some 8) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_testStrictlyPositive  [(new_int 32 (6))] (new_int 32 (9))"


(* Lorg/graalvm/compiler/jtt/except/BC_idiv;.BC_idiv_test*)
definition unit_BC_idiv_test__2 :: IRGraph where
  "unit_BC_idiv_test__2 = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_idiv_test__2  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq_2;.BC_ifeq_2_test*)
definition unit_BC_ifeq_2_test :: IRGraph where
  "unit_BC_ifeq_2_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (ConditionalNode 4 5 3), IntegerStamp 32 (0) (1)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_BC_ifeq_2_test  [(new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_BC_ifeq_2_test  [(new_int 32 (1))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq_3;.BC_ifeq_3_test*)
definition unit_BC_ifeq_3_test :: IRGraph where
  "unit_BC_ifeq_3_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (ConditionalNode 4 3 5), IntegerStamp 32 (0) (1)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_BC_ifeq_3_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_ifeq_3_test  [(new_int 32 (1))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq;.BC_ifeq_test*)
definition unit_BC_ifeq_test :: IRGraph where
  "unit_BC_ifeq_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 32 (-1) (1)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 22), VoidStamp),
  (17, (BeginNode 24), VoidStamp),
  (18, (IfNode 4 17 16), VoidStamp),
  (19, (AddNode 14 10), IntegerStamp 32 (-2) (0)),
  (21, (AddNode 14 8), IntegerStamp 32 (0) (2)),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode [22, 24] (Some 26) 27), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (ValuePhiNode 25 [19, 21] 23), IntegerStamp 32 (-2) (2)),
  (26, (FrameState [] None None None), IllegalStamp),
  (27, (ReturnNode (Some 25) None), VoidStamp)
  ]"
value "static_test unit_BC_ifeq_test  [(new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_BC_ifeq_test  [(new_int 32 (1))] (new_int 32 (-2))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq;.BC_ifeq_testCondb*)
definition unit_BC_ifeq_testCondb :: IRGraph where
  "unit_BC_ifeq_testCondb = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (4, (SignExtendNode 8 32 3), IntegerStamp 32 (-128) (127)),
  (5, (ConstantNode (new_int 32 (255))), IntegerStamp 32 (255) (255)),
  (6, (ZeroExtendNode 8 32 3), IntegerStamp 32 (0) (255)),
  (7, (IntegerEqualsNode 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (ConditionalNode 7 8 9), IntegerStamp 32 (0) (1)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_BC_ifeq_testCondb  [(new_int 32 (255))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq;.BC_ifeq_testCondc*)
definition unit_BC_ifeq_testCondc :: IRGraph where
  "unit_BC_ifeq_testCondc = irgraph [
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
value "static_test unit_BC_ifeq_testCondc  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifeq;.BC_ifeq_testConds*)
definition unit_BC_ifeq_testConds :: IRGraph where
  "unit_BC_ifeq_testConds = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (SignExtendNode 16 32 3), IntegerStamp 32 (-32768) (32767)),
  (5, (ConstantNode (new_int 32 (65535))), IntegerStamp 32 (65535) (65535)),
  (6, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (7, (IntegerEqualsNode 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (10, (ConditionalNode 7 8 9), IntegerStamp 32 (0) (1)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_BC_ifeq_testConds  [(new_int 32 (65535))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifge_2;.BC_ifge_2_test*)
definition unit_BC_ifge_2_test :: IRGraph where
  "unit_BC_ifge_2_test = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (7, (ConditionalNode 4 5 6), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_BC_ifge_2_test  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_BC_ifge_2_test  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_BC_ifge_2_test  [(new_int 32 (1)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_BC_ifge_2_test  [(new_int 32 (0)), (new_int 32 (-100))] (new_int 32 (1))"

value "static_test unit_BC_ifge_2_test  [(new_int 32 (-1)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_ifge_2_test  [(new_int 32 (-12)), (new_int 32 (-12))] (new_int 32 (1))"

end
