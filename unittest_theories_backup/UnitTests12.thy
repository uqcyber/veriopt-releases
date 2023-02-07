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


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ishr;.BC_ishr_test*)
definition unit_BC_ishr_test :: IRGraph where
  "unit_BC_ishr_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (RightShiftNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_ishr_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (0))"

value "static_test unit_BC_ishr_test  [(new_int 32 (67)), (new_int 32 (2))] (new_int 32 (16))"

value "static_test unit_BC_ishr_test  [(new_int 32 (31)), (new_int 32 (1))] (new_int 32 (15))"

value "static_test unit_BC_ishr_test  [(new_int 32 (6)), (new_int 32 (4))] (new_int 32 (0))"

value "static_test unit_BC_ishr_test  [(new_int 32 (-2147483648)), (new_int 32 (16))] (new_int 32 (-32768))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_isub;.BC_isub_test*)
definition unit_BC_isub_test :: IRGraph where
  "unit_BC_isub_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SubNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_isub_test  [(new_int 32 (1)), (new_int 32 (-2))] (new_int 32 (3))"

value "static_test unit_BC_isub_test  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (-1))"

value "static_test unit_BC_isub_test  [(new_int 32 (33)), (new_int 32 (-67))] (new_int 32 (100))"

value "static_test unit_BC_isub_test  [(new_int 32 (1)), (new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_BC_isub_test  [(new_int 32 (-2147483648)), (new_int 32 (-1))] (new_int 32 (-2147483647))"

value "static_test unit_BC_isub_test  [(new_int 32 (2147483647)), (new_int 32 (-1))] (new_int 32 (-2147483648))"

value "static_test unit_BC_isub_test  [(new_int 32 (-2147483647)), (new_int 32 (2))] (new_int 32 (2147483647))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iushr;.BC_iushr_test*)
definition unit_BC_iushr_test :: IRGraph where
  "unit_BC_iushr_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (UnsignedRightShiftNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iushr_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (0))"

value "static_test unit_BC_iushr_test  [(new_int 32 (67)), (new_int 32 (2))] (new_int 32 (16))"

value "static_test unit_BC_iushr_test  [(new_int 32 (31)), (new_int 32 (1))] (new_int 32 (15))"

value "static_test unit_BC_iushr_test  [(new_int 32 (6)), (new_int 32 (4))] (new_int 32 (0))"

value "static_test unit_BC_iushr_test  [(new_int 32 (-2147483648)), (new_int 32 (16))] (new_int 32 (32768))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ixor;.BC_ixor_test*)
definition unit_BC_ixor_test :: IRGraph where
  "unit_BC_ixor_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (XorNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_ixor_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (3))"

value "static_test unit_BC_ixor_test  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_ixor_test  [(new_int 32 (31)), (new_int 32 (63))] (new_int 32 (32))"

value "static_test unit_BC_ixor_test  [(new_int 32 (6)), (new_int 32 (4))] (new_int 32 (2))"

value "static_test unit_BC_ixor_test  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (-2147483647))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_l2i;.BC_l2i_test*)
definition unit_BC_l2i_test :: IRGraph where
  "unit_BC_l2i_test = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 64 32 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_BC_l2i_test  [(IntVal 64 (1))] (new_int 32 (1))"

value "static_test unit_BC_l2i_test  [(IntVal 64 (2))] (new_int 32 (2))"

value "static_test unit_BC_l2i_test  [(IntVal 64 (3))] (new_int 32 (3))"

value "static_test unit_BC_l2i_test  [(IntVal 64 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_l2i_test  [(IntVal 64 (-2147483647))] (new_int 32 (-2147483647))"

value "static_test unit_BC_l2i_test  [(IntVal 64 (-2147483648))] (new_int 32 (-2147483648))"

value "static_test unit_BC_l2i_test  [(IntVal 64 (2147483647))] (new_int 32 (2147483647))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ladd2;.BC_ladd2_test*)
definition unit_BC_ladd2_test :: IRGraph where
  "unit_BC_ladd2_test = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignExtendNode 32 64 1), IntegerStamp 64 (-2147483648) (2147483647)),
  (5, (SignExtendNode 32 64 2), IntegerStamp 64 (-2147483648) (2147483647)),
  (6, (AddNode 4 5), IntegerStamp 64 (-4294967296) (4294967294)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_BC_ladd2_test  [(new_int 32 (1)), (new_int 32 (2))] (IntVal 64 (3))"

value "static_test unit_BC_ladd2_test  [(new_int 32 (0)), (new_int 32 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_ladd2_test  [(new_int 32 (33)), (new_int 32 (67))] (IntVal 64 (100))"

value "static_test unit_BC_ladd2_test  [(new_int 32 (1)), (new_int 32 (-1))] (IntVal 64 (0))"

value "static_test unit_BC_ladd2_test  [(new_int 32 (-2147483648)), (new_int 32 (1))] (IntVal 64 (-2147483647))"

value "static_test unit_BC_ladd2_test  [(new_int 32 (2147483647)), (new_int 32 (1))] (IntVal 64 (2147483648))"

value "static_test unit_BC_ladd2_test  [(new_int 32 (-2147483647)), (new_int 32 (-2))] (IntVal 64 (-2147483649))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ladd;.BC_ladd_test*)
definition unit_BC_ladd_test :: IRGraph where
  "unit_BC_ladd_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (AddNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_ladd_test  [(IntVal 64 (1)), (IntVal 64 (2))] (IntVal 64 (3))"

value "static_test unit_BC_ladd_test  [(IntVal 64 (0)), (IntVal 64 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_ladd_test  [(IntVal 64 (33)), (IntVal 64 (67))] (IntVal 64 (100))"

value "static_test unit_BC_ladd_test  [(IntVal 64 (1)), (IntVal 64 (-1))] (IntVal 64 (0))"

value "static_test unit_BC_ladd_test  [(IntVal 64 (-2147483648)), (IntVal 64 (1))] (IntVal 64 (-2147483647))"

value "static_test unit_BC_ladd_test  [(IntVal 64 (2147483647)), (IntVal 64 (1))] (IntVal 64 (2147483648))"

value "static_test unit_BC_ladd_test  [(IntVal 64 (-2147483647)), (IntVal 64 (-2))] (IntVal 64 (-2147483649))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_land;.BC_land_test*)
definition unit_BC_land_test :: IRGraph where
  "unit_BC_land_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (AndNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_land_test  [(IntVal 64 (1)), (IntVal 64 (2))] (IntVal 64 (0))"

value "static_test unit_BC_land_test  [(IntVal 64 (0)), (IntVal 64 (-1))] (IntVal 64 (0))"

value "static_test unit_BC_land_test  [(IntVal 64 (31)), (IntVal 64 (63))] (IntVal 64 (31))"

value "static_test unit_BC_land_test  [(IntVal 64 (6)), (IntVal 64 (4))] (IntVal 64 (4))"

value "static_test unit_BC_land_test  [(IntVal 64 (-2147483648)), (IntVal 64 (1))] (IntVal 64 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ldc_01;.BC_ldc_01_test*)
definition unit_BC_ldc_01_test :: IRGraph where
  "unit_BC_ldc_01_test = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (-123))), IntegerStamp 32 (-123) (-123)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_BC_ldc_01_test  [] (new_int 32 (-123))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ldc_03;.BC_ldc_03_test*)
definition unit_BC_ldc_03_test :: IRGraph where
  "unit_BC_ldc_03_test = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (-123))), IntegerStamp 64 (-123) (-123)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_BC_ldc_03_test  [] (IntVal 64 (-123))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ldiv2;.BC_ldiv2_test*)
definition unit_BC_ldiv2_test :: Program where
  "unit_BC_ldiv2_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_ldiv2.test(JJ)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_ldiv2.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (-9223372036854775808))), IntegerStamp 64 (-9223372036854775808) (-9223372036854775808)),
  (3, (StoreFieldNode 3 ''org.graalvm.compiler.jtt.bytecode.BC_ldiv2::MIN'' 2 (Some 4) None 6), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ConstantNode (IntVal 64 (9223372036854775807))), IntegerStamp 64 (9223372036854775807) (9223372036854775807)),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.jtt.bytecode.BC_ldiv2::MAX'' 5 (Some 7) None 8), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_ldiv2.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_BC_ldiv2_test ''org.graalvm.compiler.jtt.bytecode.BC_ldiv2.test(JJ)J'' [(IntVal 64 (-9223372036854775808)), (IntVal 64 (-1))] (IntVal 64 (-9223372036854775808))"

value "program_test unit_BC_ldiv2_test ''org.graalvm.compiler.jtt.bytecode.BC_ldiv2.test(JJ)J'' [(IntVal 64 (-9223372036854775808)), (IntVal 64 (1))] (IntVal 64 (-9223372036854775808))"

value "program_test unit_BC_ldiv2_test ''org.graalvm.compiler.jtt.bytecode.BC_ldiv2.test(JJ)J'' [(IntVal 64 (-9223372036854775808)), (IntVal 64 (9223372036854775807))] (IntVal 64 (-1))"


(* Lorg/graalvm/compiler/jtt/except/BC_ldiv2;.BC_ldiv2_test*)
definition unit_BC_ldiv2_test__2 :: IRGraph where
  "unit_BC_ldiv2_test__2 = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_ldiv2_test__2  [(IntVal 64 (1)), (IntVal 64 (2))] (IntVal 64 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ldiv3;.BC_ldiv3_test*)
definition unit_BC_ldiv3_test :: Program where
  "unit_BC_ldiv3_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3.test(JJ)J'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal 64 (7))), IntegerStamp 64 (7) (7)),
  (3, (StoreFieldNode 3 ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3::PLUS7'' 2 (Some 4) None 6), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ConstantNode (IntVal 64 (3))), IntegerStamp 64 (3) (3)),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3::PLUS3'' 5 (Some 7) None 9), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (ConstantNode (IntVal 64 (-7))), IntegerStamp 64 (-7) (-7)),
  (9, (StoreFieldNode 9 ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3::MIN7'' 8 (Some 10) None 12), VoidStamp),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ConstantNode (IntVal 64 (-3))), IntegerStamp 64 (-3) (-3)),
  (12, (StoreFieldNode 12 ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3::MIN3'' 11 (Some 13) None 14), VoidStamp),
  (13, (FrameState [] None None None), IllegalStamp),
  (14, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_BC_ldiv3_test ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3.test(JJ)J'' [(IntVal 64 (7)), (IntVal 64 (2))] (IntVal 64 (3))"

value "program_test unit_BC_ldiv3_test ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3.test(JJ)J'' [(IntVal 64 (3)), (IntVal 64 (2))] (IntVal 64 (1))"

value "program_test unit_BC_ldiv3_test ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3.test(JJ)J'' [(IntVal 64 (-7)), (IntVal 64 (2))] (IntVal 64 (-3))"

value "program_test unit_BC_ldiv3_test ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3.test(JJ)J'' [(IntVal 64 (-3)), (IntVal 64 (2))] (IntVal 64 (-1))"

value "program_test unit_BC_ldiv3_test ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3.test(JJ)J'' [(IntVal 64 (7)), (IntVal 64 (-4))] (IntVal 64 (-1))"

value "program_test unit_BC_ldiv3_test ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3.test(JJ)J'' [(IntVal 64 (3)), (IntVal 64 (-4))] (IntVal 64 (0))"

value "program_test unit_BC_ldiv3_test ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3.test(JJ)J'' [(IntVal 64 (-7)), (IntVal 64 (-4))] (IntVal 64 (1))"

value "program_test unit_BC_ldiv3_test ''org.graalvm.compiler.jtt.bytecode.BC_ldiv3.test(JJ)J'' [(IntVal 64 (-3)), (IntVal 64 (-4))] (IntVal 64 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_ldiv_16;.BC_ldiv_16_test*)
definition unit_BC_ldiv_16_test :: IRGraph where
  "unit_BC_ldiv_16_test = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (16))), IntegerStamp 64 (16) (16)),
  (4, (ConstantNode (new_int 32 (63))), IntegerStamp 32 (63) (63)),
  (5, (RightShiftNode 1 4), IntegerStamp 64 (-1) (0)),
  (6, (ConstantNode (new_int 32 (60))), IntegerStamp 32 (60) (60)),
  (7, (UnsignedRightShiftNode 5 6), IntegerStamp 64 (0) (15)),
  (8, (AddNode 7 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (9, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (10, (RightShiftNode 8 9), IntegerStamp 64 (-576460752303423488) (576460752303423487)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_BC_ldiv_16_test  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_BC_ldiv_16_test  [(IntVal 64 (16))] (IntVal 64 (1))"

value "static_test unit_BC_ldiv_16_test  [(IntVal 64 (17))] (IntVal 64 (1))"

value "static_test unit_BC_ldiv_16_test  [(IntVal 64 (-1))] (IntVal 64 (0))"

value "static_test unit_BC_ldiv_16_test  [(IntVal 64 (-16))] (IntVal 64 (-1))"

value "static_test unit_BC_ldiv_16_test  [(IntVal 64 (-17))] (IntVal 64 (-1))"

value "static_test unit_BC_ldiv_16_test  [(IntVal 64 (-1024))] (IntVal 64 (-64))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_ldiv_4;.BC_ldiv_4_test*)
definition unit_BC_ldiv_4_test :: IRGraph where
  "unit_BC_ldiv_4_test = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (4))), IntegerStamp 64 (4) (4)),
  (4, (ConstantNode (new_int 32 (63))), IntegerStamp 32 (63) (63)),
  (5, (RightShiftNode 1 4), IntegerStamp 64 (-1) (0)),
  (6, (ConstantNode (new_int 32 (62))), IntegerStamp 32 (62) (62)),
  (7, (UnsignedRightShiftNode 5 6), IntegerStamp 64 (0) (3)),
  (8, (AddNode 7 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (9, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (10, (RightShiftNode 8 9), IntegerStamp 64 (-2305843009213693952) (2305843009213693951)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_BC_ldiv_4_test  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_BC_ldiv_4_test  [(IntVal 64 (4))] (IntVal 64 (1))"

value "static_test unit_BC_ldiv_4_test  [(IntVal 64 (5))] (IntVal 64 (1))"

value "static_test unit_BC_ldiv_4_test  [(IntVal 64 (-1))] (IntVal 64 (0))"

value "static_test unit_BC_ldiv_4_test  [(IntVal 64 (-4))] (IntVal 64 (-1))"

value "static_test unit_BC_ldiv_4_test  [(IntVal 64 (-5))] (IntVal 64 (-1))"

value "static_test unit_BC_ldiv_4_test  [(IntVal 64 (-256))] (IntVal 64 (-64))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ldiv_overflow;.BC_ldiv_overflow_test*)
definition unit_BC_ldiv_overflow_test :: IRGraph where
  "unit_BC_ldiv_overflow_test = irgraph [
  (0, (StartNode (Some 3) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (IntVal 64 (1))), IntegerStamp 64 (1) (1)),
  (5, (OrNode 2 4), IntegerStamp 64 (-9223372036854775807) (9223372036854775807)),
  (6, (SignedDivNode 6 1 5 None None 7), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_BC_ldiv_overflow_test  [(IntVal 64 (-9223372036854775808)), (IntVal 64 (-1))] (IntVal 64 (-9223372036854775808))"

value "static_test unit_BC_ldiv_overflow_test  [(IntVal 64 (-9223372036854775808)), (IntVal 64 (1))] (IntVal 64 (-9223372036854775808))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ldiv;.BC_ldiv_test*)
definition unit_BC_ldiv_test :: IRGraph where
  "unit_BC_ldiv_test = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_ldiv_test  [(IntVal 64 (1)), (IntVal 64 (2))] (IntVal 64 (0))"

value "static_test unit_BC_ldiv_test  [(IntVal 64 (2)), (IntVal 64 (-1))] (IntVal 64 (-2))"

value "static_test unit_BC_ldiv_test  [(IntVal 64 (256)), (IntVal 64 (4))] (IntVal 64 (64))"

value "static_test unit_BC_ldiv_test  [(IntVal 64 (135)), (IntVal 64 (7))] (IntVal 64 (19))"


(* Lorg/graalvm/compiler/jtt/except/BC_ldiv;.BC_ldiv_test*)
definition unit_BC_ldiv_test__2 :: IRGraph where
  "unit_BC_ldiv_test__2 = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedDivNode 4 1 2 None None 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_ldiv_test__2  [(IntVal 64 (1)), (IntVal 64 (2))] (IntVal 64 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lload_01;.BC_lload_01_test*)
definition unit_BC_lload_01_test :: IRGraph where
  "unit_BC_lload_01_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (ObjRef None)), ObjectStamp ''null'' False False True),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ConstantNode (IntVal 64 (1))), IntegerStamp 64 (1) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (ConstantNode (IntVal 64 (0))), IntegerStamp 64 (0) (0)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_BC_lload_01_test  [(new_int 32 (1))] (IntVal 64 (0))"

value "static_test unit_BC_lload_01_test  [(new_int 32 (-3))] (IntVal 64 (0))"

value "static_test unit_BC_lload_01_test  [(new_int 32 (100))] (IntVal 64 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lload_0;.BC_lload_0_test*)
definition unit_BC_lload_0_test :: IRGraph where
  "unit_BC_lload_0_test = irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ReturnNode (Some 1) None), VoidStamp)
  ]"
value "static_test unit_BC_lload_0_test  [(IntVal 64 (1))] (IntVal 64 (1))"

value "static_test unit_BC_lload_0_test  [(IntVal 64 (-3))] (IntVal 64 (-3))"

value "static_test unit_BC_lload_0_test  [(IntVal 64 (10000))] (IntVal 64 (10000))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lload_1;.BC_lload_1_test*)
definition unit_BC_lload_1_test :: IRGraph where
  "unit_BC_lload_1_test = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_BC_lload_1_test  [(new_int 32 (1)), (IntVal 64 (1))] (IntVal 64 (1))"

value "static_test unit_BC_lload_1_test  [(new_int 32 (1)), (IntVal 64 (-3))] (IntVal 64 (-3))"

value "static_test unit_BC_lload_1_test  [(new_int 32 (1)), (IntVal 64 (10000))] (IntVal 64 (10000))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lload_2;.BC_lload_2_test*)
definition unit_BC_lload_2_test :: IRGraph where
  "unit_BC_lload_2_test = irgraph [
  (0, (StartNode (Some 4) 5), VoidStamp),
  (3, (ParameterNode 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_BC_lload_2_test  [(new_int 32 (1)), (new_int 32 (1)), (IntVal 64 (1))] (IntVal 64 (1))"

value "static_test unit_BC_lload_2_test  [(new_int 32 (1)), (new_int 32 (1)), (IntVal 64 (-3))] (IntVal 64 (-3))"

value "static_test unit_BC_lload_2_test  [(new_int 32 (1)), (new_int 32 (1)), (IntVal 64 (10000))] (IntVal 64 (10000))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lload_3;.BC_lload_3_test*)
definition unit_BC_lload_3_test :: IRGraph where
  "unit_BC_lload_3_test = irgraph [
  (0, (StartNode (Some 5) 6), VoidStamp),
  (4, (ParameterNode 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lload_3_test  [(new_int 32 (1)), (new_int 32 (1)), (new_int 32 (1)), (IntVal 64 (1))] (IntVal 64 (1))"

value "static_test unit_BC_lload_3_test  [(new_int 32 (1)), (new_int 32 (1)), (new_int 32 (1)), (IntVal 64 (-3))] (IntVal 64 (-3))"

value "static_test unit_BC_lload_3_test  [(new_int 32 (1)), (new_int 32 (1)), (new_int 32 (1)), (IntVal 64 (10000))] (IntVal 64 (10000))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_lmul_16;.BC_lmul_16_test*)
definition unit_BC_lmul_16_test :: IRGraph where
  "unit_BC_lmul_16_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (16))), IntegerStamp 64 (16) (16)),
  (4, (MulNode 1 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lmul_16_test  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_BC_lmul_16_test  [(IntVal 64 (16))] (IntVal 64 (256))"

value "static_test unit_BC_lmul_16_test  [(IntVal 64 (17))] (IntVal 64 (272))"

value "static_test unit_BC_lmul_16_test  [(IntVal 64 (-1))] (IntVal 64 (-16))"

value "static_test unit_BC_lmul_16_test  [(IntVal 64 (-16))] (IntVal 64 (-256))"

value "static_test unit_BC_lmul_16_test  [(IntVal 64 (-17))] (IntVal 64 (-272))"

value "static_test unit_BC_lmul_16_test  [(IntVal 64 (-1024))] (IntVal 64 (-16384))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_lmul_4;.BC_lmul_4_test*)
definition unit_BC_lmul_4_test :: IRGraph where
  "unit_BC_lmul_4_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (4))), IntegerStamp 64 (4) (4)),
  (4, (MulNode 1 3), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lmul_4_test  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_BC_lmul_4_test  [(IntVal 64 (4))] (IntVal 64 (16))"

value "static_test unit_BC_lmul_4_test  [(IntVal 64 (5))] (IntVal 64 (20))"

value "static_test unit_BC_lmul_4_test  [(IntVal 64 (-1))] (IntVal 64 (-4))"

value "static_test unit_BC_lmul_4_test  [(IntVal 64 (-4))] (IntVal 64 (-16))"

value "static_test unit_BC_lmul_4_test  [(IntVal 64 (-5))] (IntVal 64 (-20))"

value "static_test unit_BC_lmul_4_test  [(IntVal 64 (-256))] (IntVal 64 (-1024))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lmul;.BC_lmul_test*)
definition unit_BC_lmul_test :: IRGraph where
  "unit_BC_lmul_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (MulNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lmul_test  [(IntVal 64 (1)), (IntVal 64 (2))] (IntVal 64 (2))"

value "static_test unit_BC_lmul_test  [(IntVal 64 (0)), (IntVal 64 (-1))] (IntVal 64 (0))"

value "static_test unit_BC_lmul_test  [(IntVal 64 (33)), (IntVal 64 (67))] (IntVal 64 (2211))"

value "static_test unit_BC_lmul_test  [(IntVal 64 (1)), (IntVal 64 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_lmul_test  [(IntVal 64 (-2147483648)), (IntVal 64 (1))] (IntVal 64 (-2147483648))"

value "static_test unit_BC_lmul_test  [(IntVal 64 (2147483647)), (IntVal 64 (-1))] (IntVal 64 (-2147483647))"

value "static_test unit_BC_lmul_test  [(IntVal 64 (-2147483648)), (IntVal 64 (-1))] (IntVal 64 (2147483648))"

value "static_test unit_BC_lmul_test  [(IntVal 64 (1000000)), (IntVal 64 (1000000))] (IntVal 64 (1000000000000))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lneg;.BC_lneg_test*)
definition unit_BC_lneg_test :: IRGraph where
  "unit_BC_lneg_test = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NegateNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_BC_lneg_test  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_BC_lneg_test  [(IntVal 64 (-1))] (IntVal 64 (1))"

value "static_test unit_BC_lneg_test  [(IntVal 64 (7263))] (IntVal 64 (-7263))"

value "static_test unit_BC_lneg_test  [(IntVal 64 (-2147483648))] (IntVal 64 (2147483648))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lor;.BC_lor_test*)
definition unit_BC_lor_test :: IRGraph where
  "unit_BC_lor_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (OrNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lor_test  [(IntVal 64 (1)), (IntVal 64 (2))] (IntVal 64 (3))"

value "static_test unit_BC_lor_test  [(IntVal 64 (0)), (IntVal 64 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_lor_test  [(IntVal 64 (31)), (IntVal 64 (63))] (IntVal 64 (63))"

value "static_test unit_BC_lor_test  [(IntVal 64 (6)), (IntVal 64 (4))] (IntVal 64 (6))"

value "static_test unit_BC_lor_test  [(IntVal 64 (-2147483648)), (IntVal 64 (1))] (IntVal 64 (-2147483647))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lrem2;.BC_lrem2_test*)
definition unit_BC_lrem2_test :: IRGraph where
  "unit_BC_lrem2_test = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedRemNode 4 1 2 None None 5), IntegerStamp 64 (-9223372036854775807) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lrem2_test  [(IntVal 64 (-9223372036854775808)), (IntVal 64 (-1))] (IntVal 64 (0))"

value "static_test unit_BC_lrem2_test  [(IntVal 64 (-9223372036854775808)), (IntVal 64 (1))] (IntVal 64 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lrem;.BC_lrem_test*)
definition unit_BC_lrem_test :: IRGraph where
  "unit_BC_lrem_test = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedRemNode 4 1 2 None None 5), IntegerStamp 64 (-9223372036854775807) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lrem_test  [(IntVal 64 (1)), (IntVal 64 (2))] (IntVal 64 (1))"

value "static_test unit_BC_lrem_test  [(IntVal 64 (2)), (IntVal 64 (-1))] (IntVal 64 (0))"

value "static_test unit_BC_lrem_test  [(IntVal 64 (256)), (IntVal 64 (4))] (IntVal 64 (0))"

value "static_test unit_BC_lrem_test  [(IntVal 64 (135)), (IntVal 64 (7))] (IntVal 64 (2))"


(* Lorg/graalvm/compiler/jtt/except/BC_lrem;.BC_lrem_test*)
definition unit_BC_lrem_test__2 :: IRGraph where
  "unit_BC_lrem_test__2 = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedRemNode 4 1 2 None None 5), IntegerStamp 64 (-9223372036854775807) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lrem_test__2  [(IntVal 64 (1)), (IntVal 64 (2))] (IntVal 64 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lreturn;.BC_lreturn_test*)
definition unit_BC_lreturn_test :: IRGraph where
  "unit_BC_lreturn_test = irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ReturnNode (Some 1) None), VoidStamp)
  ]"
value "static_test unit_BC_lreturn_test  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_BC_lreturn_test  [(IntVal 64 (1))] (IntVal 64 (1))"

value "static_test unit_BC_lreturn_test  [(IntVal 64 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_lreturn_test  [(IntVal 64 (256))] (IntVal 64 (256))"

value "static_test unit_BC_lreturn_test  [(IntVal 64 (1000000000000))] (IntVal 64 (1000000000000))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lshl;.BC_lshl_test*)
definition unit_BC_lshl_test :: IRGraph where
  "unit_BC_lshl_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (LeftShiftNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lshl_test  [(IntVal 64 (1)), (new_int 32 (2))] (IntVal 64 (4))"

value "static_test unit_BC_lshl_test  [(IntVal 64 (0)), (new_int 32 (-1))] (IntVal 64 (0))"

value "static_test unit_BC_lshl_test  [(IntVal 64 (31)), (new_int 32 (1))] (IntVal 64 (62))"

value "static_test unit_BC_lshl_test  [(IntVal 64 (6)), (new_int 32 (4))] (IntVal 64 (96))"

value "static_test unit_BC_lshl_test  [(IntVal 64 (-2147483648)), (new_int 32 (1))] (IntVal 64 (-4294967296))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lshr02;.BC_lshr02_test0*)
definition unit_BC_lshr02_test0 :: IRGraph where
  "unit_BC_lshr02_test0 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (32))), IntegerStamp 32 (32) (32)),
  (4, (RightShiftNode 1 3), IntegerStamp 64 (-2147483648) (2147483647)),
  (5, (ConstantNode (new_int 32 (63))), IntegerStamp 32 (63) (63)),
  (6, (RightShiftNode 1 5), IntegerStamp 64 (-1) (0)),
  (7, (ReturnNode (Some 6) None), VoidStamp)
  ]"
value "static_test unit_BC_lshr02_test0  [(IntVal 64 (1))] (IntVal 64 (0))"

value "static_test unit_BC_lshr02_test0  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_BC_lshr02_test0  [(IntVal 64 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_lshr02_test0  [(IntVal 64 (9223372036854775807))] (IntVal 64 (0))"

value "static_test unit_BC_lshr02_test0  [(IntVal 64 (-9223372036854775808))] (IntVal 64 (-1))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_lshr_C16;.BC_lshr_C16_test*)
definition unit_BC_lshr_C16_test :: IRGraph where
  "unit_BC_lshr_C16_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (4, (RightShiftNode 1 3), IntegerStamp 64 (-140737488355328) (140737488355327)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lshr_C16_test  [(IntVal 64 (87224824140))] (IntVal 64 (1330945))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_lshr_C24;.BC_lshr_C24_test*)
definition unit_BC_lshr_C24_test :: IRGraph where
  "unit_BC_lshr_C24_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (24))), IntegerStamp 32 (24) (24)),
  (4, (RightShiftNode 1 3), IntegerStamp 64 (-549755813888) (549755813887)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lshr_C24_test  [(IntVal 64 (87224824140))] (IntVal 64 (5199))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_lshr_C32;.BC_lshr_C32_test*)
definition unit_BC_lshr_C32_test :: IRGraph where
  "unit_BC_lshr_C32_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (32))), IntegerStamp 32 (32) (32)),
  (4, (RightShiftNode 1 3), IntegerStamp 64 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lshr_C32_test  [(IntVal 64 (87224824140))] (IntVal 64 (20))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lshr;.BC_lshr_test*)
definition unit_BC_lshr_test :: IRGraph where
  "unit_BC_lshr_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (RightShiftNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lshr_test  [(IntVal 64 (1)), (new_int 32 (2))] (IntVal 64 (0))"

value "static_test unit_BC_lshr_test  [(IntVal 64 (67)), (new_int 32 (2))] (IntVal 64 (16))"

value "static_test unit_BC_lshr_test  [(IntVal 64 (31)), (new_int 32 (1))] (IntVal 64 (15))"

value "static_test unit_BC_lshr_test  [(IntVal 64 (6)), (new_int 32 (4))] (IntVal 64 (0))"

value "static_test unit_BC_lshr_test  [(IntVal 64 (-2147483648)), (new_int 32 (16))] (IntVal 64 (-32768))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lsub;.BC_lsub_test*)
definition unit_BC_lsub_test :: IRGraph where
  "unit_BC_lsub_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SubNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lsub_test  [(IntVal 64 (1)), (IntVal 64 (-2))] (IntVal 64 (3))"

value "static_test unit_BC_lsub_test  [(IntVal 64 (0)), (IntVal 64 (1))] (IntVal 64 (-1))"

value "static_test unit_BC_lsub_test  [(IntVal 64 (33)), (IntVal 64 (-67))] (IntVal 64 (100))"

value "static_test unit_BC_lsub_test  [(IntVal 64 (1)), (IntVal 64 (1))] (IntVal 64 (0))"

value "static_test unit_BC_lsub_test  [(IntVal 64 (-2147483648)), (IntVal 64 (-1))] (IntVal 64 (-2147483647))"

value "static_test unit_BC_lsub_test  [(IntVal 64 (2147483647)), (IntVal 64 (-1))] (IntVal 64 (2147483648))"

value "static_test unit_BC_lsub_test  [(IntVal 64 (-2147483647)), (IntVal 64 (2))] (IntVal 64 (-2147483649))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lushr;.BC_lushr_test*)
definition unit_BC_lushr_test :: IRGraph where
  "unit_BC_lushr_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (UnsignedRightShiftNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lushr_test  [(IntVal 64 (1)), (new_int 32 (2))] (IntVal 64 (0))"

value "static_test unit_BC_lushr_test  [(IntVal 64 (67)), (new_int 32 (2))] (IntVal 64 (16))"

value "static_test unit_BC_lushr_test  [(IntVal 64 (31)), (new_int 32 (1))] (IntVal 64 (15))"

value "static_test unit_BC_lushr_test  [(IntVal 64 (6)), (new_int 32 (4))] (IntVal 64 (0))"

value "static_test unit_BC_lushr_test  [(IntVal 64 (-2147483648)), (new_int 32 (16))] (IntVal 64 (281474976677888))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_lxor;.BC_lxor_test*)
definition unit_BC_lxor_test :: IRGraph where
  "unit_BC_lxor_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (ParameterNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (XorNode 1 2), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_lxor_test  [(IntVal 64 (1)), (IntVal 64 (2))] (IntVal 64 (3))"

value "static_test unit_BC_lxor_test  [(IntVal 64 (0)), (IntVal 64 (-1))] (IntVal 64 (-1))"

value "static_test unit_BC_lxor_test  [(IntVal 64 (31)), (IntVal 64 (63))] (IntVal 64 (32))"

value "static_test unit_BC_lxor_test  [(IntVal 64 (6)), (IntVal 64 (4))] (IntVal 64 (2))"

value "static_test unit_BC_lxor_test  [(IntVal 64 (-2147483648)), (IntVal 64 (1))] (IntVal 64 (-2147483647))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_new;.BC_new_test*)
definition unit_BC_new_test :: IRGraph where
  "unit_BC_new_test = irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NewInstanceNode 3 ''org.graalvm.compiler.jtt.JTTTest$DummyTestClass'' None 5), ObjectStamp ''org.graalvm.compiler.jtt.JTTTest$DummyTestClass'' True True False),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode (Some 1) None), VoidStamp)
  ]"
value "static_test unit_BC_new_test  [(new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_putfield_01;.BC_putfield_01_test*)
definition unit_BC_putfield_01_test :: Program where
  "unit_BC_putfield_01_test = Map.empty (
  ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (LoadFieldNode 3 ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01::object'' None 4), ObjectStamp ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01$TestClass'' True False False),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01$TestClass::field'' 1 (Some 5) (Some 3) 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (LoadFieldNode 6 ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01::object'' None 7), ObjectStamp ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01$TestClass'' True False False),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01$TestClass::field'' (Some 6) 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01$TestClass'' None 4), ObjectStamp ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01$TestClass'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01::object'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_BC_putfield_01_test ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01.test(I)I'' [(new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_BC_putfield_01_test ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01.test(I)I'' [(new_int 32 (1))] (new_int 32 (1))"

value "program_test unit_BC_putfield_01_test ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01.test(I)I'' [(new_int 32 (2))] (new_int 32 (2))"

value "program_test unit_BC_putfield_01_test ''org.graalvm.compiler.jtt.bytecode.BC_putfield_01.test(I)I'' [(new_int 32 (-4))] (new_int 32 (-4))"

end
