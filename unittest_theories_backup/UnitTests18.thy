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


(* Lorg/graalvm/compiler/jtt/lang/Int_less03;.Int_less03_test*)
definition unit_Int_less03_test :: IRGraph where
  "unit_Int_less03_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (-5))), IntegerStamp 32 (-5) (-5)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 9), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (ReturnNode (Some 8) None), VoidStamp),
  (10, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_Int_less03_test  [(new_int 32 (-2147483648))] (new_int 32 (1))"

value "static_test unit_Int_less03_test  [(new_int 32 (-6))] (new_int 32 (1))"

value "static_test unit_Int_less03_test  [(new_int 32 (-5))] (new_int 32 (0))"

value "static_test unit_Int_less03_test  [(new_int 32 (-4))] (new_int 32 (0))"

value "static_test unit_Int_less03_test  [(new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_Int_less03_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Int_less03_test  [(new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_Int_less03_test  [(new_int 32 (2))] (new_int 32 (0))"

value "static_test unit_Int_less03_test  [(new_int 32 (2147483647))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/lang/Int_lessEqual01;.Int_lessEqual01_test*)
definition unit_Int_lessEqual01_test :: IRGraph where
  "unit_Int_lessEqual01_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (BeginNode 9), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ReturnNode (Some 4) None), VoidStamp),
  (10, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Int_lessEqual01_test  [(new_int 32 (-2147483648))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual01_test  [(new_int 32 (-2))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual01_test  [(new_int 32 (-1))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual01_test  [(new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual01_test  [(new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_Int_lessEqual01_test  [(new_int 32 (2))] (new_int 32 (0))"

value "static_test unit_Int_lessEqual01_test  [(new_int 32 (2147483647))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/lang/Int_lessEqual02;.Int_lessEqual02_test*)
definition unit_Int_lessEqual02_test :: IRGraph where
  "unit_Int_lessEqual02_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (4, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 10), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ReturnNode (Some 9) None), VoidStamp),
  (11, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (12, (ReturnNode (Some 11) None), VoidStamp)
  ]"
value "static_test unit_Int_lessEqual02_test  [(new_int 32 (-2147483648))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual02_test  [(new_int 32 (-2))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual02_test  [(new_int 32 (-1))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual02_test  [(new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual02_test  [(new_int 32 (4))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual02_test  [(new_int 32 (5))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual02_test  [(new_int 32 (6))] (new_int 32 (0))"

value "static_test unit_Int_lessEqual02_test  [(new_int 32 (2147483647))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/lang/Int_lessEqual03;.Int_lessEqual03_test*)
definition unit_Int_lessEqual03_test :: IRGraph where
  "unit_Int_lessEqual03_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (-5))), IntegerStamp 32 (-5) (-5)),
  (4, (ConstantNode (new_int 32 (-4))), IntegerStamp 32 (-4) (-4)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 10), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ReturnNode (Some 9) None), VoidStamp),
  (11, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (12, (ReturnNode (Some 11) None), VoidStamp)
  ]"
value "static_test unit_Int_lessEqual03_test  [(new_int 32 (-2147483648))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual03_test  [(new_int 32 (-6))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual03_test  [(new_int 32 (-5))] (new_int 32 (1))"

value "static_test unit_Int_lessEqual03_test  [(new_int 32 (-4))] (new_int 32 (0))"

value "static_test unit_Int_lessEqual03_test  [(new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_Int_lessEqual03_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Int_lessEqual03_test  [(new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_Int_lessEqual03_test  [(new_int 32 (2))] (new_int 32 (0))"

value "static_test unit_Int_lessEqual03_test  [(new_int 32 (2147483647))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_intDivIntegerMax*)
definition unit_IntegerDivRemConstantTest_intDivIntegerMax :: IRGraph where
  "unit_IntegerDivRemConstantTest_intDivIntegerMax = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (2147483647))), IntegerStamp 32 (2147483647) (2147483647)),
  (4, (SignedDivNode 4 1 3 None None 5), IntegerStamp 32 (-1) (1)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_intDivIntegerMax  [(new_int 32 (-10))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intDivIntegerMax  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intDivIntegerMax  [(new_int 32 (4256))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intDivIntegerMax  [(new_int 32 (2147483647))] (new_int 32 (1))"

value "static_test unit_IntegerDivRemConstantTest_intDivIntegerMax  [(new_int 32 (-2147483648))] (new_int 32 (-1))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_intDivIntegerMinOdd*)
definition unit_IntegerDivRemConstantTest_intDivIntegerMinOdd :: IRGraph where
  "unit_IntegerDivRemConstantTest_intDivIntegerMinOdd = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (-2147483647))), IntegerStamp 32 (-2147483647) (-2147483647)),
  (4, (SignedDivNode 4 1 3 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_intDivIntegerMinOdd  [(new_int 32 (-123))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intDivIntegerMinOdd  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intDivIntegerMinOdd  [(new_int 32 (123))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intDivIntegerMinOdd  [(new_int 32 (2147483647))] (new_int 32 (-1))"

value "static_test unit_IntegerDivRemConstantTest_intDivIntegerMinOdd  [(new_int 32 (-2147483648))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_intDivNegativeConstant*)
definition unit_IntegerDivRemConstantTest_intDivNegativeConstant :: IRGraph where
  "unit_IntegerDivRemConstantTest_intDivNegativeConstant = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (-1234))), IntegerStamp 32 (-1234) (-1234)),
  (4, (SignedDivNode 4 1 3 None None 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_intDivNegativeConstant  [(new_int 32 (-123))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intDivNegativeConstant  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intDivNegativeConstant  [(new_int 32 (123))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intDivNegativeConstant  [(new_int 32 (2147483647))] (new_int 32 (-1740262))"

value "static_test unit_IntegerDivRemConstantTest_intDivNegativeConstant  [(new_int 32 (-2147483648))] (new_int 32 (1740262))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_intDivPositiveConstant*)
definition unit_IntegerDivRemConstantTest_intDivPositiveConstant :: IRGraph where
  "unit_IntegerDivRemConstantTest_intDivPositiveConstant = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (4, (SignedDivNode 4 1 3 None None 5), IntegerStamp 32 (-429496729) (429496729)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_intDivPositiveConstant  [(new_int 32 (-10))] (new_int 32 (-2))"

value "static_test unit_IntegerDivRemConstantTest_intDivPositiveConstant  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intDivPositiveConstant  [(new_int 32 (4256))] (new_int 32 (851))"

value "static_test unit_IntegerDivRemConstantTest_intDivPositiveConstant  [(new_int 32 (2147483647))] (new_int 32 (429496729))"

value "static_test unit_IntegerDivRemConstantTest_intDivPositiveConstant  [(new_int 32 (-2147483648))] (new_int 32 (-429496729))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_intRemMax*)
definition unit_IntegerDivRemConstantTest_intRemMax :: IRGraph where
  "unit_IntegerDivRemConstantTest_intRemMax = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (2147483647))), IntegerStamp 32 (2147483647) (2147483647)),
  (4, (SignedRemNode 4 1 3 None None 5), IntegerStamp 32 (-2147483646) (2147483646)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_intRemMax  [(new_int 32 (-10))] (new_int 32 (-10))"

value "static_test unit_IntegerDivRemConstantTest_intRemMax  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intRemMax  [(new_int 32 (4256))] (new_int 32 (4256))"

value "static_test unit_IntegerDivRemConstantTest_intRemMax  [(new_int 32 (2147483647))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intRemMax  [(new_int 32 (-2147483648))] (new_int 32 (-1))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_intRemMin*)
definition unit_IntegerDivRemConstantTest_intRemMin :: IRGraph where
  "unit_IntegerDivRemConstantTest_intRemMin = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (-2147483648))), IntegerStamp 32 (-2147483648) (-2147483648)),
  (4, (SignedRemNode 4 1 3 None None 5), IntegerStamp 32 (-2147483647) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_intRemMin  [(new_int 32 (-10))] (new_int 32 (-10))"

value "static_test unit_IntegerDivRemConstantTest_intRemMin  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intRemMin  [(new_int 32 (4256))] (new_int 32 (4256))"

value "static_test unit_IntegerDivRemConstantTest_intRemMin  [(new_int 32 (2147483647))] (new_int 32 (2147483647))"

value "static_test unit_IntegerDivRemConstantTest_intRemMin  [(new_int 32 (-2147483648))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_intRemNegativeConstant*)
definition unit_IntegerDivRemConstantTest_intRemNegativeConstant :: IRGraph where
  "unit_IntegerDivRemConstantTest_intRemNegativeConstant = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (-139968))), IntegerStamp 32 (-139968) (-139968)),
  (4, (ConstantNode (new_int 32 (139968))), IntegerStamp 32 (139968) (139968)),
  (5, (SignedRemNode 5 1 4 None None 6), IntegerStamp 32 (-139967) (139967)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_intRemNegativeConstant  [(new_int 32 (-10))] (new_int 32 (-10))"

value "static_test unit_IntegerDivRemConstantTest_intRemNegativeConstant  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intRemNegativeConstant  [(new_int 32 (4256))] (new_int 32 (4256))"

value "static_test unit_IntegerDivRemConstantTest_intRemNegativeConstant  [(new_int 32 (2147483647))] (new_int 32 (94591))"

value "static_test unit_IntegerDivRemConstantTest_intRemNegativeConstant  [(new_int 32 (-2147483648))] (new_int 32 (-94592))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_intRemPositiveConstant*)
definition unit_IntegerDivRemConstantTest_intRemPositiveConstant :: IRGraph where
  "unit_IntegerDivRemConstantTest_intRemPositiveConstant = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (139968))), IntegerStamp 32 (139968) (139968)),
  (4, (SignedRemNode 4 1 3 None None 5), IntegerStamp 32 (-139967) (139967)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_intRemPositiveConstant  [(new_int 32 (-10))] (new_int 32 (-10))"

value "static_test unit_IntegerDivRemConstantTest_intRemPositiveConstant  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intRemPositiveConstant  [(new_int 32 (4256))] (new_int 32 (4256))"

value "static_test unit_IntegerDivRemConstantTest_intRemPositiveConstant  [(new_int 32 (2147483647))] (new_int 32 (94591))"

value "static_test unit_IntegerDivRemConstantTest_intRemPositiveConstant  [(new_int 32 (-2147483648))] (new_int 32 (-94592))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_intRemPowerOf2*)
definition unit_IntegerDivRemConstantTest_intRemPowerOf2 :: IRGraph where
  "unit_IntegerDivRemConstantTest_intRemPowerOf2 = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (4, (SignedRemNode 4 1 3 None None 5), IntegerStamp 32 (-3) (3)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_intRemPowerOf2  [(new_int 32 (-10))] (new_int 32 (-2))"

value "static_test unit_IntegerDivRemConstantTest_intRemPowerOf2  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intRemPowerOf2  [(new_int 32 (4256))] (new_int 32 (0))"

value "static_test unit_IntegerDivRemConstantTest_intRemPowerOf2  [(new_int 32 (2147483647))] (new_int 32 (3))"

value "static_test unit_IntegerDivRemConstantTest_intRemPowerOf2  [(new_int 32 (-2147483648))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_longDivLongMax*)
definition unit_IntegerDivRemConstantTest_longDivLongMax :: IRGraph where
  "unit_IntegerDivRemConstantTest_longDivLongMax = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (9223372036854775807))), IntegerStamp 64 (9223372036854775807) (9223372036854775807)),
  (4, (SignedDivNode 4 1 3 None None 5), IntegerStamp 64 (-1) (1)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_longDivLongMax  [(IntVal 64 (-1234))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longDivLongMax  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longDivLongMax  [(IntVal 64 (214423))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longDivLongMax  [(IntVal 64 (9223372036854775807))] (IntVal 64 (1))"

value "static_test unit_IntegerDivRemConstantTest_longDivLongMax  [(IntVal 64 (-9223372036854775808))] (IntVal 64 (-1))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_longDivLongMinOdd*)
definition unit_IntegerDivRemConstantTest_longDivLongMinOdd :: IRGraph where
  "unit_IntegerDivRemConstantTest_longDivLongMinOdd = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (-9223372036854775807))), IntegerStamp 64 (-9223372036854775807) (-9223372036854775807)),
  (4, (SignedDivNode 4 1 3 None None 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_longDivLongMinOdd  [(IntVal 64 (-1234))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longDivLongMinOdd  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longDivLongMinOdd  [(IntVal 64 (214423))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longDivLongMinOdd  [(IntVal 64 (9223372036854775807))] (IntVal 64 (-1))"

value "static_test unit_IntegerDivRemConstantTest_longDivLongMinOdd  [(IntVal 64 (-9223372036854775808))] (IntVal 64 (1))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_longDivNegativeConstant*)
definition unit_IntegerDivRemConstantTest_longDivNegativeConstant :: IRGraph where
  "unit_IntegerDivRemConstantTest_longDivNegativeConstant = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (-413))), IntegerStamp 64 (-413) (-413)),
  (4, (SignedDivNode 4 1 3 None None 5), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_longDivNegativeConstant  [(IntVal 64 (-43))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longDivNegativeConstant  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longDivNegativeConstant  [(IntVal 64 (147065))] (IntVal 64 (-356))"

value "static_test unit_IntegerDivRemConstantTest_longDivNegativeConstant  [(IntVal 64 (9223372036854775807))] (IntVal 64 (-22332619943958294))"

value "static_test unit_IntegerDivRemConstantTest_longDivNegativeConstant  [(IntVal 64 (-9223372036854775808))] (IntVal 64 (22332619943958294))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_longDivPositiveConstant*)
definition unit_IntegerDivRemConstantTest_longDivPositiveConstant :: IRGraph where
  "unit_IntegerDivRemConstantTest_longDivPositiveConstant = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (35170432))), IntegerStamp 64 (35170432) (35170432)),
  (4, (SignedDivNode 4 1 3 None None 5), IntegerStamp 64 (-262247902921) (262247902921)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_longDivPositiveConstant  [(IntVal 64 (-1234))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longDivPositiveConstant  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longDivPositiveConstant  [(IntVal 64 (214423))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longDivPositiveConstant  [(IntVal 64 (9223372036854775807))] (IntVal 64 (262247902921))"

value "static_test unit_IntegerDivRemConstantTest_longDivPositiveConstant  [(IntVal 64 (-9223372036854775808))] (IntVal 64 (-262247902921))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_longRemMax*)
definition unit_IntegerDivRemConstantTest_longRemMax :: IRGraph where
  "unit_IntegerDivRemConstantTest_longRemMax = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (9223372036854775807))), IntegerStamp 64 (9223372036854775807) (9223372036854775807)),
  (4, (SignedRemNode 4 1 3 None None 5), IntegerStamp 64 (-9223372036854775806) (9223372036854775806)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_longRemMax  [(IntVal 64 (-43))] (IntVal 64 (-43))"

value "static_test unit_IntegerDivRemConstantTest_longRemMax  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longRemMax  [(IntVal 64 (147065))] (IntVal 64 (147065))"

value "static_test unit_IntegerDivRemConstantTest_longRemMax  [(IntVal 64 (9223372036854775807))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longRemMax  [(IntVal 64 (-9223372036854775808))] (IntVal 64 (-1))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_longRemMin*)
definition unit_IntegerDivRemConstantTest_longRemMin :: IRGraph where
  "unit_IntegerDivRemConstantTest_longRemMin = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (-9223372036854775808))), IntegerStamp 64 (-9223372036854775808) (-9223372036854775808)),
  (4, (SignedRemNode 4 1 3 None None 5), IntegerStamp 64 (-9223372036854775807) (9223372036854775807)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_longRemMin  [(IntVal 64 (-43))] (IntVal 64 (-43))"

value "static_test unit_IntegerDivRemConstantTest_longRemMin  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longRemMin  [(IntVal 64 (147065))] (IntVal 64 (147065))"

value "static_test unit_IntegerDivRemConstantTest_longRemMin  [(IntVal 64 (9223372036854775807))] (IntVal 64 (9223372036854775807))"

value "static_test unit_IntegerDivRemConstantTest_longRemMin  [(IntVal 64 (-9223372036854775808))] (IntVal 64 (0))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_longRemNegativeConstant*)
definition unit_IntegerDivRemConstantTest_longRemNegativeConstant :: IRGraph where
  "unit_IntegerDivRemConstantTest_longRemNegativeConstant = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (-413))), IntegerStamp 64 (-413) (-413)),
  (4, (ConstantNode (IntVal 64 (413))), IntegerStamp 64 (413) (413)),
  (5, (SignedRemNode 5 1 4 None None 6), IntegerStamp 64 (-412) (412)),
  (6, (ReturnNode (Some 5) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_longRemNegativeConstant  [(IntVal 64 (-43))] (IntVal 64 (-43))"

value "static_test unit_IntegerDivRemConstantTest_longRemNegativeConstant  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longRemNegativeConstant  [(IntVal 64 (147065))] (IntVal 64 (37))"

value "static_test unit_IntegerDivRemConstantTest_longRemNegativeConstant  [(IntVal 64 (9223372036854775807))] (IntVal 64 (385))"

value "static_test unit_IntegerDivRemConstantTest_longRemNegativeConstant  [(IntVal 64 (-9223372036854775808))] (IntVal 64 (-386))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_longRemPositiveConstant*)
definition unit_IntegerDivRemConstantTest_longRemPositiveConstant :: IRGraph where
  "unit_IntegerDivRemConstantTest_longRemPositiveConstant = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (35170432))), IntegerStamp 64 (35170432) (35170432)),
  (4, (SignedRemNode 4 1 3 None None 5), IntegerStamp 64 (-35170431) (35170431)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_longRemPositiveConstant  [(IntVal 64 (-1234))] (IntVal 64 (-1234))"

value "static_test unit_IntegerDivRemConstantTest_longRemPositiveConstant  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longRemPositiveConstant  [(IntVal 64 (214423))] (IntVal 64 (214423))"

value "static_test unit_IntegerDivRemConstantTest_longRemPositiveConstant  [(IntVal 64 (9223372036854775807))] (IntVal 64 (29143935))"

value "static_test unit_IntegerDivRemConstantTest_longRemPositiveConstant  [(IntVal 64 (-9223372036854775808))] (IntVal 64 (-29143936))"


(* Lorg/graalvm/compiler/core/test/IntegerDivRemConstantTest;.IntegerDivRemConstantTest_longRemPowerOf2*)
definition unit_IntegerDivRemConstantTest_longRemPowerOf2 :: IRGraph where
  "unit_IntegerDivRemConstantTest_longRemPowerOf2 = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 64 (4))), IntegerStamp 64 (4) (4)),
  (4, (SignedRemNode 4 1 3 None None 5), IntegerStamp 64 (-3) (3)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_IntegerDivRemConstantTest_longRemPowerOf2  [(IntVal 64 (-43))] (IntVal 64 (-3))"

value "static_test unit_IntegerDivRemConstantTest_longRemPowerOf2  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_IntegerDivRemConstantTest_longRemPowerOf2  [(IntVal 64 (147065))] (IntVal 64 (1))"

value "static_test unit_IntegerDivRemConstantTest_longRemPowerOf2  [(IntVal 64 (9223372036854775807))] (IntVal 64 (3))"

value "static_test unit_IntegerDivRemConstantTest_longRemPowerOf2  [(IntVal 64 (-9223372036854775808))] (IntVal 64 (0))"


(* Lorg/graalvm/compiler/core/test/IntegerStampShiftTest;.IntegerStampShiftTest_unsignedShiftNegativeInt*)
definition unit_IntegerStampShiftTest_unsignedShiftNegativeInt :: IRGraph where
  "unit_IntegerStampShiftTest_unsignedShiftNegativeInt = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (-16))), IntegerStamp 32 (-16) (-16)),
  (10, (ConstantNode (new_int 32 (-256))), IntegerStamp 32 (-256) (-256)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 32 (-256) (-16)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (ConstantNode (new_int 32 (8))), IntegerStamp 32 (8) (8)),
  (17, (ConstantNode (new_int 32 (16777215))), IntegerStamp 32 (16777215) (16777215)),
  (18, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IntegerStampShiftTest_unsignedShiftNegativeInt  [(new_int 32 (0))] (new_int 32 (16777215))"


(* Lorg/graalvm/compiler/core/test/IntegerStampShiftTest;.IntegerStampShiftTest_unsignedShiftNegativeLong*)
definition unit_IntegerStampShiftTest_unsignedShiftNegativeLong :: IRGraph where
  "unit_IntegerStampShiftTest_unsignedShiftNegativeLong = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 64 (-16))), IntegerStamp 64 (-16) (-16)),
  (10, (ConstantNode (IntVal 64 (-256))), IntegerStamp 64 (-256) (-256)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 64 (-256) (-16)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (ConstantNode (new_int 32 (8))), IntegerStamp 32 (8) (8)),
  (17, (ConstantNode (IntVal 64 (72057594037927935))), IntegerStamp 64 (72057594037927935) (72057594037927935)),
  (18, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IntegerStampShiftTest_unsignedShiftNegativeLong  [(new_int 32 (0))] (IntVal 64 (72057594037927935))"


(* Lorg/graalvm/compiler/core/test/IntegerStampShiftTest;.IntegerStampShiftTest_unsignedShiftPositiveInt*)
definition unit_IntegerStampShiftTest_unsignedShiftPositiveInt :: IRGraph where
  "unit_IntegerStampShiftTest_unsignedShiftPositiveInt = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (2147483632))), IntegerStamp 32 (2147483632) (2147483632)),
  (10, (ConstantNode (new_int 32 (2147483392))), IntegerStamp 32 (2147483392) (2147483392)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 32 (2147483392) (2147483632)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (ConstantNode (new_int 32 (8))), IntegerStamp 32 (8) (8)),
  (17, (ConstantNode (new_int 32 (8388607))), IntegerStamp 32 (8388607) (8388607)),
  (18, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IntegerStampShiftTest_unsignedShiftPositiveInt  [(new_int 32 (0))] (new_int 32 (8388607))"


(* Lorg/graalvm/compiler/core/test/IntegerStampShiftTest;.IntegerStampShiftTest_unsignedShiftPositiveLong*)
definition unit_IntegerStampShiftTest_unsignedShiftPositiveLong :: IRGraph where
  "unit_IntegerStampShiftTest_unsignedShiftPositiveLong = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 64 (9223372036854775792))), IntegerStamp 64 (9223372036854775792) (9223372036854775792)),
  (10, (ConstantNode (IntVal 64 (9223372036854775552))), IntegerStamp 64 (9223372036854775552) (9223372036854775552)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 64 (9223372036854775552) (9223372036854775792)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (ConstantNode (new_int 32 (8))), IntegerStamp 32 (8) (8)),
  (17, (ConstantNode (IntVal 64 (36028797018963967))), IntegerStamp 64 (36028797018963967) (36028797018963967)),
  (18, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_IntegerStampShiftTest_unsignedShiftPositiveLong  [(new_int 32 (0))] (IntVal 64 (36028797018963967))"


(* Lorg/graalvm/compiler/jtt/micro/InvokeVirtual_01;.InvokeVirtual_01_test*)
definition unit_InvokeVirtual_01_test :: Program where
  "unit_InvokeVirtual_01_test = Map.empty (
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 17), VoidStamp),
  (6, (BeginNode 8), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (LoadFieldNode 8 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::aObject'' None 10), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' False False False),
  (9, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I'' [8, 1]), VoidStamp),
  (10, (InvokeNode 10 9 None None (Some 11) 12), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (ReturnNode (Some 10) None), VoidStamp),
  (13, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (14, (IntegerEqualsNode 1 13), VoidStamp),
  (15, (BeginNode 27), VoidStamp),
  (16, (BeginNode 18), VoidStamp),
  (17, (IfNode 14 16 15), VoidStamp),
  (18, (LoadFieldNode 18 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::bObject'' None 20), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' False False False),
  (19, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I'' [18, 1]), VoidStamp),
  (20, (InvokeNode 20 19 None None (Some 21) 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (ReturnNode (Some 20) None), VoidStamp),
  (23, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (24, (IntegerEqualsNode 1 23), VoidStamp),
  (25, (BeginNode 34), VoidStamp),
  (26, (BeginNode 28), VoidStamp),
  (27, (IfNode 24 26 25), VoidStamp),
  (28, (LoadFieldNode 28 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::cObject'' None 30), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' False False False),
  (29, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I'' [28, 1]), VoidStamp),
  (30, (InvokeNode 30 29 None None (Some 31) 32), IntegerStamp 32 (-2147483648) (2147483647)),
  (31, (FrameState [] None None None), IllegalStamp),
  (32, (ReturnNode (Some 30) None), VoidStamp),
  (33, (ConstantNode (new_int 32 (42))), IntegerStamp 32 (42) (42)),
  (34, (ReturnNode (Some 33) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' None 4), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::aObject'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (NewInstanceNode 6 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B'' None 10), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B'' True True False),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (FrameState [] (Some 8) None None), IllegalStamp),
  (10, (StoreFieldNode 10 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::bObject'' 6 (Some 11) None 12), VoidStamp),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (NewInstanceNode 12 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$C'' None 16), ObjectStamp ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$C'' True True False),
  (13, (FrameState [] None None None), IllegalStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (FrameState [] (Some 14) None None), IllegalStamp),
  (16, (StoreFieldNode 16 ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01::cObject'' 12 (Some 17) None 18), VoidStamp),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ReturnNode None None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ReturnNode (Some 2) None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_InvokeVirtual_01_test ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.test(I)I'' [(new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_InvokeVirtual_01_test ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.test(I)I'' [(new_int 32 (1))] (new_int 32 (11))"

value "program_test unit_InvokeVirtual_01_test ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.test(I)I'' [(new_int 32 (2))] (new_int 32 (22))"

value "program_test unit_InvokeVirtual_01_test ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01.test(I)I'' [(new_int 32 (3))] (new_int 32 (42))"


(* Lorg/graalvm/compiler/jtt/optimize/LLE_01;.LLE_01_test*)
definition unit_LLE_01_test :: IRGraph where
  "unit_LLE_01_test = irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.optimize.LLE_01$TestClass'' None 5), ObjectStamp ''org.graalvm.compiler.jtt.optimize.LLE_01$TestClass'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.jtt.optimize.LLE_01$TestClass::field1'' 4 (Some 6) (Some 2) 8), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (8, (StoreFieldNode 8 ''org.graalvm.compiler.jtt.optimize.LLE_01$TestClass::field1'' 7 (Some 9) (Some 2) 10), VoidStamp),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (LoadFieldNode 10 ''org.graalvm.compiler.jtt.optimize.LLE_01$TestClass::field1'' (Some 2) 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_LLE_01_test  [] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/lang/Long_reverseBytes02;.Long_reverseBytes02_test*)
definition unit_Long_reverseBytes02_test :: IRGraph where
  "unit_Long_reverseBytes02_test = irgraph [
  (0, (StartNode (Some 2) 41), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (56))), IntegerStamp 32 (56) (56)),
  (4, (RightShiftNode 1 3), IntegerStamp 64 (-128) (127)),
  (5, (ConstantNode (IntVal 64 (255))), IntegerStamp 64 (255) (255)),
  (6, (AndNode 4 5), IntegerStamp 64 (0) (255)),
  (7, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (8, (ConstantNode (new_int 32 (48))), IntegerStamp 32 (48) (48)),
  (9, (RightShiftNode 1 8), IntegerStamp 64 (-32768) (32767)),
  (10, (AndNode 9 5), IntegerStamp 64 (0) (255)),
  (11, (ConstantNode (new_int 32 (8))), IntegerStamp 32 (8) (8)),
  (12, (LeftShiftNode 10 11), IntegerStamp 64 (0) (65280)),
  (13, (OrNode 6 12), IntegerStamp 64 (0) (65535)),
  (14, (ConstantNode (new_int 32 (40))), IntegerStamp 32 (40) (40)),
  (15, (RightShiftNode 1 14), IntegerStamp 64 (-8388608) (8388607)),
  (16, (AndNode 15 5), IntegerStamp 64 (0) (255)),
  (17, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (18, (LeftShiftNode 16 17), IntegerStamp 64 (0) (16711680)),
  (19, (OrNode 13 18), IntegerStamp 64 (0) (16777215)),
  (20, (ConstantNode (new_int 32 (32))), IntegerStamp 32 (32) (32)),
  (21, (RightShiftNode 1 20), IntegerStamp 64 (-2147483648) (2147483647)),
  (22, (AndNode 21 5), IntegerStamp 64 (0) (255)),
  (23, (ConstantNode (new_int 32 (24))), IntegerStamp 32 (24) (24)),
  (24, (LeftShiftNode 22 23), IntegerStamp 64 (0) (4278190080)),
  (25, (OrNode 19 24), IntegerStamp 64 (0) (4294967295)),
  (26, (RightShiftNode 1 23), IntegerStamp 64 (-549755813888) (549755813887)),
  (27, (AndNode 26 5), IntegerStamp 64 (0) (255)),
  (28, (LeftShiftNode 27 20), IntegerStamp 64 (0) (1095216660480)),
  (29, (OrNode 25 28), IntegerStamp 64 (0) (1099511627775)),
  (30, (RightShiftNode 1 17), IntegerStamp 64 (-140737488355328) (140737488355327)),
  (31, (AndNode 30 5), IntegerStamp 64 (0) (255)),
  (32, (LeftShiftNode 31 14), IntegerStamp 64 (0) (280375465082880)),
  (33, (OrNode 29 32), IntegerStamp 64 (0) (281474976710655)),
  (34, (RightShiftNode 1 11), IntegerStamp 64 (-36028797018963968) (36028797018963967)),
  (35, (AndNode 34 5), IntegerStamp 64 (0) (255)),
  (36, (LeftShiftNode 35 8), IntegerStamp 64 (0) (71776119061217280)),
  (37, (OrNode 33 36), IntegerStamp 64 (0) (72057594037927935)),
  (38, (AndNode 1 5), IntegerStamp 64 (0) (255)),
  (39, (LeftShiftNode 38 3), IntegerStamp 64 (-9223372036854775808) (9151314442816847872)),
  (40, (OrNode 37 39), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (41, (ReturnNode (Some 40) None), VoidStamp)
  ]"
value "static_test unit_Long_reverseBytes02_test  [(IntVal 64 (1234605616436508424))] (IntVal 64 (610068790934446609))"


(* Lorg/graalvm/compiler/jtt/loop/Loop01;.Loop01_test*)
definition unit_Loop01_test :: IRGraph where
  "unit_Loop01_test = irgraph [
  (0, (StartNode (Some 1) 5), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 26] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [2, 18] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 25] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (11, (IntegerLessThanNode 8 10), VoidStamp),
  (13, (LoopExitNode 6 (Some 14) 28), VoidStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 24), VoidStamp),
  (16, (IfNode 11 15 13), VoidStamp),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (19, (IntegerEqualsNode 7 2), VoidStamp),
  (20, (BeginNode 26), VoidStamp),
  (22, (LoopExitNode 6 (Some 23) 27), VoidStamp),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (IfNode 19 22 20), VoidStamp),
  (25, (AddNode 8 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (LoopEndNode 6), VoidStamp),
  (27, (ReturnNode (Some 2) None), VoidStamp),
  (28, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Loop01_test  [] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/loop/Loop02;.Loop02_test*)
definition unit_Loop02_test :: IRGraph where
  "unit_Loop02_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 27] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [1, 18] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 26] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (11, (IntegerLessThanNode 8 10), VoidStamp),
  (13, (LoopExitNode 6 (Some 14) 29), VoidStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 25), VoidStamp),
  (16, (IfNode 11 15 13), VoidStamp),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (19, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (20, (IntegerEqualsNode 7 19), VoidStamp),
  (21, (BeginNode 27), VoidStamp),
  (23, (LoopExitNode 6 (Some 24) 28), VoidStamp),
  (24, (FrameState [] None None None), IllegalStamp),
  (25, (IfNode 20 23 21), VoidStamp),
  (26, (AddNode 8 19), IntegerStamp 32 (-2147483648) (2147483647)),
  (27, (LoopEndNode 6), VoidStamp),
  (28, (ReturnNode (Some 19) None), VoidStamp),
  (29, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Loop02_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Loop02_test  [(new_int 32 (1))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/loop/Loop03;.Loop03_test*)
definition unit_Loop03_test :: IRGraph where
  "unit_Loop03_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (5, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (8, (EndNode), VoidStamp),
  (9, (LoopBeginNode [8, 26] None (Some 14) 23), VoidStamp),
  (10, (ValuePhiNode 10 [3, 11] 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (ValuePhiNode 11 [4, 24] 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (12, (ValuePhiNode 12 [5, 11] 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (13, (ValuePhiNode 13 [6, 25] 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (IntegerLessThanNode 13 1), VoidStamp),
  (17, (LoopExitNode 9 (Some 21) 33), VoidStamp),
  (18, (RefNode 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (RefNode 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (20, (RefNode 12), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (BeginNode 26), VoidStamp),
  (23, (IfNode 15 22 17), VoidStamp),
  (24, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (25, (AddNode 13 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (LoopEndNode 9), VoidStamp),
  (27, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (28, (MulNode 19 27), IntegerStamp 32 (-2147483648) (2147483647)),
  (29, (AddNode 18 28), IntegerStamp 32 (-2147483648) (2147483647)),
  (30, (ConstantNode (new_int 32 (1000))), IntegerStamp 32 (1000) (1000)),
  (31, (MulNode 20 30), IntegerStamp 32 (-2147483648) (2147483647)),
  (32, (AddNode 29 31), IntegerStamp 32 (-2147483648) (2147483647)),
  (33, (ReturnNode (Some 32) None), VoidStamp)
  ]"
value "static_test unit_Loop03_test  [(new_int 32 (10))] (new_int 32 (7077))"


(* Lorg/graalvm/compiler/jtt/loop/Loop04;.Loop04_test*)
definition unit_Loop04_test :: IRGraph where
  "unit_Loop04_test = irgraph [
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
value "static_test unit_Loop04_test  [(new_int 32 (0))] (new_int 32 (4321))"

value "static_test unit_Loop04_test  [(new_int 32 (1))] (new_int 32 (2432))"

value "static_test unit_Loop04_test  [(new_int 32 (10))] (new_int 32 (2432))"

end
