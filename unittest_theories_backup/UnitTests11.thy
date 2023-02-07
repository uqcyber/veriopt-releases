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


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifge_3;.BC_ifge_3_test*)
definition unit_BC_ifge_3_test :: IRGraph where
  "unit_BC_ifge_3_test = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (6, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (7, (ConditionalNode 4 5 6), IntegerStamp 32 (0) (1)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_BC_ifge_3_test  [(new_int 32 (0)), (new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_BC_ifge_3_test  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_ifge_3_test  [(new_int 32 (1)), (new_int 32 (1))] (new_int 32 (0))"

value "static_test unit_BC_ifge_3_test  [(new_int 32 (0)), (new_int 32 (-100))] (new_int 32 (0))"

value "static_test unit_BC_ifge_3_test  [(new_int 32 (-1)), (new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_BC_ifge_3_test  [(new_int 32 (-12)), (new_int 32 (-12))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifge;.BC_ifge_test*)
definition unit_BC_ifge_test :: IRGraph where
  "unit_BC_ifge_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 32 (-1) (1)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 24), VoidStamp),
  (17, (BeginNode 22), VoidStamp),
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
value "static_test unit_BC_ifge_test  [(new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_BC_ifge_test  [(new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_BC_ifge_test  [(new_int 32 (-1))] (new_int 32 (-2))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifgt;.BC_ifgt_test*)
definition unit_BC_ifgt_test :: IRGraph where
  "unit_BC_ifgt_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (BeginNode 13), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (10, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [4, 10] 12), IntegerStamp 32 (-1) (1)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 24), VoidStamp),
  (17, (BeginNode 22), VoidStamp),
  (18, (IfNode 5 17 16), VoidStamp),
  (19, (AddNode 14 10), IntegerStamp 32 (-2) (0)),
  (21, (AddNode 14 4), IntegerStamp 32 (0) (2)),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode [22, 24] (Some 26) 27), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (ValuePhiNode 25 [19, 21] 23), IntegerStamp 32 (-2) (2)),
  (26, (FrameState [] None None None), IllegalStamp),
  (27, (ReturnNode (Some 25) None), VoidStamp)
  ]"
value "static_test unit_BC_ifgt_test  [(new_int 32 (0))] (new_int 32 (-2))"

value "static_test unit_BC_ifgt_test  [(new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_BC_ifgt_test  [(new_int 32 (-1))] (new_int 32 (-2))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ificmplt1;.BC_ificmplt1_test*)
definition unit_BC_ificmplt1_test :: IRGraph where
  "unit_BC_ificmplt1_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (12))), IntegerStamp 32 (12) (12)),
  (10, (ConstantNode (new_int 32 (13))), IntegerStamp 32 (13) (13)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 16), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 32 (12) (13)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_BC_ificmplt1_test  [(new_int 32 (0))] (new_int 32 (12))"

value "static_test unit_BC_ificmplt1_test  [(new_int 32 (1))] (new_int 32 (13))"

value "static_test unit_BC_ificmplt1_test  [(new_int 32 (2))] (new_int 32 (13))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ificmplt2;.BC_ificmplt2_test*)
definition unit_BC_ificmplt2_test :: IRGraph where
  "unit_BC_ificmplt2_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 14), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (13))), IntegerStamp 32 (13) (13)),
  (11, (ConstantNode (new_int 32 (12))), IntegerStamp 32 (12) (12)),
  (12, (EndNode), VoidStamp),
  (13, (MergeNode [12, 14] (Some 16) 17), VoidStamp),
  (14, (EndNode), VoidStamp),
  (15, (ValuePhiNode 15 [9, 11] 13), IntegerStamp 32 (12) (13)),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (ReturnNode (Some 15) None), VoidStamp)
  ]"
value "static_test unit_BC_ificmplt2_test  [(new_int 32 (0))] (new_int 32 (12))"

value "static_test unit_BC_ificmplt2_test  [(new_int 32 (1))] (new_int 32 (12))"

value "static_test unit_BC_ificmplt2_test  [(new_int 32 (2))] (new_int 32 (13))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ificmpne1;.BC_ificmpne1_test*)
definition unit_BC_ificmpne1_test :: IRGraph where
  "unit_BC_ificmpne1_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 13), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (12))), IntegerStamp 32 (12) (12)),
  (10, (ConstantNode (new_int 32 (13))), IntegerStamp 32 (13) (13)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 16), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 32 (12) (13)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_BC_ificmpne1_test  [(new_int 32 (0))] (new_int 32 (13))"

value "static_test unit_BC_ificmpne1_test  [(new_int 32 (1))] (new_int 32 (12))"

value "static_test unit_BC_ificmpne1_test  [(new_int 32 (2))] (new_int 32 (13))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ificmpne2;.BC_ificmpne2_test*)
definition unit_BC_ificmpne2_test :: IRGraph where
  "unit_BC_ificmpne2_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (13))), IntegerStamp 32 (13) (13)),
  (10, (ConstantNode (new_int 32 (12))), IntegerStamp 32 (12) (12)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 16), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 32 (12) (13)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (ReturnNode (Some 14) None), VoidStamp)
  ]"
value "static_test unit_BC_ificmpne2_test  [(new_int 32 (0))] (new_int 32 (13))"

value "static_test unit_BC_ificmpne2_test  [(new_int 32 (1))] (new_int 32 (12))"

value "static_test unit_BC_ificmpne2_test  [(new_int 32 (2))] (new_int 32 (13))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifle;.BC_ifle_test*)
definition unit_BC_ifle_test :: IRGraph where
  "unit_BC_ifle_test = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (BeginNode 11), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (10, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [4, 10] 12), IntegerStamp 32 (-1) (1)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 22), VoidStamp),
  (17, (BeginNode 24), VoidStamp),
  (18, (IfNode 5 17 16), VoidStamp),
  (19, (AddNode 14 10), IntegerStamp 32 (-2) (0)),
  (21, (AddNode 14 4), IntegerStamp 32 (0) (2)),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode [22, 24] (Some 26) 27), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (ValuePhiNode 25 [19, 21] 23), IntegerStamp 32 (-2) (2)),
  (26, (FrameState [] None None None), IllegalStamp),
  (27, (ReturnNode (Some 25) None), VoidStamp)
  ]"
value "static_test unit_BC_ifle_test  [(new_int 32 (0))] (new_int 32 (2))"

value "static_test unit_BC_ifle_test  [(new_int 32 (1))] (new_int 32 (-2))"

value "static_test unit_BC_ifle_test  [(new_int 32 (-1))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iflt;.BC_iflt_test*)
definition unit_BC_iflt_test :: IRGraph where
  "unit_BC_iflt_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
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
value "static_test unit_BC_iflt_test  [(new_int 32 (0))] (new_int 32 (-2))"

value "static_test unit_BC_iflt_test  [(new_int 32 (1))] (new_int 32 (-2))"

value "static_test unit_BC_iflt_test  [(new_int 32 (-1))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ifne;.BC_ifne_test*)
definition unit_BC_ifne_test :: IRGraph where
  "unit_BC_ifne_test = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 11), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (10, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (11, (EndNode), VoidStamp),
  (12, (MergeNode [11, 13] (Some 15) 18), VoidStamp),
  (13, (EndNode), VoidStamp),
  (14, (ValuePhiNode 14 [8, 10] 12), IntegerStamp 32 (-1) (1)),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (BeginNode 24), VoidStamp),
  (17, (BeginNode 22), VoidStamp),
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
value "static_test unit_BC_ifne_test  [(new_int 32 (0))] (new_int 32 (-2))"

value "static_test unit_BC_ifne_test  [(new_int 32 (1))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iinc_1;.BC_iinc_1_test*)
definition unit_BC_iinc_1_test :: IRGraph where
  "unit_BC_iinc_1_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iinc_1_test  [(new_int 32 (1))] (new_int 32 (2))"

value "static_test unit_BC_iinc_1_test  [(new_int 32 (2))] (new_int 32 (3))"

value "static_test unit_BC_iinc_1_test  [(new_int 32 (4))] (new_int 32 (5))"

value "static_test unit_BC_iinc_1_test  [(new_int 32 (-1))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iinc_2;.BC_iinc_2_test*)
definition unit_BC_iinc_2_test :: IRGraph where
  "unit_BC_iinc_2_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iinc_2_test  [(new_int 32 (1))] (new_int 32 (3))"

value "static_test unit_BC_iinc_2_test  [(new_int 32 (2))] (new_int 32 (4))"

value "static_test unit_BC_iinc_2_test  [(new_int 32 (4))] (new_int 32 (6))"

value "static_test unit_BC_iinc_2_test  [(new_int 32 (-2))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iinc_3;.BC_iinc_3_test*)
definition unit_BC_iinc_3_test :: IRGraph where
  "unit_BC_iinc_3_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (51))), IntegerStamp 32 (51) (51)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iinc_3_test  [(new_int 32 (1))] (new_int 32 (52))"

value "static_test unit_BC_iinc_3_test  [(new_int 32 (2))] (new_int 32 (53))"

value "static_test unit_BC_iinc_3_test  [(new_int 32 (4))] (new_int 32 (55))"

value "static_test unit_BC_iinc_3_test  [(new_int 32 (-1))] (new_int 32 (50))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iinc_4;.BC_iinc_4_test*)
definition unit_BC_iinc_4_test :: IRGraph where
  "unit_BC_iinc_4_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (512))), IntegerStamp 32 (512) (512)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iinc_4_test  [(new_int 32 (1))] (new_int 32 (513))"

value "static_test unit_BC_iinc_4_test  [(new_int 32 (2))] (new_int 32 (514))"

value "static_test unit_BC_iinc_4_test  [(new_int 32 (4))] (new_int 32 (516))"

value "static_test unit_BC_iinc_4_test  [(new_int 32 (-1))] (new_int 32 (511))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iload_0_1;.BC_iload_0_1_test*)
definition unit_BC_iload_0_1_test :: IRGraph where
  "unit_BC_iload_0_1_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (AddNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iload_0_1_test  [(new_int 32 (0))] (new_int 32 (1))"

value "static_test unit_BC_iload_0_1_test  [(new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_iload_0_1_test  [(new_int 32 (2))] (new_int 32 (3))"

value "static_test unit_BC_iload_0_1_test  [(new_int 32 (1000345))] (new_int 32 (1000346))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iload_0_2;.BC_iload_0_2_test*)
definition unit_BC_iload_0_2_test :: IRGraph where
  "unit_BC_iload_0_2_test = irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ReturnNode (Some 1) None), VoidStamp)
  ]"
value "static_test unit_BC_iload_0_2_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_iload_0_2_test  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iload_0_2_test  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_iload_0_2_test  [(new_int 32 (1000345))] (new_int 32 (1000345))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iload_0;.BC_iload_0_test*)
definition unit_BC_iload_0_test :: IRGraph where
  "unit_BC_iload_0_test = irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ReturnNode (Some 1) None), VoidStamp)
  ]"
value "static_test unit_BC_iload_0_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_iload_0_test  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iload_0_test  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_iload_0_test  [(new_int 32 (1000345))] (new_int 32 (1000345))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iload_1_1;.BC_iload_1_1_test*)
definition unit_BC_iload_1_1_test :: IRGraph where
  "unit_BC_iload_1_1_test = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ReturnNode (Some 1) None), VoidStamp)
  ]"
value "static_test unit_BC_iload_1_1_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_iload_1_1_test  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iload_1_1_test  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_iload_1_1_test  [(new_int 32 (1000345))] (new_int 32 (1000345))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iload_1;.BC_iload_1_test*)
definition unit_BC_iload_1_test :: IRGraph where
  "unit_BC_iload_1_test = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_BC_iload_1_test  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_iload_1_test  [(new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iload_1_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_iload_1_test  [(new_int 32 (1)), (new_int 32 (1000345))] (new_int 32 (1000345))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iload_2;.BC_iload_2_test*)
definition unit_BC_iload_2_test :: IRGraph where
  "unit_BC_iload_2_test = irgraph [
  (0, (StartNode (Some 4) 5), VoidStamp),
  (3, (ParameterNode 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_BC_iload_2_test  [(new_int 32 (1)), (new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_iload_2_test  [(new_int 32 (1)), (new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iload_2_test  [(new_int 32 (1)), (new_int 32 (1)), (new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_iload_2_test  [(new_int 32 (1)), (new_int 32 (1)), (new_int 32 (1000345))] (new_int 32 (1000345))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_iload_3;.BC_iload_3_test*)
definition unit_BC_iload_3_test :: IRGraph where
  "unit_BC_iload_3_test = irgraph [
  (0, (StartNode (Some 5) 6), VoidStamp),
  (4, (ParameterNode 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_iload_3_test  [(new_int 32 (1)), (new_int 32 (1)), (new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_iload_3_test  [(new_int 32 (1)), (new_int 32 (1)), (new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_iload_3_test  [(new_int 32 (1)), (new_int 32 (1)), (new_int 32 (1)), (new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_iload_3_test  [(new_int 32 (1)), (new_int 32 (1)), (new_int 32 (1)), (new_int 32 (1000345))] (new_int 32 (1000345))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_imul_16;.BC_imul_16_test*)
definition unit_BC_imul_16_test :: IRGraph where
  "unit_BC_imul_16_test = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (IntegerEqualsNode 1 4), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 11), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (10, (MulNode 2 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (ReturnNode (Some 10) None), VoidStamp),
  (12, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_BC_imul_16_test  [(new_int 32 (0)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (0)), (new_int 32 (16))] (new_int 32 (256))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (0)), (new_int 32 (17))] (new_int 32 (272))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (-16))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (0)), (new_int 32 (-16))] (new_int 32 (-256))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (0)), (new_int 32 (-17))] (new_int 32 (-272))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (0)), (new_int 32 (2147483647))] (new_int 32 (-16))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (0)), (new_int 32 (-2147483648))] (new_int 32 (0))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (1)), (new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (1)), (new_int 32 (16))] (new_int 32 (256))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (1)), (new_int 32 (17))] (new_int 32 (272))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (-16))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (1)), (new_int 32 (-16))] (new_int 32 (-256))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (1)), (new_int 32 (-17))] (new_int 32 (-272))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (1)), (new_int 32 (2147483647))] (new_int 32 (-16))"

value "static_test unit_BC_imul_16_test  [(new_int 32 (1)), (new_int 32 (-2147483648))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/BC_imul_4;.BC_imul_4_test*)
definition unit_BC_imul_4_test :: IRGraph where
  "unit_BC_imul_4_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (4, (MulNode 1 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_imul_4_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_imul_4_test  [(new_int 32 (4))] (new_int 32 (16))"

value "static_test unit_BC_imul_4_test  [(new_int 32 (5))] (new_int 32 (20))"

value "static_test unit_BC_imul_4_test  [(new_int 32 (-1))] (new_int 32 (-4))"

value "static_test unit_BC_imul_4_test  [(new_int 32 (-4))] (new_int 32 (-16))"

value "static_test unit_BC_imul_4_test  [(new_int 32 (-5))] (new_int 32 (-20))"

value "static_test unit_BC_imul_4_test  [(new_int 32 (-256))] (new_int 32 (-1024))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_imul;.BC_imul_test*)
definition unit_BC_imul_test :: IRGraph where
  "unit_BC_imul_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (MulNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_imul_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_imul_test  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_imul_test  [(new_int 32 (33)), (new_int 32 (67))] (new_int 32 (2211))"

value "static_test unit_BC_imul_test  [(new_int 32 (1)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_imul_test  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (-2147483648))"

value "static_test unit_BC_imul_test  [(new_int 32 (2147483647)), (new_int 32 (-1))] (new_int 32 (-2147483647))"

value "static_test unit_BC_imul_test  [(new_int 32 (-2147483648)), (new_int 32 (-1))] (new_int 32 (-2147483648))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ineg;.BC_ineg_test*)
definition unit_BC_ineg_test :: IRGraph where
  "unit_BC_ineg_test = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NegateNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_BC_ineg_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_ineg_test  [(new_int 32 (-1))] (new_int 32 (1))"

value "static_test unit_BC_ineg_test  [(new_int 32 (7263))] (new_int 32 (-7263))"

value "static_test unit_BC_ineg_test  [(new_int 32 (-2147483648))] (new_int 32 (-2147483648))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_invokestatic;.BC_invokestatic_test*)
definition unit_BC_invokestatic_test :: IRGraph where
  "unit_BC_invokestatic_test = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ReturnNode (Some 1) None), VoidStamp)
  ]"
value "static_test unit_BC_invokestatic_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_invokestatic_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_BC_invokestatic_test  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_invokestatic_test  [(new_int 32 (3))] (new_int 32 (3))"

value "static_test unit_BC_invokestatic_test  [(new_int 32 (-4))] (new_int 32 (-4))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ior;.BC_ior_test*)
definition unit_BC_ior_test :: IRGraph where
  "unit_BC_ior_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (OrNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_ior_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (3))"

value "static_test unit_BC_ior_test  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_ior_test  [(new_int 32 (31)), (new_int 32 (63))] (new_int 32 (63))"

value "static_test unit_BC_ior_test  [(new_int 32 (6)), (new_int 32 (4))] (new_int 32 (6))"

value "static_test unit_BC_ior_test  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (-2147483647))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_irem2;.BC_irem2_test*)
definition unit_BC_irem2_test :: IRGraph where
  "unit_BC_irem2_test = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedRemNode 4 1 2 None None 5), IntegerStamp 32 (-2147483647) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_irem2_test  [(new_int 32 (-2147483648)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_irem2_test  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_irem3;.BC_irem3_test*)
definition unit_BC_irem3_test :: IRGraph where
  "unit_BC_irem3_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_irem3_test  [(new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_irem3_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_irem3_test  [(new_int 32 (1000))] (new_int 32 (0))"

value "static_test unit_BC_irem3_test  [(new_int 32 (-2147483648))] (new_int 32 (0))"

value "static_test unit_BC_irem3_test  [(new_int 32 (2147483647))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_irem4;.BC_irem4_test*)
definition unit_BC_irem4_test :: IRGraph where
  "unit_BC_irem4_test = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (8))), IntegerStamp 32 (8) (8)),
  (4, (SignedRemNode 4 1 3 None None 5), IntegerStamp 32 (-7) (7)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_irem4_test  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_irem4_test  [(new_int 32 (-2))] (new_int 32 (-2))"

value "static_test unit_BC_irem4_test  [(new_int 32 (-8))] (new_int 32 (0))"

value "static_test unit_BC_irem4_test  [(new_int 32 (16))] (new_int 32 (0))"

value "static_test unit_BC_irem4_test  [(new_int 32 (-16))] (new_int 32 (0))"

value "static_test unit_BC_irem4_test  [(new_int 32 (-23))] (new_int 32 (-7))"

value "static_test unit_BC_irem4_test  [(new_int 32 (23))] (new_int 32 (7))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_irem;.BC_irem_test*)
definition unit_BC_irem_test :: IRGraph where
  "unit_BC_irem_test = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedRemNode 4 1 2 None None 5), IntegerStamp 32 (-2147483647) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_irem_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (1))"

value "static_test unit_BC_irem_test  [(new_int 32 (2)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_irem_test  [(new_int 32 (256)), (new_int 32 (4))] (new_int 32 (0))"

value "static_test unit_BC_irem_test  [(new_int 32 (135)), (new_int 32 (7))] (new_int 32 (2))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_irem;.BC_irem_test2*)
definition unit_BC_irem_test2 :: IRGraph where
  "unit_BC_irem_test2 = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (13))), IntegerStamp 32 (13) (13)),
  (4, (SignedRemNode 4 3 1 None None 5), IntegerStamp 32 (0) (13)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_irem_test2  [(new_int 32 (2))] (new_int 32 (1))"

value "static_test unit_BC_irem_test2  [(new_int 32 (20000000))] (new_int 32 (13))"

value "static_test unit_BC_irem_test2  [(new_int 32 (-20000000))] (new_int 32 (13))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_irem;.BC_irem_test3*)
definition unit_BC_irem_test3 :: IRGraph where
  "unit_BC_irem_test3 = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (13))), IntegerStamp 32 (13) (13)),
  (4, (SignedRemNode 4 1 3 None None 5), IntegerStamp 32 (-12) (12)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_irem_test3  [(new_int 32 (2))] (new_int 32 (2))"

value "static_test unit_BC_irem_test3  [(new_int 32 (200000000))] (new_int 32 (5))"

value "static_test unit_BC_irem_test3  [(new_int 32 (-200000000))] (new_int 32 (-5))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_irem;.BC_irem_test4*)
definition unit_BC_irem_test4 :: IRGraph where
  "unit_BC_irem_test4 = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedRemNode 4 1 2 None None 7), IntegerStamp 32 (-2147483647) (2147483647)),
  (5, (AbsNode 4), IntegerStamp 32 (0) (2147483647)),
  (6, (AbsNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (SignedRemNode 7 6 2 None None 11), IntegerStamp 32 (-2147483647) (2147483647)),
  (8, (ConstantNode (new_int 32 (32))), IntegerStamp 32 (32) (32)),
  (9, (OrNode 5 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (SignExtendNode 32 64 9), IntegerStamp 64 (-2147483648) (2147483647)),
  (11, (ReturnNode (Some 10) None), VoidStamp)
  ]"
value "static_test unit_BC_irem_test4  [(new_int 32 (-100000)), (new_int 32 (3000000))] (IntVal 64 (100000))"

value "static_test unit_BC_irem_test4  [(new_int 32 (-100000)), (new_int 32 (30))] (IntVal 64 (10))"

value "static_test unit_BC_irem_test4  [(new_int 32 (-1000000)), (new_int 32 (-30))] (IntVal 64 (10))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_irem;.BC_irem_test5*)
definition unit_BC_irem_test5 :: IRGraph where
  "unit_BC_irem_test5 = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (255))), IntegerStamp 32 (255) (255)),
  (5, (AddNode 1 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (AddNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (SignedRemNode 7 5 6 None None 8), IntegerStamp 32 (-2147483647) (2147483647)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_BC_irem_test5  [(new_int 32 (2147483647)), (new_int 32 (2147483647))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_irem;.BC_irem_test6*)
definition unit_BC_irem_test6 :: IRGraph where
  "unit_BC_irem_test6 = irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (255))), IntegerStamp 32 (255) (255)),
  (5, (ConstantNode (new_int 32 (-255))), IntegerStamp 32 (-255) (-255)),
  (6, (AddNode 1 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (AddNode 2 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (SignedRemNode 8 6 7 None None 9), IntegerStamp 32 (-2147483647) (2147483647)),
  (9, (ReturnNode (Some 8) None), VoidStamp)
  ]"
value "static_test unit_BC_irem_test6  [(new_int 32 (-2147483648)), (new_int 32 (-2147483648))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/except/BC_irem;.BC_irem_test*)
definition unit_BC_irem_test__2 :: IRGraph where
  "unit_BC_irem_test__2 = irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (SignedRemNode 4 1 2 None None 5), IntegerStamp 32 (-2147483647) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_irem_test__2  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ireturn;.BC_ireturn_test*)
definition unit_BC_ireturn_test :: IRGraph where
  "unit_BC_ireturn_test = irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ReturnNode (Some 1) None), VoidStamp)
  ]"
value "static_test unit_BC_ireturn_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_BC_ireturn_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_BC_ireturn_test  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_BC_ireturn_test  [(new_int 32 (256))] (new_int 32 (256))"


(* Lorg/graalvm/compiler/jtt/bytecode/BC_ishl;.BC_ishl_test*)
definition unit_BC_ishl_test :: IRGraph where
  "unit_BC_ishl_test = irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (LeftShiftNode 1 2), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (ReturnNode (Some 4) None), VoidStamp)
  ]"
value "static_test unit_BC_ishl_test  [(new_int 32 (1)), (new_int 32 (2))] (new_int 32 (4))"

value "static_test unit_BC_ishl_test  [(new_int 32 (0)), (new_int 32 (-1))] (new_int 32 (0))"

value "static_test unit_BC_ishl_test  [(new_int 32 (31)), (new_int 32 (1))] (new_int 32 (62))"

value "static_test unit_BC_ishl_test  [(new_int 32 (6)), (new_int 32 (4))] (new_int 32 (96))"

value "static_test unit_BC_ishl_test  [(new_int 32 (-2147483648)), (new_int 32 (1))] (new_int 32 (0))"

end
