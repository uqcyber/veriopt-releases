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


(* Lorg/graalvm/compiler/jtt/loop/Loop07_2;.Loop07_2_test*)
definition unit_Loop07_2_test :: IRGraph where
  "unit_Loop07_2_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 20] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [1, 18] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 19] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 8 1), VoidStamp),
  (12, (LoopExitNode 6 (Some 14) 21), VoidStamp),
  (13, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 20), VoidStamp),
  (16, (IfNode 10 15 12), VoidStamp),
  (17, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (18, (AddNode 7 17), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (AddNode 8 17), IntegerStamp 32 (-2147483648) (2147483647)),
  (20, (LoopEndNode 6), VoidStamp),
  (21, (ReturnNode (Some 13) None), VoidStamp)
  ]"
value "static_test unit_Loop07_2_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Loop07_2_test  [(new_int 32 (10))] (new_int 32 (20))"

value "static_test unit_Loop07_2_test  [(new_int 32 (25))] (new_int 32 (50))"


(* Lorg/graalvm/compiler/jtt/loop/Loop08;.Loop08_test*)
definition unit_Loop08_test :: IRGraph where
  "unit_Loop08_test = irgraph [
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
value "static_test unit_Loop08_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Loop08_test  [(new_int 32 (10))] (new_int 32 (45))"

value "static_test unit_Loop08_test  [(new_int 32 (25))] (new_int 32 (300))"


(* Lorg/graalvm/compiler/jtt/loop/Loop09_2;.Loop09_2_test*)
definition unit_Loop09_2_test :: IRGraph where
  "unit_Loop09_2_test = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.loop.Loop09_2::cnt'' 3 (Some 5) None 7), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (7, (EndNode), VoidStamp),
  (8, (LoopBeginNode [7, 28] None (Some 11) 18), VoidStamp),
  (9, (ValuePhiNode 9 [1, 20] 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (ValuePhiNode 10 [3, 27] 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (IntegerLessThanNode 10 1), VoidStamp),
  (14, (LoopExitNode 8 (Some 16) 29), VoidStamp),
  (15, (RefNode 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (BeginNode 22), VoidStamp),
  (18, (IfNode 12 17 14), VoidStamp),
  (19, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (20, (AddNode 9 19), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (LoadFieldNode 22 ''org.graalvm.compiler.jtt.loop.Loop09_2::cnt'' None 24), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (AddNode 22 19), IntegerStamp 32 (-2147483648) (2147483647)),
  (24, (StoreFieldNode 24 ''org.graalvm.compiler.jtt.loop.Loop09_2::cnt'' 23 (Some 26) None 28), VoidStamp),
  (25, (FrameState [] None None None), IllegalStamp),
  (26, (FrameState [] (Some 25) None None), IllegalStamp),
  (27, (AddNode 10 19), IntegerStamp 32 (-2147483648) (2147483647)),
  (28, (LoopEndNode 8), VoidStamp),
  (29, (LoadFieldNode 29 ''org.graalvm.compiler.jtt.loop.Loop09_2::cnt'' None 31), IntegerStamp 32 (-2147483648) (2147483647)),
  (30, (SubNode 15 29), IntegerStamp 32 (-2147483648) (2147483647)),
  (31, (ReturnNode (Some 30) None), VoidStamp)
  ]"
value "static_test unit_Loop09_2_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Loop09_2_test  [(new_int 32 (10))] (new_int 32 (10))"

value "static_test unit_Loop09_2_test  [(new_int 32 (25))] (new_int 32 (25))"


(* Lorg/graalvm/compiler/jtt/loop/Loop11;.Loop11_test*)
definition unit_Loop11_test :: IRGraph where
  "unit_Loop11_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 20] None (Some 9) 19), VoidStamp),
  (7, (ValuePhiNode 7 [1, 11] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 12] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (11, (AddNode 7 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (12, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (13, (IntegerLessThanNode 7 12), VoidStamp),
  (14, (BeginNode 20), VoidStamp),
  (16, (LoopExitNode 6 (Some 18) 21), VoidStamp),
  (17, (RefNode 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (IfNode 13 16 14), VoidStamp),
  (20, (LoopEndNode 6), VoidStamp),
  (21, (ReturnNode (Some 17) None), VoidStamp)
  ]"
value "static_test unit_Loop11_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Loop11_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_Loop11_test  [(new_int 32 (5))] (new_int 32 (1))"


(* Lorg/graalvm/compiler/jtt/loop/Loop14;.Loop14_test*)
definition unit_Loop14_test :: Program where
  "unit_Loop14_test = Map.empty (
  ''org.graalvm.compiler.jtt.loop.Loop14.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (MethodCallTargetNode ''org.graalvm.compiler.jtt.loop.Loop14.calc(I)I'' [1]), VoidStamp),
  (4, (InvokeNode 4 3 None None (Some 5) 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode (Some 4) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.loop.Loop14.calc(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 52] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [3, 29] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 51] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 8 1), VoidStamp),
  (12, (LoopExitNode 6 (Some 14) 53), VoidStamp),
  (13, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 10 15 12), VoidStamp),
  (17, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (18, (StoreFieldNode 18 ''org.graalvm.compiler.jtt.loop.Loop14::value'' 17 (Some 19) None 21), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (21, (EndNode), VoidStamp),
  (22, (LoopBeginNode [21, 50] None (Some 25) 32), VoidStamp),
  (23, (ValuePhiNode 23 [7, 48] 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (24, (ValuePhiNode 24 [3, 49] 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (25, (FrameState [] None None None), IllegalStamp),
  (26, (IntegerLessThanNode 24 1), VoidStamp),
  (28, (LoopExitNode 22 (Some 30) 52), VoidStamp),
  (29, (RefNode 23), IntegerStamp 32 (-2147483648) (2147483647)),
  (30, (FrameState [] None None None), IllegalStamp),
  (31, (BeginNode 34), VoidStamp),
  (32, (IfNode 26 31 28), VoidStamp),
  (34, (EndNode), VoidStamp),
  (35, (LoopBeginNode [34, 46] None (Some 37) 43), VoidStamp),
  (36, (ValuePhiNode 36 [3, 45] 35), IntegerStamp 32 (-2147483648) (2147483647)),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (IntegerLessThanNode 36 1), VoidStamp),
  (40, (LoopExitNode 35 (Some 41) 47), VoidStamp),
  (41, (FrameState [] None None None), IllegalStamp),
  (42, (BeginNode 46), VoidStamp),
  (43, (IfNode 38 42 40), VoidStamp),
  (44, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (45, (AddNode 36 44), IntegerStamp 32 (-2147483648) (2147483647)),
  (46, (LoopEndNode 35), VoidStamp),
  (47, (LoadFieldNode 47 ''org.graalvm.compiler.jtt.loop.Loop14::value'' None 50), IntegerStamp 32 (-2147483648) (2147483647)),
  (48, (AddNode 23 47), IntegerStamp 32 (-2147483648) (2147483647)),
  (49, (AddNode 24 44), IntegerStamp 32 (-2147483648) (2147483647)),
  (50, (LoopEndNode 22), VoidStamp),
  (51, (AddNode 8 44), IntegerStamp 32 (-2147483648) (2147483647)),
  (52, (LoopEndNode 6), VoidStamp),
  (53, (ReturnNode (Some 13) None), VoidStamp)
  ]
  )"
value "program_test unit_Loop14_test ''org.graalvm.compiler.jtt.loop.Loop14.test(I)I'' [(new_int 32 (1))] (new_int 32 (5))"

value "program_test unit_Loop14_test ''org.graalvm.compiler.jtt.loop.Loop14.test(I)I'' [(new_int 32 (1))] (new_int 32 (5))"


(* Lorg/graalvm/compiler/jtt/loop/Loop16;.Loop16_test*)
definition unit_Loop16_test :: Program where
  "unit_Loop16_test = Map.empty (
  ''org.graalvm.compiler.jtt.loop.Loop16.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NewInstanceNode 3 ''org.graalvm.compiler.jtt.loop.Loop16$TestClass'' None 6), ObjectStamp ''org.graalvm.compiler.jtt.loop.Loop16$TestClass'' True True False),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (MethodCallTargetNode ''org.graalvm.compiler.jtt.loop.Loop16$TestClass.run(I)I'' [3, 1]), VoidStamp),
  (6, (InvokeNode 6 5 None None (Some 7) 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (ReturnNode (Some 6) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.loop.Loop16$TestClass.run(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 6), VoidStamp),
  (1, (ParameterNode 0), ObjectStamp ''org.graalvm.compiler.jtt.loop.Loop16$TestClass'' True True False),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (EndNode), VoidStamp),
  (7, (LoopBeginNode [6, 72] None (Some 9) 15), VoidStamp),
  (8, (ValuePhiNode 8 [4, 71] 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 2 8), VoidStamp),
  (11, (BeginNode 21), VoidStamp),
  (13, (LoopExitNode 7 (Some 14) 73), VoidStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (IfNode 10 13 11), VoidStamp),
  (16, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (17, (ConstantNode (new_int 32 (6))), IntegerStamp 32 (6) (6)),
  (18, (IntegerLessThanNode 8 17), VoidStamp),
  (19, (BeginNode 23), VoidStamp),
  (20, (BeginNode 57), VoidStamp),
  (21, (IfNode 18 20 19), VoidStamp),
  (23, (EndNode), VoidStamp),
  (24, (LoopBeginNode [23, 50] None (Some 26) 32), VoidStamp),
  (25, (ValuePhiNode 25 [4, 49] 24), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (FrameState [] None None None), IllegalStamp),
  (27, (IntegerLessThanNode 25 8), VoidStamp),
  (29, (LoopExitNode 24 (Some 30) 62), VoidStamp),
  (30, (FrameState [] None None None), IllegalStamp),
  (31, (BeginNode 33), VoidStamp),
  (32, (IfNode 27 31 29), VoidStamp),
  (33, (LoadFieldNode 33 ''org.graalvm.compiler.jtt.loop.Loop16$TestClass::a'' (Some 1) 35), IntegerStamp 32 (-2147483648) (2147483647)),
  (34, (AddNode 8 33), IntegerStamp 32 (-2147483648) (2147483647)),
  (35, (StoreFieldNode 35 ''org.graalvm.compiler.jtt.loop.Loop16$TestClass::a'' 34 (Some 36) (Some 1) 37), VoidStamp),
  (36, (FrameState [] None None None), IllegalStamp),
  (37, (LoadFieldNode 37 ''org.graalvm.compiler.jtt.loop.Loop16$TestClass::a'' (Some 1) 47), IntegerStamp 32 (-2147483648) (2147483647)),
  (38, (ConstantNode (new_int 32 (500))), IntegerStamp 32 (500) (500)),
  (39, (ConstantNode (new_int 32 (501))), IntegerStamp 32 (501) (501)),
  (40, (IntegerLessThanNode 37 39), VoidStamp),
  (42, (LoopExitNode 24 (Some 43) 44), VoidStamp),
  (43, (FrameState [] None None None), IllegalStamp),
  (44, (LoopExitNode 7 (Some 45) 75), VoidStamp),
  (45, (FrameState [] None None None), IllegalStamp),
  (46, (BeginNode 50), VoidStamp),
  (47, (IfNode 40 46 42), VoidStamp),
  (48, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (49, (AddNode 25 48), IntegerStamp 32 (-2147483648) (2147483647)),
  (50, (LoopEndNode 24), VoidStamp),
  (52, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (53, (ConstantNode (new_int 32 (8))), IntegerStamp 32 (8) (8)),
  (54, (IntegerLessThanNode 8 53), VoidStamp),
  (55, (BeginNode 58), VoidStamp),
  (56, (BeginNode 65), VoidStamp),
  (57, (IfNode 54 56 55), VoidStamp),
  (58, (LoadFieldNode 58 ''org.graalvm.compiler.jtt.loop.Loop16$TestClass::b'' (Some 1) 60), IntegerStamp 32 (-2147483648) (2147483647)),
  (59, (AddNode 8 58), IntegerStamp 32 (-2147483648) (2147483647)),
  (60, (StoreFieldNode 60 ''org.graalvm.compiler.jtt.loop.Loop16$TestClass::b'' 59 (Some 61) (Some 1) 64), VoidStamp),
  (61, (FrameState [] None None None), IllegalStamp),
  (62, (EndNode), VoidStamp),
  (63, (MergeNode [62, 64, 69] (Some 70) 72), VoidStamp),
  (64, (EndNode), VoidStamp),
  (65, (LoadFieldNode 65 ''org.graalvm.compiler.jtt.loop.Loop16$TestClass::c'' (Some 1) 67), IntegerStamp 32 (-2147483648) (2147483647)),
  (66, (AddNode 8 65), IntegerStamp 32 (-2147483648) (2147483647)),
  (67, (StoreFieldNode 67 ''org.graalvm.compiler.jtt.loop.Loop16$TestClass::c'' 66 (Some 68) (Some 1) 69), VoidStamp),
  (68, (FrameState [] None None None), IllegalStamp),
  (69, (EndNode), VoidStamp),
  (70, (FrameState [] None None None), IllegalStamp),
  (71, (AddNode 8 48), IntegerStamp 32 (-2147483648) (2147483647)),
  (72, (LoopEndNode 7), VoidStamp),
  (73, (EndNode), VoidStamp),
  (74, (MergeNode [73, 75] (Some 76) 77), VoidStamp),
  (75, (EndNode), VoidStamp),
  (76, (FrameState [] None None None), IllegalStamp),
  (77, (LoadFieldNode 77 ''org.graalvm.compiler.jtt.loop.Loop16$TestClass::a'' (Some 1) 78), IntegerStamp 32 (-2147483648) (2147483647)),
  (78, (LoadFieldNode 78 ''org.graalvm.compiler.jtt.loop.Loop16$TestClass::b'' (Some 1) 80), IntegerStamp 32 (-2147483648) (2147483647)),
  (79, (AddNode 77 78), IntegerStamp 32 (-2147483648) (2147483647)),
  (80, (LoadFieldNode 80 ''org.graalvm.compiler.jtt.loop.Loop16$TestClass::c'' (Some 1) 82), IntegerStamp 32 (-2147483648) (2147483647)),
  (81, (AddNode 79 80), IntegerStamp 32 (-2147483648) (2147483647)),
  (82, (ReturnNode (Some 81) None), VoidStamp)
  ]
  )"
value "program_test unit_Loop16_test ''org.graalvm.compiler.jtt.loop.Loop16.test(I)I'' [(new_int 32 (40))] (new_int 32 (526))"


(* Lorg/graalvm/compiler/jtt/loop/LoopEscape;.LoopEscape_test0*)
definition unit_LoopEscape_test0 :: Program where
  "unit_LoopEscape_test0 = Map.empty (
  ''org.graalvm.compiler.jtt.loop.LoopEscape.test0(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NewInstanceNode 3 ''org.graalvm.compiler.jtt.loop.LoopEscape$L'' None 6), ObjectStamp ''org.graalvm.compiler.jtt.loop.LoopEscape$L'' True True False),
  (4, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' 4 (Some 8) (Some 3) 9), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (FrameState [] (Some 7) None None), IllegalStamp),
  (9, (StoreFieldNode 9 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::b'' 4 (Some 10) (Some 3) 11), VoidStamp),
  (10, (FrameState [] (Some 7) None None), IllegalStamp),
  (11, (StoreFieldNode 11 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::c'' 4 (Some 12) (Some 3) 15), VoidStamp),
  (12, (FrameState [] (Some 7) None None), IllegalStamp),
  (13, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (15, (EndNode), VoidStamp),
  (16, (LoopBeginNode [15, 39] None (Some 18) 24), VoidStamp),
  (17, (ValuePhiNode 17 [13, 38] 16), IntegerStamp 32 (-2147483648) (2147483647)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (IntegerLessThanNode 17 1), VoidStamp),
  (21, (LoopExitNode 16 (Some 22) 40), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (BeginNode 25), VoidStamp),
  (24, (IfNode 19 23 21), VoidStamp),
  (25, (LoadFieldNode 25 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' (Some 3) 28), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (27, (AddNode 25 26), IntegerStamp 32 (-2147483648) (2147483647)),
  (28, (StoreFieldNode 28 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' 27 (Some 29) (Some 3) 30), VoidStamp),
  (29, (FrameState [] None None None), IllegalStamp),
  (30, (LoadFieldNode 30 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::b'' (Some 3) 33), IntegerStamp 32 (-2147483648) (2147483647)),
  (31, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (32, (AddNode 30 31), IntegerStamp 32 (-2147483648) (2147483647)),
  (33, (StoreFieldNode 33 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::b'' 32 (Some 34) (Some 3) 36), VoidStamp),
  (34, (FrameState [] None None None), IllegalStamp),
  (35, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (36, (StoreFieldNode 36 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::c'' 35 (Some 37) (Some 3) 39), VoidStamp),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (AddNode 17 26), IntegerStamp 32 (-2147483648) (2147483647)),
  (39, (LoopEndNode 16), VoidStamp),
  (40, (LoadFieldNode 40 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' (Some 3) 41), IntegerStamp 32 (-2147483648) (2147483647)),
  (41, (LoadFieldNode 41 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::b'' (Some 3) 45), IntegerStamp 32 (-2147483648) (2147483647)),
  (42, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (43, (MulNode 41 42), IntegerStamp 32 (-2147483648) (2147483647)),
  (44, (AddNode 40 43), IntegerStamp 32 (-2147483648) (2147483647)),
  (45, (LoadFieldNode 45 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::c'' (Some 3) 49), IntegerStamp 32 (-2147483648) (2147483647)),
  (46, (ConstantNode (new_int 32 (100))), IntegerStamp 32 (100) (100)),
  (47, (MulNode 45 46), IntegerStamp 32 (-2147483648) (2147483647)),
  (48, (AddNode 44 47), IntegerStamp 32 (-2147483648) (2147483647)),
  (49, (ReturnNode (Some 48) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.loop.LoopEscape.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.loop.LoopEscape$L'' None 7), ObjectStamp ''org.graalvm.compiler.jtt.loop.LoopEscape$L'' True True False),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (StoreFieldNode 7 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' 3 (Some 9) (Some 2) 10), VoidStamp),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (FrameState [] (Some 8) None None), IllegalStamp),
  (10, (StoreFieldNode 10 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::b'' 4 (Some 11) (Some 2) 12), VoidStamp),
  (11, (FrameState [] (Some 8) None None), IllegalStamp),
  (12, (StoreFieldNode 12 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::c'' 5 (Some 13) (Some 2) 14), VoidStamp),
  (13, (FrameState [] (Some 8) None None), IllegalStamp),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.jtt.loop.LoopEscape::ll'' 2 (Some 15) None 16), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.loop.LoopEscape.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_LoopEscape_test0 ''org.graalvm.compiler.jtt.loop.LoopEscape.test0(I)I'' [(new_int 32 (0))] (new_int 32 (555))"

value "program_test unit_LoopEscape_test0 ''org.graalvm.compiler.jtt.loop.LoopEscape.test0(I)I'' [(new_int 32 (1))] (new_int 32 (446))"

value "program_test unit_LoopEscape_test0 ''org.graalvm.compiler.jtt.loop.LoopEscape.test0(I)I'' [(new_int 32 (2))] (new_int 32 (437))"

value "program_test unit_LoopEscape_test0 ''org.graalvm.compiler.jtt.loop.LoopEscape.test0(I)I'' [(new_int 32 (5))] (new_int 32 (410))"


(* Lorg/graalvm/compiler/jtt/loop/LoopEscape;.LoopEscape_test1*)
definition unit_LoopEscape_test1 :: Program where
  "unit_LoopEscape_test1 = Map.empty (
  ''org.graalvm.compiler.jtt.loop.LoopEscape.test1(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NewInstanceNode 3 ''org.graalvm.compiler.jtt.loop.LoopEscape$L'' None 6), ObjectStamp ''org.graalvm.compiler.jtt.loop.LoopEscape$L'' True True False),
  (4, (ConstantNode (new_int 32 (5))), IntegerStamp 32 (5) (5)),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' 4 (Some 8) (Some 3) 9), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (FrameState [] (Some 7) None None), IllegalStamp),
  (9, (StoreFieldNode 9 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::b'' 4 (Some 10) (Some 3) 11), VoidStamp),
  (10, (FrameState [] (Some 7) None None), IllegalStamp),
  (11, (StoreFieldNode 11 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::c'' 4 (Some 12) (Some 3) 15), VoidStamp),
  (12, (FrameState [] (Some 7) None None), IllegalStamp),
  (13, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (15, (EndNode), VoidStamp),
  (16, (LoopBeginNode [15, 55] None (Some 18) 24), VoidStamp),
  (17, (ValuePhiNode 17 [13, 54] 16), IntegerStamp 32 (-2147483648) (2147483647)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (IntegerLessThanNode 17 1), VoidStamp),
  (21, (LoopExitNode 16 (Some 22) 56), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (BeginNode 25), VoidStamp),
  (24, (IfNode 19 23 21), VoidStamp),
  (25, (LoadFieldNode 25 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' (Some 3) 27), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (27, (SignedRemNode 27 25 26 None None 31), IntegerStamp 32 (-1) (1)),
  (28, (IntegerEqualsNode 27 13), VoidStamp),
  (29, (BeginNode 46), VoidStamp),
  (30, (BeginNode 32), VoidStamp),
  (31, (IfNode 28 30 29), VoidStamp),
  (32, (LoadFieldNode 32 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' (Some 3) 35), IntegerStamp 32 (-2147483648) (2147483647)),
  (33, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (34, (AddNode 32 33), IntegerStamp 32 (-2147483648) (2147483647)),
  (35, (StoreFieldNode 35 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' 34 (Some 36) (Some 3) 37), VoidStamp),
  (36, (FrameState [] None None None), IllegalStamp),
  (37, (LoadFieldNode 37 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::b'' (Some 3) 40), IntegerStamp 32 (-2147483648) (2147483647)),
  (38, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (39, (AddNode 37 38), IntegerStamp 32 (-2147483648) (2147483647)),
  (40, (StoreFieldNode 40 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::b'' 39 (Some 41) (Some 3) 43), VoidStamp),
  (41, (FrameState [] None None None), IllegalStamp),
  (42, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (43, (StoreFieldNode 43 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::c'' 42 (Some 44) (Some 3) 50), VoidStamp),
  (44, (FrameState [] None None None), IllegalStamp),
  (46, (LoadFieldNode 46 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' (Some 3) 48), IntegerStamp 32 (-2147483648) (2147483647)),
  (47, (AddNode 46 33), IntegerStamp 32 (-2147483648) (2147483647)),
  (48, (StoreFieldNode 48 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' 47 (Some 49) (Some 3) 52), VoidStamp),
  (49, (FrameState [] None None None), IllegalStamp),
  (50, (EndNode), VoidStamp),
  (51, (MergeNode [50, 52] (Some 53) 55), VoidStamp),
  (52, (EndNode), VoidStamp),
  (53, (FrameState [] None None None), IllegalStamp),
  (54, (AddNode 17 33), IntegerStamp 32 (-2147483648) (2147483647)),
  (55, (LoopEndNode 16), VoidStamp),
  (56, (LoadFieldNode 56 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' (Some 3) 57), IntegerStamp 32 (-2147483648) (2147483647)),
  (57, (LoadFieldNode 57 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::b'' (Some 3) 61), IntegerStamp 32 (-2147483648) (2147483647)),
  (58, (ConstantNode (new_int 32 (10))), IntegerStamp 32 (10) (10)),
  (59, (MulNode 57 58), IntegerStamp 32 (-2147483648) (2147483647)),
  (60, (AddNode 56 59), IntegerStamp 32 (-2147483648) (2147483647)),
  (61, (LoadFieldNode 61 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::c'' (Some 3) 65), IntegerStamp 32 (-2147483648) (2147483647)),
  (62, (ConstantNode (new_int 32 (100))), IntegerStamp 32 (100) (100)),
  (63, (MulNode 61 62), IntegerStamp 32 (-2147483648) (2147483647)),
  (64, (AddNode 60 63), IntegerStamp 32 (-2147483648) (2147483647)),
  (65, (ReturnNode (Some 64) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.loop.LoopEscape.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.loop.LoopEscape$L'' None 7), ObjectStamp ''org.graalvm.compiler.jtt.loop.LoopEscape$L'' True True False),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (StoreFieldNode 7 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::a'' 3 (Some 9) (Some 2) 10), VoidStamp),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (FrameState [] (Some 8) None None), IllegalStamp),
  (10, (StoreFieldNode 10 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::b'' 4 (Some 11) (Some 2) 12), VoidStamp),
  (11, (FrameState [] (Some 8) None None), IllegalStamp),
  (12, (StoreFieldNode 12 ''org.graalvm.compiler.jtt.loop.LoopEscape$L::c'' 5 (Some 13) (Some 2) 14), VoidStamp),
  (13, (FrameState [] (Some 8) None None), IllegalStamp),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.jtt.loop.LoopEscape::ll'' 2 (Some 15) None 16), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.loop.LoopEscape.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_LoopEscape_test1 ''org.graalvm.compiler.jtt.loop.LoopEscape.test1(I)I'' [(new_int 32 (0))] (new_int 32 (555))"

value "program_test unit_LoopEscape_test1 ''org.graalvm.compiler.jtt.loop.LoopEscape.test1(I)I'' [(new_int 32 (1))] (new_int 32 (556))"

value "program_test unit_LoopEscape_test1 ''org.graalvm.compiler.jtt.loop.LoopEscape.test1(I)I'' [(new_int 32 (2))] (new_int 32 (447))"


(* Lorg/graalvm/compiler/jtt/loop/LoopInline;.LoopInline_test*)
definition unit_LoopInline_test :: Program where
  "unit_LoopInline_test = Map.empty (
  ''org.graalvm.compiler.jtt.loop.LoopInline.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 32] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [3, 20] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 31] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 8 1), VoidStamp),
  (12, (LoopExitNode 6 (Some 14) 38), VoidStamp),
  (13, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 18), VoidStamp),
  (16, (IfNode 10 15 12), VoidStamp),
  (17, (MethodCallTargetNode ''org.graalvm.compiler.jtt.loop.LoopInline.foo(I)I'' [8]), VoidStamp),
  (18, (InvokeNode 18 17 None None (Some 19) 29), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (AddNode 7 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (ConstantNode (new_int 32 (15))), IntegerStamp 32 (15) (15)),
  (22, (ConstantNode (new_int 32 (16))), IntegerStamp 32 (16) (16)),
  (23, (IntegerLessThanNode 20 22), VoidStamp),
  (25, (LoopExitNode 6 (Some 27) 35), VoidStamp),
  (26, (RefNode 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (27, (FrameState [] None None None), IllegalStamp),
  (28, (BeginNode 32), VoidStamp),
  (29, (IfNode 23 28 25), VoidStamp),
  (30, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (31, (AddNode 8 30), IntegerStamp 32 (-2147483648) (2147483647)),
  (32, (LoopEndNode 6), VoidStamp),
  (33, (ConstantNode (new_int 32 (3))), IntegerStamp 32 (3) (3)),
  (34, (MethodCallTargetNode ''org.graalvm.compiler.jtt.loop.LoopInline.foo(I)I'' [33]), VoidStamp),
  (35, (InvokeNode 35 34 None None (Some 36) 40), IntegerStamp 32 (-2147483648) (2147483647)),
  (36, (FrameState [] None None None), IllegalStamp),
  (37, (SubNode 26 35), IntegerStamp 32 (-2147483648) (2147483647)),
  (38, (EndNode), VoidStamp),
  (39, (MergeNode [38, 40] (Some 42) 43), VoidStamp),
  (40, (EndNode), VoidStamp),
  (41, (ValuePhiNode 41 [13, 37] 39), IntegerStamp 32 (-2147483648) (2147483647)),
  (42, (FrameState [] None None None), IllegalStamp),
  (43, (ReturnNode (Some 41) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.loop.LoopInline.foo(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 28] None (Some 9) 16), VoidStamp),
  (7, (ValuePhiNode 7 [3, 17] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 27] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 8 1), VoidStamp),
  (12, (LoopExitNode 6 (Some 14) 33), VoidStamp),
  (13, (RefNode 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (BeginNode 25), VoidStamp),
  (16, (IfNode 10 15 12), VoidStamp),
  (17, (AddNode 7 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (18, (ConstantNode (new_int 32 (4))), IntegerStamp 32 (4) (4)),
  (19, (IntegerEqualsNode 8 18), VoidStamp),
  (20, (BeginNode 28), VoidStamp),
  (22, (LoopExitNode 6 (Some 24) 30), VoidStamp),
  (23, (RefNode 17), IntegerStamp 32 (-2147483648) (2147483647)),
  (24, (FrameState [] None None None), IllegalStamp),
  (25, (IfNode 19 22 20), VoidStamp),
  (26, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (27, (AddNode 8 26), IntegerStamp 32 (-2147483648) (2147483647)),
  (28, (LoopEndNode 6), VoidStamp),
  (29, (MethodCallTargetNode ''org.graalvm.compiler.jtt.loop.LoopInline.foo2(I)I'' [23]), VoidStamp),
  (30, (InvokeNode 30 29 None None (Some 31) 35), IntegerStamp 32 (-2147483648) (2147483647)),
  (31, (FrameState [] None None None), IllegalStamp),
  (32, (AddNode 23 30), IntegerStamp 32 (-2147483648) (2147483647)),
  (33, (EndNode), VoidStamp),
  (34, (MergeNode [33, 35] (Some 37) 38), VoidStamp),
  (35, (EndNode), VoidStamp),
  (36, (ValuePhiNode 36 [13, 32] 34), IntegerStamp 32 (-2147483648) (2147483647)),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (ReturnNode (Some 36) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.loop.LoopInline.foo2(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (5, (EndNode), VoidStamp),
  (6, (LoopBeginNode [5, 22] None (Some 9) 17), VoidStamp),
  (7, (ValuePhiNode 7 [1, 21] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (ValuePhiNode 8 [3, 19] 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (11, (IntegerLessThanNode 7 10), VoidStamp),
  (12, (BeginNode 22), VoidStamp),
  (14, (LoopExitNode 6 (Some 16) 23), VoidStamp),
  (15, (RefNode 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (IfNode 11 14 12), VoidStamp),
  (18, (MulNode 7 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (19, (AddNode 8 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (20, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (21, (AddNode 7 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (LoopEndNode 6), VoidStamp),
  (23, (ReturnNode (Some 15) None), VoidStamp)
  ]
  )"
value "program_test unit_LoopInline_test ''org.graalvm.compiler.jtt.loop.LoopInline.test(I)I'' [(new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_LoopInline_test ''org.graalvm.compiler.jtt.loop.LoopInline.test(I)I'' [(new_int 32 (10))] (new_int 32 (402))"


(* Lorg/graalvm/compiler/jtt/loop/LoopUnroll;.LoopUnroll_test*)
definition unit_LoopUnroll_test :: IRGraph where
  "unit_LoopUnroll_test = irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (2))), IntegerStamp 32 (2) (2)),
  (4, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (6, (EndNode), VoidStamp),
  (7, (LoopBeginNode [6, 26] None (Some 11) 19), VoidStamp),
  (8, (ValuePhiNode 8 [3, 21] 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (ValuePhiNode 9 [1, 23] 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (ValuePhiNode 10 [4, 25] 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (FrameState [] None None None), IllegalStamp),
  (12, (ConstantNode (new_int 32 (7))), IntegerStamp 32 (7) (7)),
  (13, (IntegerLessThanNode 10 12), VoidStamp),
  (15, (LoopExitNode 7 (Some 17) 27), VoidStamp),
  (16, (RefNode 8), IntegerStamp 32 (-2147483648) (2147483647)),
  (17, (FrameState [] None None None), IllegalStamp),
  (18, (BeginNode 23), VoidStamp),
  (19, (IfNode 13 18 15), VoidStamp),
  (20, (AddNode 9 3), IntegerStamp 32 (-2147483648) (2147483647)),
  (21, (MulNode 8 20), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (ConstantNode (new_int 32 (50))), IntegerStamp 32 (50) (50)),
  (23, (SignedDivNode 23 9 22 None None 26), IntegerStamp 32 (-42949672) (42949672)),
  (24, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (25, (AddNode 10 24), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (LoopEndNode 7), VoidStamp),
  (27, (ReturnNode (Some 16) None), VoidStamp)
  ]"
value "static_test unit_LoopUnroll_test  [(new_int 32 (42))] (new_int 32 (5632))"


(* Lorg/graalvm/compiler/jtt/lang/Math_abs;.Math_abs_testAbsI*)
definition unit_Math_abs_testAbsI :: IRGraph where
  "unit_Math_abs_testAbsI = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (AbsNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Math_abs_testAbsI  [(new_int 32 (-2147483648))] (new_int 32 (-2147483648))"

value "static_test unit_Math_abs_testAbsI  [(new_int 32 (-326543323))] (new_int 32 (326543323))"

value "static_test unit_Math_abs_testAbsI  [(new_int 32 (-21325))] (new_int 32 (21325))"

value "static_test unit_Math_abs_testAbsI  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Math_abs_testAbsI  [(new_int 32 (5432))] (new_int 32 (5432))"

value "static_test unit_Math_abs_testAbsI  [(new_int 32 (352438548))] (new_int 32 (352438548))"

value "static_test unit_Math_abs_testAbsI  [(new_int 32 (2147483647))] (new_int 32 (2147483647))"


(* Lorg/graalvm/compiler/jtt/lang/Math_abs;.Math_abs_testAbsL*)
definition unit_Math_abs_testAbsL :: IRGraph where
  "unit_Math_abs_testAbsL = irgraph [
  (0, (StartNode (Some 2) 4), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (AbsNode 1), IntegerStamp 64 (-9223372036854775808) (9223372036854775807)),
  (4, (ReturnNode (Some 3) None), VoidStamp)
  ]"
value "static_test unit_Math_abs_testAbsL  [(IntVal 64 (-9223372036854775808))] (IntVal 64 (-9223372036854775808))"

value "static_test unit_Math_abs_testAbsL  [(IntVal 64 (-425423654342))] (IntVal 64 (425423654342))"

value "static_test unit_Math_abs_testAbsL  [(IntVal 64 (-21543224))] (IntVal 64 (21543224))"

value "static_test unit_Math_abs_testAbsL  [(IntVal 64 (0))] (IntVal 64 (0))"

value "static_test unit_Math_abs_testAbsL  [(IntVal 64 (1325488))] (IntVal 64 (1325488))"

value "static_test unit_Math_abs_testAbsL  [(IntVal 64 (313567897765))] (IntVal 64 (313567897765))"

value "static_test unit_Math_abs_testAbsL  [(IntVal 64 (9223372036854775807))] (IntVal 64 (9223372036854775807))"


(* Lorg/graalvm/compiler/nodes/test/NarrowTest;.NarrowTest_snippet0*)
definition unit_NarrowTest_snippet0 :: IRGraph where
  "unit_NarrowTest_snippet0 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (4, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (5, (SignExtendNode 8 32 4), IntegerStamp 32 (-128) (127)),
  (6, (ConstantNode (new_int 32 (-127))), IntegerStamp 32 (-127) (-127)),
  (7, (SignedDivNode 7 5 6 None None 14), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (NarrowNode 32 8 7), IntegerStamp 8 (-128) (127)),
  (9, (SignExtendNode 8 32 8), IntegerStamp 32 (-128) (127)),
  (10, (IntegerLessThanNode 9 3), VoidStamp),
  (11, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (12, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (0) (1)),
  (14, (ReturnNode (Some 13) None), VoidStamp)
  ]"
value "static_test unit_NarrowTest_snippet0  [(new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/Narrow_byte01;.Narrow_byte01_test*)
definition unit_Narrow_byte01_test :: IRGraph where
  "unit_Narrow_byte01_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (4, (SignExtendNode 8 32 3), IntegerStamp 32 (-128) (127)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.jtt.optimize.Narrow_byte01::val'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.jtt.optimize.Narrow_byte01::val'' None 8), IntegerStamp 32 (-128) (127)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_Narrow_byte01_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Narrow_byte01_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_Narrow_byte01_test  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_Narrow_byte01_test  [(new_int 32 (110))] (new_int 32 (110))"


(* Lorg/graalvm/compiler/jtt/optimize/Narrow_byte02;.Narrow_byte02_test*)
definition unit_Narrow_byte02_test :: Program where
  "unit_Narrow_byte02_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.Narrow_byte02.test(B)B'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (LoadFieldNode 3 ''org.graalvm.compiler.jtt.optimize.Narrow_byte02::val'' None 6), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Narrow_byte02$Byte'' True False False),
  (4, (NarrowNode 32 8 1), IntegerStamp 8 (-128) (127)),
  (5, (SignExtendNode 8 32 4), IntegerStamp 32 (-128) (127)),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.jtt.optimize.Narrow_byte02$Byte::foo'' 5 (Some 7) (Some 3) 8), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (LoadFieldNode 8 ''org.graalvm.compiler.jtt.optimize.Narrow_byte02::val'' None 9), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Narrow_byte02$Byte'' True False False),
  (9, (LoadFieldNode 9 ''org.graalvm.compiler.jtt.optimize.Narrow_byte02$Byte::foo'' (Some 8) 10), IntegerStamp 32 (-128) (127)),
  (10, (ReturnNode (Some 9) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Narrow_byte02.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.optimize.Narrow_byte02$Byte'' None 4), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Narrow_byte02$Byte'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.optimize.Narrow_byte02::val'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Narrow_byte02.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_Narrow_byte02_test ''org.graalvm.compiler.jtt.optimize.Narrow_byte02.test(B)B'' [(new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_Narrow_byte02_test ''org.graalvm.compiler.jtt.optimize.Narrow_byte02.test(B)B'' [(new_int 32 (1))] (new_int 32 (1))"

value "program_test unit_Narrow_byte02_test ''org.graalvm.compiler.jtt.optimize.Narrow_byte02.test(B)B'' [(new_int 32 (-1))] (new_int 32 (-1))"

value "program_test unit_Narrow_byte02_test ''org.graalvm.compiler.jtt.optimize.Narrow_byte02.test(B)B'' [(new_int 32 (110))] (new_int 32 (110))"


(* Lorg/graalvm/compiler/jtt/optimize/Narrow_byte04;.Narrow_byte04_test*)
definition unit_Narrow_byte04_test :: IRGraph where
  "unit_Narrow_byte04_test = irgraph [
  (0, (StartNode (Some 2) 14), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (240))), IntegerStamp 32 (240) (240)),
  (4, (AndNode 1 3), IntegerStamp 32 (0) (240)),
  (5, (NarrowNode 32 8 4), IntegerStamp 8 (-128) (112)),
  (6, (SignExtendNode 8 32 5), IntegerStamp 32 (-128) (112)),
  (7, (ConstantNode (new_int 32 (15))), IntegerStamp 32 (15) (15)),
  (8, (AndNode 1 7), IntegerStamp 32 (0) (15)),
  (9, (NarrowNode 32 8 8), IntegerStamp 8 (0) (15)),
  (10, (ConstantNode (new_int 32 (-80))), IntegerStamp 32 (-80) (-80)),
  (11, (IntegerEqualsNode 6 10), VoidStamp),
  (12, (BeginNode 18), VoidStamp),
  (13, (BeginNode 16), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode [16, 18] (Some 20) 23), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (ValuePhiNode 19 [8, 1] 17), IntegerStamp 32 (-2147483648) (2147483647)),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (NarrowNode 32 8 19), IntegerStamp 8 (-128) (127)),
  (22, (SignExtendNode 8 32 21), IntegerStamp 32 (-128) (127)),
  (23, (ReturnNode (Some 22) None), VoidStamp)
  ]"
value "static_test unit_Narrow_byte04_test  [(new_int 32 (-79))] (new_int 32 (1))"

value "static_test unit_Narrow_byte04_test  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_Narrow_byte04_test  [(new_int 32 (0))] (new_int 32 (0))"


(* Lorg/graalvm/compiler/jtt/optimize/Narrow_char01;.Narrow_char01_test*)
definition unit_Narrow_char01_test :: IRGraph where
  "unit_Narrow_char01_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (ZeroExtendNode 16 32 3), IntegerStamp 32 (0) (65535)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.jtt.optimize.Narrow_char01::val'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.jtt.optimize.Narrow_char01::val'' None 8), IntegerStamp 32 (0) (65535)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_Narrow_char01_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Narrow_char01_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_Narrow_char01_test  [(new_int 32 (255))] (new_int 32 (255))"

value "static_test unit_Narrow_char01_test  [(new_int 32 (65000))] (new_int 32 (65000))"


(* Lorg/graalvm/compiler/jtt/optimize/Narrow_char02;.Narrow_char02_test*)
definition unit_Narrow_char02_test :: Program where
  "unit_Narrow_char02_test = Map.empty (
  ''org.graalvm.compiler.jtt.optimize.Narrow_char02.test(C)C'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (LoadFieldNode 3 ''org.graalvm.compiler.jtt.optimize.Narrow_char02::val'' None 6), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Narrow_char02$Char'' True False False),
  (4, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (5, (ZeroExtendNode 16 32 4), IntegerStamp 32 (0) (65535)),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.jtt.optimize.Narrow_char02$Char::foo'' 5 (Some 7) (Some 3) 8), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (LoadFieldNode 8 ''org.graalvm.compiler.jtt.optimize.Narrow_char02::val'' None 9), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Narrow_char02$Char'' True False False),
  (9, (LoadFieldNode 9 ''org.graalvm.compiler.jtt.optimize.Narrow_char02$Char::foo'' (Some 8) 10), IntegerStamp 32 (0) (65535)),
  (10, (ReturnNode (Some 9) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.optimize.Narrow_char02.<clinit>()V'' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 2), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (NewInstanceNode 2 ''org.graalvm.compiler.jtt.optimize.Narrow_char02$Char'' None 4), ObjectStamp ''org.graalvm.compiler.jtt.optimize.Narrow_char02$Char'' True True False),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (StoreFieldNode 4 ''org.graalvm.compiler.jtt.optimize.Narrow_char02::val'' 2 (Some 5) None 6), VoidStamp),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (ReturnNode None None), VoidStamp)
  ],
  '''' \<mapsto> irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (MethodCallTargetNode ''org.graalvm.compiler.jtt.optimize.Narrow_char02.<clinit>()V'' []), VoidStamp),
  (3, (InvokeNode 3 2 None None (Some 4) 5), VoidStamp),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ReturnNode None None), VoidStamp)
  ]
  )"
value "program_test unit_Narrow_char02_test ''org.graalvm.compiler.jtt.optimize.Narrow_char02.test(C)C'' [(new_int 32 (0))] (new_int 32 (0))"

value "program_test unit_Narrow_char02_test ''org.graalvm.compiler.jtt.optimize.Narrow_char02.test(C)C'' [(new_int 32 (1))] (new_int 32 (1))"

value "program_test unit_Narrow_char02_test ''org.graalvm.compiler.jtt.optimize.Narrow_char02.test(C)C'' [(new_int 32 (255))] (new_int 32 (255))"

value "program_test unit_Narrow_char02_test ''org.graalvm.compiler.jtt.optimize.Narrow_char02.test(C)C'' [(new_int 32 (65000))] (new_int 32 (65000))"


(* Lorg/graalvm/compiler/jtt/optimize/Narrow_short01;.Narrow_short01_test*)
definition unit_Narrow_short01_test :: IRGraph where
  "unit_Narrow_short01_test = irgraph [
  (0, (StartNode (Some 2) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NarrowNode 32 16 1), IntegerStamp 16 (-32768) (32767)),
  (4, (SignExtendNode 16 32 3), IntegerStamp 32 (-32768) (32767)),
  (5, (StoreFieldNode 5 ''org.graalvm.compiler.jtt.optimize.Narrow_short01::val'' 4 (Some 6) None 7), VoidStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.jtt.optimize.Narrow_short01::val'' None 8), IntegerStamp 32 (-32768) (32767)),
  (8, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_Narrow_short01_test  [(new_int 32 (0))] (new_int 32 (0))"

value "static_test unit_Narrow_short01_test  [(new_int 32 (1))] (new_int 32 (1))"

value "static_test unit_Narrow_short01_test  [(new_int 32 (-1))] (new_int 32 (-1))"

value "static_test unit_Narrow_short01_test  [(new_int 32 (23110))] (new_int 32 (23110))"

end
