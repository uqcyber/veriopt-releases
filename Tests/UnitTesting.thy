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



(* Lorg/graalvm/compiler/jtt/hotpath/HP_field02;.HP_field02_test*)
definition unit_HP_field02_test_1936 :: Program where
  "unit_HP_field02_test_1936 = Map.empty (
  ''org.graalvm.compiler.jtt.hotpath.HP_field02.test(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NewInstanceNode 3 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass'' None 21), ObjectStamp ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass'' True True False),
  (4, (ConstantNode (ObjRef None)), ObjectStamp ''null'' False False True),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (FrameState [] (Some 6) None None), IllegalStamp),
  (20, (ConstantNode (IntVal32 (0))), IntegerStamp 32 (0) (0)),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::a'' 20 (Some 7) (Some 3) 22), VoidStamp),
  (22, (StoreFieldNode 22 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::b'' 20 (Some 7) (Some 3) 23), VoidStamp),
  (23, (StoreFieldNode 23 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::c'' 20 (Some 7) (Some 3) 9), VoidStamp),
  (8, (MethodCallTargetNode ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass.run(I)I'' [3, 1]), VoidStamp),
  (9, (InvokeNode 9 8 None None (Some 10) 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (FrameState [] None None None), IllegalStamp),
  (11, (ReturnNode (Some 9) None), VoidStamp)
  ],
  ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass.run(I)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 6), VoidStamp),
  (1, (ParameterNode 0), ObjectStamp ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass'' True True False),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (IntVal32 (0))), IntegerStamp 32 (0) (0)),
  (6, (EndNode), VoidStamp),
  (7, (LoopBeginNode [6, 48] None (Some 9) 15), VoidStamp),
  (8, (ValuePhiNode 8 [4, 47] 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (IntegerLessThanNode 2 8), VoidStamp),
  (11, (BeginNode 21), VoidStamp),
  (13, (LoopExitNode 7 (Some 14) 49), VoidStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (IfNode 10 13 11), VoidStamp),
  (16, (ConstantNode (IntVal32 (5))), IntegerStamp 32 (5) (5)),
  (17, (ConstantNode (IntVal32 (6))), IntegerStamp 32 (6) (6)),
  (18, (IntegerLessThanNode 8 17), VoidStamp),
  (19, (BeginNode 22), VoidStamp),
  (20, (BeginNode 32), VoidStamp),
  (21, (IfNode 18 20 19), VoidStamp),
  (22, (LoadFieldNode 22 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::a'' (Some 1) 24), IntegerStamp 32 (-2147483648) (2147483647)),
  (23, (AddNode 8 22), IntegerStamp 32 (-2147483648) (2147483647)),
  (24, (StoreFieldNode 24 ''org.graalvm.compiler.jtt.hotpath.HP_field02$TestClass::a'' 23 (Some 25) (Some 1) 37), VoidStamp),
  (25, (FrameState [] None None None), IllegalStamp),
  (27, (ConstantNode (IntVal32 (7))), IntegerStamp 32 (7) (7)),
  (28, (ConstantNode (IntVal32 (8))), IntegerStamp 32 (8) (8)),
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
  (46, (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1)),
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
value "program_test unit_HP_field02_test_1936 ''org.graalvm.compiler.jtt.hotpath.HP_field02.test(I)I'' [(IntVal32 (40))] (IntVal32 (820))"


end
