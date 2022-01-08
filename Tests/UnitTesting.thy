section \<open>Testing of IR Semantics based on GraalVM Unit Tests\<close>

theory UnitTesting
  imports
    Semantics.IRStepObj
    (*Parsing*)
begin

declare [[ML_source_trace, ML_debugger]]

inductive static_test :: "IRGraph \<Rightarrow> Value list \<Rightarrow> Value \<Rightarrow> bool"
  where
  "\<lbrakk>config0 = (g, 0, new_map_state, ps);
    (\<lambda>x. None) \<turnstile> ([config0, config0], new_heap) | [] \<longrightarrow>* ((end # xs), heap) | l \<rbrakk>
    \<Longrightarrow> static_test g ps ((prod.fst(prod.snd(prod.snd end))) 0)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as testE) static_test .

(* get the return value of the top-most function *)
fun get_result :: "(IRGraph \<times> ID \<times> MapState \<times> Params) \<Rightarrow> Value" where
  "get_result (g,i,m,p) = m 0"
(* export_code get_result *)


(* object_test and program_test run a static initialisation block first
   (to initialise static fields etc.), then a named method.
*)
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

(* Lorg/graalvm/compiler/core/test/VeriOptFactorialTest;.factAsAnObject*)
definition unit_factAsAnObject_2 :: Program where
  "unit_factAsAnObject_2 = Map.empty (
  ''org.graalvm.compiler.core.test.VeriOptFactorialTest.factAsAnObject(I)Lorg/graalvm/compiler/core/test/VeriOptFactorialTest$FactResult;'' \<mapsto> irgraph [
  (0, (StartNode (Some 2) 3), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (NewInstanceNode 3 ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult'' None 6), ObjectStamp ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult'' True True False),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1)),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult::value'' 5 (Some 8) (Some 3) 10), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (FrameState [] (Some 7) None None), IllegalStamp),
  (10, (EndNode), VoidStamp),
  (11, (LoopBeginNode [10] None (Some 13) 20), VoidStamp),
  (12, (ValuePhiNode 12 [1, 25] 11), IntegerStamp 32 (-2147483648) (2147483647)),
  (13, (FrameState [] None None None), IllegalStamp),
  (14, (ConstantNode (IntVal32 (2))), IntegerStamp 32 (2) (2)),
  (15, (IntegerLessThanNode 12 14), VoidStamp),
  (16, (BeginNode 22), VoidStamp),
  (18, (LoopExitNode 11 (Some 19) 27), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (IfNode 15 18 16), VoidStamp),
  (21, (MethodCallTargetNode ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult.multiply(I)V'' [3, 12]), VoidStamp),
  (22, (InvokeNode 22 21 None None (Some 23) 26), VoidStamp),
  (23, (FrameState [] None None None), IllegalStamp),
  (24, (ConstantNode (IntVal32 (-1))), IntegerStamp 32 (-1) (-1)),
  (25, (AddNode 12 24), IntegerStamp 32 (-2147483648) (2147483647)),
  (26, (LoopEndNode 11), VoidStamp),
  (27, (ReturnNode (Some 3) None), VoidStamp)
  ],
  ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult.multiply(I)V'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 4), VoidStamp),
  (1, (ParameterNode 0), ObjectStamp ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult'' True True False),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (LoadFieldNode 4 ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult::value'' (Some 1) 6), IntegerStamp 32 (-2147483648) (2147483647)),
  (5, (MulNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (StoreFieldNode 6 ''org.graalvm.compiler.core.test.VeriOptFactorialTest$FactResult::value'' 5 (Some 7) (Some 1) 8), VoidStamp),
  (7, (FrameState [] None None None), IllegalStamp),
  (8, (ReturnNode None None), VoidStamp)
  ]
  )"
fun check_result_2 :: "Value \<Rightarrow> FieldRefHeap \<Rightarrow> bool" where
  "check_result_2 (ObjRef x) h = (h_load_field ''value'' x h = (IntVal32 (120)))" |
  "check_result_2 _ _ = False"
(* code_thms check_result_2 *)
(* export_code check_result_2 *)
(* declare [[code_preproc_trace]] *)
value "object_test unit_factAsAnObject_2 
    ''org.graalvm.compiler.core.test.VeriOptFactorialTest.factAsAnObject(I)Lorg/graalvm/compiler/core/test/VeriOptFactorialTest$FactResult;''
    [(IntVal32 (5))]
    check_result_2"
(* But this gives the following error:
     exception Match raised (line 8104 of "generated code")'
*)



(* Lorg/graalvm/compiler/api/directives/test/OpaqueDirectiveTest;.booleanSnippet*)
definition unit_booleanSnippet_21 :: IRGraph where  "unit_booleanSnippet_21 = irgraph [
  (0, (StartNode (Some 1) 3), VoidStamp),
  (1, (FrameState [] None None None), IllegalStamp),
  (2, (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1)),
  (3, (ReturnNode (Some 2) None), VoidStamp)
  ]"
value "static_test unit_booleanSnippet_21 [] (IntVal32 (1))"

(*
graph \<open>
0: (StartNode (Some 2) 11, VoidStamp)
1: (ParameterNode 0, IntegerStamp 32 (-2147483648) (2147483647))
2: (FrameState [] None None None, IllegalStamp)
3: (ConstantNode (IntVal32 (3)), IntegerStamp 32 (3) (3))
4: (ConstantNode (IntVal32 (4)), IntegerStamp 32 (4) (4))
5: (IntegerLessThanNode 1 4, VoidStamp)
6: (ConstantNode (IntVal32 (0)), IntegerStamp 32 (0) (0))
7: (ConstantNode (IntVal32 (1)), IntegerStamp 32 (1) (1))
8: (ConditionalNode 5 6 7, IntegerStamp 32 (0) (1))
9: (BeginNode 12, VoidStamp)
10: (BeginNode 13, VoidStamp)
11: (IfNode 5 10 9, VoidStamp)
12: (ReturnNode (Some 7) None, VoidStamp)
13: (ReturnNode (Some 7) None, VoidStamp)
\<close>

graph_file \<open>test.graph\<close>
*)


(* Lorg/graalvm/compiler/api/directives/test/BlackholeDirectiveTest;.booleanSnippet*)
definition unit_booleanSnippet_3 :: IRGraph where  "unit_booleanSnippet_3 = irgraph [
  (0, (StartNode (Some 2) 11), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal32 (3))), IntegerStamp 32 (3) (3)),
  (4, (ConstantNode (IntVal32 (4))), IntegerStamp 32 (4) (4)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (ConstantNode (IntVal32 (0))), IntegerStamp 32 (0) (0)),
  (7, (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1)),
  (8, (ConditionalNode 5 6 7), IntegerStamp 32 (0) (1)),
  (9, (BeginNode 12), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 5 10 9), VoidStamp),
  (12, (ReturnNode (Some 7) None), VoidStamp),
  (13, (ReturnNode (Some 7) None), VoidStamp)
  ]"
value "static_test unit_booleanSnippet_3 [(IntVal32 (5))] (IntVal32 (1))"


(* Lorg/graalvm/compiler/core/test/DontReuseArgumentSpaceTest;.callTwice*)
definition unit_callTwice_343 :: Program where
  "unit_callTwice_343 = Map.empty (
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
value "program_test unit_callTwice_343 ''org.graalvm.compiler.core.test.DontReuseArgumentSpaceTest.callTwice(IIIIIIIIII)I'' [(IntVal32 (1)), (IntVal32 (2)), (IntVal32 (3)), (IntVal32 (4)), (IntVal32 (5)), (IntVal32 (6)), (IntVal32 (7)), (IntVal32 (8)), (IntVal32 (9)), (IntVal32 (10))] (IntVal32 (55))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedIntegerTest;.compareInteger*)
definition unit_compareInteger_16194 :: Program where
  "unit_compareInteger_16194 = Map.empty (
  ''org.graalvm.compiler.replacements.test.UnsignedIntegerTest.compareInteger(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (MethodCallTargetNode ''java.lang.Integer.compareUnsigned(II)I'' [1, 2]), VoidStamp),
  (5, (InvokeNode 5 4 None None (Some 6) 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''java.lang.Integer.compareUnsigned(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (IntVal32 (-2147483648))), IntegerStamp 32 (-2147483648) (-2147483648)),
  (5, (AddNode 1 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (AddNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (MethodCallTargetNode ''java.lang.Integer.compare(II)I'' [5, 6]), VoidStamp),
  (8, (InvokeNode 8 7 None None (Some 9) 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ReturnNode (Some 8) None), VoidStamp)
  ],
  ''java.lang.Integer.compare(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal32 (-1))), IntegerStamp 32 (-1) (-1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (ConstantNode (IntVal32 (0))), IntegerStamp 32 (0) (0)),
  (12, (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (0) (1)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (-1) (1)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]
  )"
value "program_test unit_compareInteger_16194 ''org.graalvm.compiler.replacements.test.UnsignedIntegerTest.compareInteger(II)I'' [(IntVal32 (5)), (IntVal32 (7))] (IntVal32 (-1))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedIntegerTest;.compareInteger*)
definition unit_compareInteger_16197 :: Program where
  "unit_compareInteger_16197 = Map.empty (
  ''org.graalvm.compiler.replacements.test.UnsignedIntegerTest.compareInteger(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (MethodCallTargetNode ''java.lang.Integer.compareUnsigned(II)I'' [1, 2]), VoidStamp),
  (5, (InvokeNode 5 4 None None (Some 6) 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''java.lang.Integer.compareUnsigned(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (IntVal32 (-2147483648))), IntegerStamp 32 (-2147483648) (-2147483648)),
  (5, (AddNode 1 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (AddNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (MethodCallTargetNode ''java.lang.Integer.compare(II)I'' [5, 6]), VoidStamp),
  (8, (InvokeNode 8 7 None None (Some 9) 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ReturnNode (Some 8) None), VoidStamp)
  ],
  ''java.lang.Integer.compare(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal32 (-1))), IntegerStamp 32 (-1) (-1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (ConstantNode (IntVal32 (0))), IntegerStamp 32 (0) (0)),
  (12, (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (0) (1)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (-1) (1)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]
  )"
value "program_test unit_compareInteger_16197 ''org.graalvm.compiler.replacements.test.UnsignedIntegerTest.compareInteger(II)I'' [(IntVal32 (-3)), (IntVal32 (-7))] (IntVal32 (1))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedIntegerTest;.compareInteger*)
definition unit_compareInteger_16200 :: Program where
  "unit_compareInteger_16200 = Map.empty (
  ''org.graalvm.compiler.replacements.test.UnsignedIntegerTest.compareInteger(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (MethodCallTargetNode ''java.lang.Integer.compareUnsigned(II)I'' [1, 2]), VoidStamp),
  (5, (InvokeNode 5 4 None None (Some 6) 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''java.lang.Integer.compareUnsigned(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (IntVal32 (-2147483648))), IntegerStamp 32 (-2147483648) (-2147483648)),
  (5, (AddNode 1 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (AddNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (MethodCallTargetNode ''java.lang.Integer.compare(II)I'' [5, 6]), VoidStamp),
  (8, (InvokeNode 8 7 None None (Some 9) 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ReturnNode (Some 8) None), VoidStamp)
  ],
  ''java.lang.Integer.compare(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal32 (-1))), IntegerStamp 32 (-1) (-1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (ConstantNode (IntVal32 (0))), IntegerStamp 32 (0) (0)),
  (12, (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (0) (1)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (-1) (1)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]
  )"
value "program_test unit_compareInteger_16200 ''org.graalvm.compiler.replacements.test.UnsignedIntegerTest.compareInteger(II)I'' [(IntVal32 (-3)), (IntVal32 (7))] (IntVal32 (1))"


(* Lorg/graalvm/compiler/replacements/test/UnsignedIntegerTest;.compareInteger*)
definition unit_compareInteger_16203 :: Program where
  "unit_compareInteger_16203 = Map.empty (
  ''org.graalvm.compiler.replacements.test.UnsignedIntegerTest.compareInteger(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 5), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (MethodCallTargetNode ''java.lang.Integer.compareUnsigned(II)I'' [1, 2]), VoidStamp),
  (5, (InvokeNode 5 4 None None (Some 6) 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (FrameState [] None None None), IllegalStamp),
  (7, (ReturnNode (Some 5) None), VoidStamp)
  ],
  ''java.lang.Integer.compareUnsigned(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (ConstantNode (IntVal32 (-2147483648))), IntegerStamp 32 (-2147483648) (-2147483648)),
  (5, (AddNode 1 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (6, (AddNode 2 4), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (MethodCallTargetNode ''java.lang.Integer.compare(II)I'' [5, 6]), VoidStamp),
  (8, (InvokeNode 8 7 None None (Some 9) 10), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (FrameState [] None None None), IllegalStamp),
  (10, (ReturnNode (Some 8) None), VoidStamp)
  ],
  ''java.lang.Integer.compare(II)I'' \<mapsto> irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 16), VoidStamp),
  (6, (BeginNode 14), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal32 (-1))), IntegerStamp 32 (-1) (-1)),
  (10, (IntegerEqualsNode 1 2), VoidStamp),
  (11, (ConstantNode (IntVal32 (0))), IntegerStamp 32 (0) (0)),
  (12, (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1)),
  (13, (ConditionalNode 10 11 12), IntegerStamp 32 (0) (1)),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode [14, 16] (Some 18) 19), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (ValuePhiNode 17 [8, 13] 15), IntegerStamp 32 (-1) (1)),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (ReturnNode (Some 17) None), VoidStamp)
  ]
  )"
value "program_test unit_compareInteger_16203 ''org.graalvm.compiler.replacements.test.UnsignedIntegerTest.compareInteger(II)I'' [(IntVal32 (42)), (IntVal32 (-5))] (IntVal32 (-1))"


(* Lorg/graalvm/compiler/core/test/ConditionalNodeTest;.conditionalTest0*)
definition unit_conditionalTest0_80 :: IRGraph where  "unit_conditionalTest0_80 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal32 (-1))), IntegerStamp 32 (-1) (-1)),
  (9, (ConstantNode (IntVal32 (0))), IntegerStamp 32 (0) (0)),
  (10, (StoreFieldNode 10 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink1'' 9 (Some 11) None 16), VoidStamp),
  (11, (FrameState [] None None None), IllegalStamp),
  (13, (ConstantNode (IntVal32 (6))), IntegerStamp 32 (6) (6)),
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
value "static_test unit_conditionalTest0_80 [(IntVal32 (0))] (IntVal32 (6))"


(* Lorg/graalvm/compiler/core/test/ConditionalNodeTest;.conditionalTest0*)
definition unit_conditionalTest0_81 :: IRGraph where  "unit_conditionalTest0_81 = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal32 (1))), IntegerStamp 32 (1) (1)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 14), VoidStamp),
  (6, (BeginNode 10), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal32 (-1))), IntegerStamp 32 (-1) (-1)),
  (9, (ConstantNode (IntVal32 (0))), IntegerStamp 32 (0) (0)),
  (10, (StoreFieldNode 10 ''org.graalvm.compiler.core.test.ConditionalNodeTest::sink1'' 9 (Some 11) None 16), VoidStamp),
  (11, (FrameState [] None None None), IllegalStamp),
  (13, (ConstantNode (IntVal32 (6))), IntegerStamp 32 (6) (6)),
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

end