section \<open>Example program evaluation\<close>

theory ExecExamples
  imports
    IRStepObj
begin

(* NB: The starting state is duplicated causing the program to be executed twice
       The reason for this is that the top step of ReturnNode empties
       the state list to signal completion, this means we can't access the state

   Discuss ways to fix this
 *)
inductive exec_graph :: "IRGraph \<Rightarrow> Value list \<Rightarrow> (ID \<times> MapState) \<Rightarrow> ExecLog \<Rightarrow> bool" ("_|_\<leadsto>_|_")
  where
  "\<lbrakk>state = new_map ps;
    (\<lambda>x. g) \<turnstile> ([('''', 0, state), ('''', 0, state)], new_heap) | [] \<longrightarrow>* ((end # xs), heap) | l\<rbrakk>
    \<Longrightarrow> exec_graph g ps (prod.snd end) l"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o * o \<Rightarrow> o \<Rightarrow> bool as execE) "exec_graph" .


definition simple_return :: IRGraph where
  "simple_return = irgraph [
    (2, (ReturnNode (Some 1) None)),
    (1, (ConstantNode 42)),
    (0, (StartNode None 2))
  ]"

(* IntVal 42 *)
values "{m_val m 0 |n m l. simple_return | [] \<leadsto> (n, m) | l}"

values "{l | x l . simple_return | [] \<leadsto> x | l}"

definition double_param :: IRGraph where
  "double_param = irgraph [
    (3, (ReturnNode (Some 2) None)),
    (2, (AddNode 1 1)),
    (1, (ParameterNode 0)),
    (0, (StartNode None 3))
  ]"

(* IntVal 10 *)
values "{m_val m 0 |n m l. double_param | [IntVal 5] \<leadsto> (n, m) | l}"
values "{l | x l . double_param | [IntVal 5] \<leadsto> x | l}"
(* IntVal 50 *)
values "{m_val m 0 |n m l. double_param | [IntVal 25] \<leadsto> (n, m) | l}"
(* IntVal 256 *)
values "{m_val m 0 |n m l. double_param | [IntVal 128] \<leadsto> (n, m) | l}"
(* IntVal 198 *)
values "{m_val m 0 |n m l. double_param | [IntVal 99] \<leadsto> (n, m) | l}"

definition simple_if :: IRGraph where
  "simple_if = irgraph [
    (12, (ReturnNode (Some 11) None)),
    (11, (ValuePhiNode 11 [9,7] 10)),
    (10, (MergeNode [5,6] None 12)),
    (9, (AddNode 7 8)),
    (8, (ParameterNode 2)),
    (7, (ParameterNode 1)),
    (6, (EndNode)),
    (5, (EndNode)),
    (4, (BeginNode 6)),
    (3, (BeginNode 5)),
    (2, (IfNode 1 3 4)),
    (1, (ParameterNode 0)),
    (0, (StartNode None 2))
  ]"

(* IntVal 20 *)
values "{m_val m 0 |n m l. simple_if | [IntVal 0, IntVal 20, IntVal 100] \<leadsto> (n, m) | l}"
values "{l | x l . simple_if | [IntVal 0, IntVal 20, IntVal 100] \<leadsto> x | l}"
(* IntVal 120 *)
values "{m_val m 0 |n m l. simple_if | [IntVal 1, IntVal 20, IntVal 100] \<leadsto> (n, m) | l}"
values "{l | x l . simple_if | [IntVal 1, IntVal 20, IntVal 100] \<leadsto> x | l}"


definition loop :: IRGraph where
  "loop = irgraph [
    (13, (ReturnNode (Some 7) None)),
    (12, (LoopEndNode 11)),
    (11, (BeginNode 12)),
    (10, (IfNode 9 11 13)),
    (9, (IntegerLessThanNode 7 6)),
    (8, (AddNode 7 5)),
    (7, (ValuePhiNode 7 [4,8] 3)),
    (6, (ParameterNode 0)),
    (5, (ConstantNode 1)),
    (4, (ConstantNode 0)),
    (3, (LoopBeginNode [2,12] None None 10)),
    (2, (EndNode)),
    (1, (BeginNode 2)),
    (0, (StartNode None 1))
  ]"

(* IntVal 0 *)
values "{m_val m 0 |n m l. loop | [IntVal 0] \<leadsto> (n, m) | l}"
(* IntVal 1 *)
values "{m_val m 0 |n m l. loop | [IntVal 1] \<leadsto> (n, m) | l}"
(* IntVal 2 *)
values "{m_val m 0 |n m l. loop | [IntVal 2] \<leadsto> (n, m) | l}"
(* IntVal 5 *)
values "{m_val m 0 |n m l. loop | [IntVal 5] \<leadsto> (n, m) | l}"
(* IntVal 10 *)
values "{m_val m 0 |n m l. loop | [IntVal 10] \<leadsto> (n, m) | l}"
values "{l | x l . loop | [IntVal 10] \<leadsto> x | l}"

definition sum :: IRGraph where
  "sum = irgraph [
    (15, (ReturnNode (Some 10) None)),
    (14, (LoopEndNode 13)),
    (13, (BeginNode 14)),
    (12, (IfNode 11 13 15)),
    (11, (IntegerLessThanNode 7 6)),
    (10, (AddNode 8 7)),
    (9, (AddNode 7 5)),
    (8, (ValuePhiNode 8 [4,10] 3)),
    (7, (ValuePhiNode 7 [4,9] 3)),
    (6, (ParameterNode 0)),
    (5, (ConstantNode 1)),
    (4, (ConstantNode 0)),
    (3, (LoopBeginNode [2,14] None None 12)),
    (2, (EndNode)),
    (1, (BeginNode 2)),
    (0, (StartNode None 1))
  ]"

(* IntVal 1 *)
values "{m_val m 0 |n m l. sum | [IntVal 1] \<leadsto> (n, m) | l}"
(* IntVal 3 *)
values "{m_val m 0 |n m l. sum | [IntVal 2] \<leadsto> (n, m) | l}"
(* IntVal 15 *)
values "{m_val m 0 |n m l. sum | [IntVal 5] \<leadsto> (n, m) | l}"
(* IntVal 28 *)
values "{m_val m 0 |n m l. sum | [IntVal 7] \<leadsto> (n, m) | l}"
(* IntVal 210 *)
values "{m_val m 0 |n m l. sum | [IntVal 20] \<leadsto> (n, m) | l}"


inductive exec_prog :: "Program \<Rightarrow> Signature \<Rightarrow> Value list \<Rightarrow> (ID \<times> MapState) \<Rightarrow> bool" ("_|_|_\<leadsto>_")
  where
  "\<lbrakk>state = new_map ps;
    p \<turnstile> ([(main, 0, state), (main, 0, state)], new_heap) | [] \<longrightarrow>* ((end # xs), heap) | l\<rbrakk>
    \<Longrightarrow> exec_prog p main ps (prod.snd end)"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o * o \<Rightarrow> bool as execProgE) "exec_prog" .


(* Automatically generated program *)
definition prog :: "string \<Rightarrow> IRGraph " where
"prog = (\<lambda>x . start_end_graph)
(''Fib.fib(I)I'' := irgraph [
 (0, (StartNode ((Some 2)) (8))),
 (1, (ParameterNode (0))),
 (2, (FrameState ([]) (None) ((Some [1])) (None))),
 (3, (ConstantNode (1))),
 (4, (ConstantNode (2))),
 (5, (IntegerLessThanNode (1) (4))),
 (6, (BeginNode (13))),
 (7, (BeginNode (9))),
 (8, (IfNode (5) (7) (6))),
 (9, (ReturnNode ((Some 1)) (None))),
 (10, (ConstantNode (-1))),
 (11, (AddNode (1) (10))),
 (12, (MethodCallTargetNode (''Fib.fib(I)I'') ([11]))),
 (13, (InvokeNode (13) (12) (None) (None) ((Some 14)) (18))),
 (14, (FrameState ([]) (None) ((Some [1, 13])) (None))),
 (15, (ConstantNode (-2))),
 (16, (AddNode (1) (15))),
 (17, (MethodCallTargetNode (''Fib.fib(I)I'') ([16]))),
 (18, (InvokeNode (18) (17) (None) (None) ((Some 19)) (21))),
 (19, (FrameState ([]) (None) ((Some [13, 18])) (None))),
 (20, (AddNode (13) (18))),
 (21, (ReturnNode ((Some 20)) (None)))
])
"


export_code execProgE prog in SML module_name "IRInterpreter" file_prefix "IRInterpreter"

(* IntVal 1 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 1] \<leadsto> (n, m)}"
(* IntVal 1 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 2] \<leadsto> (n, m)}"
(* IntVal 2 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 3] \<leadsto> (n, m)}"
(* IntVal 3 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 4] \<leadsto> (n, m)}"
(* IntVal 5 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 5] \<leadsto> (n, m)}"
(* IntVal 8 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 6] \<leadsto> (n, m)}"
(* IntVal 13 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 7] \<leadsto> (n, m)}"



definition combs :: "string \<Rightarrow> IRGraph " where
"combs = ((\<lambda>x . start_end_graph)
(''Combinations.combinations(I, I)I'' := irgraph [
 (0, (StartNode ((Some 3)) (5))),
 (1, (ParameterNode (0))),
 (2, (ParameterNode (1))),
 (3, (FrameState ([]) (None) ((Some [1, 2])) (None))),
 (4, (MethodCallTargetNode (''Combinations.fact(I)I'') ([1]))),
 (5, (InvokeNode (5) (4) (None) (None) ((Some 6)) (8))),
 (6, (FrameState ([]) (None) ((Some [1, 2, 5])) (None))),
 (7, (MethodCallTargetNode (''Combinations.fact(I)I'') ([2]))),
 (8, (InvokeNode (8) (7) (None) (None) ((Some 9)) (12))),
 (9, (FrameState ([]) (None) ((Some [1, 2, 5, 8])) (None))),
 (10, (SubNode (1) (2))),
 (11, (MethodCallTargetNode (''Combinations.fact(I)I'') ([10]))),
 (12, (InvokeNode (12) (11) (None) (None) ((Some 13)) (15))),
 (13, (FrameState ([]) (None) ((Some [5, 8, 12])) (None))),
 (14, (MulNode (8) (12))),
 (15, (SignedDivNode (5) (14) (None) (None) (16))),
 (16, (ReturnNode ((Some 15)) (None)))
]))
(''Combinations.fact(I)I'' := irgraph [
 (0, (StartNode ((Some 2)) (5))),
 (1, (ParameterNode (0))),
 (2, (FrameState ([]) (None) ((Some [1])) (None))),
 (3, (ConstantNode (1))),
 (5, (EndNode)),
 (6, (LoopBeginNode ([5]) (None) ((Some 9)) (17))),
 (7, (ValuePhiNode (7) ([1, 20, 9]) (6))),
 (8, (ValuePhiNode (8) ([3, 18, 9]) (6))),
 (9, (FrameState ([]) (None) ((Some [7, 8])) (None))),
 (10, (ConstantNode (2))),
 (11, (IntegerLessThanNode (7) (10))),
 (12, (BeginNode (21))),
 (14, (LoopExitNode (6) ((Some 16)) (22))),
 (15, (ValueProxyNode (8) (14))),
 (16, (FrameState ([]) (None) ((Some [15])) (None))),
 (17, (IfNode (11) (14) (12))),
 (18, (MulNode (7) (8))),
 (19, (ConstantNode (-1))),
 (20, (AddNode (7) (19))),
 (21, (LoopEndNode (6))),
 (22, (ReturnNode ((Some 15)) (None)))
])
"


definition combs_params where "combs_params = new_map [IntVal 10, IntVal 6]"
definition combs_main where "combs_main = ''Combinations.combinations(I, I)I''"

values "{m_val m 0 |n m l. combs | combs_main | [IntVal 10, IntVal 6] \<leadsto> (n, m)}"

values "{l |x h l. combs \<turnstile> ([(combs_main, 0, combs_params), (combs_main, 0, combs_params)], new_heap) | [] \<longrightarrow>* (x, h) | l}"
values "{x |x h l. combs \<turnstile> ([(combs_main, 0, combs_params), (combs_main, 0, combs_params)], new_heap) | [] \<longrightarrow>* (x, h) | l}"
values "{m_values (prod.snd (prod.snd (x!0))) 12 |x h l. combs \<turnstile> ([(combs_main, 0, combs_params), (combs_main, 0, combs_params)], new_heap) | [] \<longrightarrow>* (x, h) | l}"


definition native_combs :: "string \<Rightarrow> IRGraph " where
"native_combs = ((\<lambda>x . empty_graph)
(''Combinations.fact(I)I'' := 
 (add_node 0 (StartNode ((Some 2)) (5))
 (add_node 1 (ParameterNode (0))
 (add_node 2 (FrameState ([]) (None) ((Some [1])) (None))
 (add_node 3 (ConstantNode (1))
 (add_node 5 (EndNode)
 (add_node 6 (LoopBeginNode ([5, 21]) (None) ((Some 9)) (17))
 (add_node 7 (ValuePhiNode (7) ([1, 20, 9]) (6))
 (add_node 8 (ValuePhiNode (8) ([3, 18, 9]) (6))
 (add_node 9 (FrameState ([]) (None) ((Some [7, 8])) (None))
 (add_node 10 (ConstantNode (2))
 (add_node 11 (IntegerLessThanNode (7) (10))
 (add_node 12 (BeginNode (21))
 (add_node 14 (LoopExitNode (6) ((Some 16)) (22))
 (add_node 15 (ValueProxyNode (8) (14))
 (add_node 16 (FrameState ([]) (None) ((Some [15])) (None))
 (add_node 17 (IfNode (11) (14) (12))
 (add_node 18 (MulNode (7) (8))
 (add_node 19 (ConstantNode (-1))
 (add_node 20 (AddNode (7) (19))
 (add_node 21 (LoopEndNode (6))
 (add_node 22 (ReturnNode ((Some 15)) (None))
 empty_graph)))))))))))))))))))))
))
(''Combinations.combinations(II)I'' := 
 (add_node 0 (StartNode ((Some 3)) (8))
 (add_node 1 (ParameterNode (0))
 (add_node 2 (ParameterNode (1))
 (add_node 3 (FrameState ([]) (None) ((Some [1, 2])) (None))
 (add_node 4 (SubstrateMethodCallTargetNode (''Combinations.fact(I)I'') ([1]))
 (add_node 5 (ExceptionObjectNode ((Some 6)) (14))
 (add_node 6 (FrameState ([]) (None) ((Some [1, 2, 5])) (None))
 (add_node 8 (InvokeWithExceptionNode (8) (4) (None) (None) ((Some 9)) (10) (5))
 (add_node 9 (FrameState ([]) (None) ((Some [1, 2, 8])) (None))
 (add_node 10 (KillingBeginNode (18))
 (add_node 11 (SubstrateMethodCallTargetNode (''Combinations.fact(I)I'') ([2]))
 (add_node 12 (ExceptionObjectNode ((Some 13)) (16))
 (add_node 13 (FrameState ([]) (None) ((Some [1, 2, 12])) (None))
 (add_node 14 (EndNode)
 (add_node 15 (MergeNode ([14, 16, 25, 38]) ((Some 41)) (42))
 (add_node 16 (EndNode)
 (add_node 17 (ValuePhiNode (17) ([5, 12, 23, 32, 41]) (15))
 (add_node 18 (InvokeWithExceptionNode (18) (11) (None) (None) ((Some 19)) (20) (12))
 (add_node 19 (FrameState ([]) (None) ((Some [1, 2, 8, 18])) (None))
 (add_node 20 (KillingBeginNode (26))
 (add_node 21 (SubNode (1) (2))
 (add_node 22 (SubstrateMethodCallTargetNode (''Combinations.fact(I)I'') ([21]))
 (add_node 23 (ExceptionObjectNode ((Some 24)) (25))
 (add_node 24 (FrameState ([]) (None) ((Some [23])) (None))
 (add_node 25 (EndNode)
 (add_node 26 (InvokeWithExceptionNode (26) (22) (None) (None) ((Some 27)) (28) (23))
 (add_node 27 (FrameState ([]) (None) ((Some [8, 18, 26])) (None))
 (add_node 28 (KillingBeginNode (35))
 (add_node 29 (MulNode (18) (26))
 (add_node 30 (ConstantNode (0))
 (add_node 31 (IntegerEqualsNode (29) (30))
 (add_node 32 (BytecodeExceptionNode ([]) ((Some 36)) (38))
 (add_node 33 (BeginNode (39))
 (add_node 34 (BeginNode (32))
 (add_node 35 (IfNode (31) (34) (33))
 (add_node 36 (FrameState ([]) (None) (None) (None))
 (add_node 38 (EndNode)
 (add_node 39 (SignedDivNode (8) (29) ((Some 33)) (None) (40))
 (add_node 40 (ReturnNode ((Some 39)) (None))
 (add_node 41 (FrameState ([]) (None) ((Some [17])) (None))
 (add_node 42 (UnwindNode (17))
 empty_graph)))))))))))))))))))))))))))))))))))))))))
)
"

definition native_combs_params where "native_combs_params = new_map [IntVal 10, IntVal 6]"
definition native_combs_main where "native_combs_main = ''Combinations.combinations(II)I''"

values "{m_val m 0 |n m l. native_combs | native_combs_main | [IntVal 10, IntVal 6] \<leadsto> (n, m)}"

values "{m | m . native_combs \<turnstile> ([(native_combs_main, 0, native_combs_params)], new_heap) \<rightarrow>*41* m}"


definition exceptional_prog :: "string \<Rightarrow> IRGraph " where
"exceptional_prog = (((\<lambda>x . empty_graph)
(''Exceptional.main(I)V'' :=
  (add_node 0 (StartNode ((Some 2)) (3))
  (add_node 1 (ParameterNode (0))
  (add_node 2 (SubstrateMethodCallTargetNode (''Exceptional.maybeException(I)V'') ([1]))
  (add_node 3 (InvokeWithExceptionNode (3) (2) (None) (None) ((Some 14)) (4) (5))
  (add_node 4 (ReturnNode (None) (None))
  (add_node 5 (UnwindNode (1))
  empty_graph))))))
))
(''Exceptional.maybeException(I)V'' := 
 (add_node 0 (StartNode ((Some 2)) (7))
 (add_node 1 (ParameterNode (0))
 (add_node 2 (FrameState ([]) (None) ((Some [1])) (None))
 (add_node 3 (ConstantNode (0))
 (add_node 4 (IntegerLessThanNode (1) (3))
 (add_node 5 (BeginNode (21))
 (add_node 6 (BeginNode (8))
 (add_node 7 (IfNode (4) (6) (5))
 (add_node 8 (NewInstanceNode ''IllegalArgumentException'' None 13)
 (add_node 9 (SubstrateMethodCallTargetNode (''java.lang.IllegalArgumentException.<init>()V'') ([8]))
 (add_node 10 (ExceptionObjectNode ((Some 11)) (17))
 (add_node 11 (FrameState ([]) (None) ((Some [10])) (None))
 (add_node 13 (InvokeWithExceptionNode (13) (9) (None) (None) ((Some 14)) (15) (10))
 (add_node 14 (FrameState ([]) (None) ((Some [8])) (None))
 (add_node 15 (KillingBeginNode (19))
 (add_node 17 (EndNode)
 (add_node 18 (MergeNode ([17, 19]) ((Some 22)) (23))
 (add_node 19 (EndNode)
 (add_node 20 (ValuePhiNode (20) ([10, 8, 22]) (18))
 (add_node 21 (ReturnNode (None) (None))
 (add_node 22 (FrameState ([]) (None) ((Some [20])) (None))
 (add_node 23 (UnwindNode (20))
 empty_graph))))))))))))))))))))))
))
(''java.lang.IllegalArgumentException.<init>()V'' := 
 (add_node 0 (StartNode ((Some 2)) (2))
 (add_node 1 (ConstantNode 12)
 (add_node 2 (ReturnNode (Some 1) (None))
 empty_graph)))
)
"

definition exceptional_params where "exceptional_params = new_map [IntVal (10)]"
definition exceptional_main where "exceptional_main = ''Exceptional.main(I)V''"


values "{m_state m |n m. exceptional_prog | exceptional_main | [IntVal (10)] \<leadsto> (n, m)}"
values "{m_state m |n m. exceptional_prog | exceptional_main | [IntVal (-10)] \<leadsto> (n, m)}"
values "{m_state m |n m. exceptional_prog | exceptional_main | [IntVal (0)] \<leadsto> (n, m)}"
values "{m_state m |n m. exceptional_prog | exceptional_main | [IntVal (-1)] \<leadsto> (n, m)}"

values "{m | m . exceptional_prog \<turnstile> ([(exceptional_main, 0, exceptional_params)], new_heap) \<rightarrow>*5* m}"

end