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
    (2, (ReturnNode (Some 1) None), default_stamp),
    (1, (ConstantNode (IntVal 32 42)), default_stamp),
    (0, (StartNode None 2), VoidStamp)
  ]"

(* IntVal 42 *)
values "{m_val m 0 |n m l. simple_return | [] \<leadsto> (n, m) | l}"

values "{l | x l . simple_return | [] \<leadsto> x | l}"

definition double_param :: IRGraph where
  "double_param = irgraph [
    (3, (ReturnNode (Some 2) None), default_stamp),
    (2, (AddNode 1 1), default_stamp),
    (1, (ParameterNode 0), default_stamp),
    (0, (StartNode None 3), VoidStamp)
  ]"

(* IntVal 10 *)
values "{m_val m 0 |n m l. double_param | [IntVal 32 5] \<leadsto> (n, m) | l}"
values "{l | x l . double_param | [IntVal 32 5] \<leadsto> x | l}"
(* IntVal 50 *)
values "{m_val m 0 |n m l. double_param | [IntVal 32 25] \<leadsto> (n, m) | l}"
(* IntVal 256 *)
values "{m_val m 0 |n m l. double_param | [IntVal 32 128] \<leadsto> (n, m) | l}"
(* IntVal 198 *)
values "{m_val m 0 |n m l. double_param | [IntVal 32 99] \<leadsto> (n, m) | l}"

definition simple_if :: IRGraph where
  "simple_if = irgraph [
    (12, (ReturnNode (Some 11) None), default_stamp),
    (11, (ValuePhiNode 11 [9,7] 10), default_stamp),
    (10, (MergeNode [5,6] None 12), default_stamp),
    (9, (AddNode 7 8), default_stamp),
    (8, (ParameterNode 2), default_stamp),
    (7, (ParameterNode 1), default_stamp),
    (6, (EndNode), VoidStamp),
    (5, (EndNode), VoidStamp),
    (4, (BeginNode 6), VoidStamp),
    (3, (BeginNode 5), VoidStamp),
    (2, (IfNode 1 3 4), VoidStamp),
    (1, (ParameterNode 0), default_stamp),
    (0, (StartNode None 2), VoidStamp)
  ]"

(* IntVal 20 *)
values "{m_val m 0 |n m l. simple_if | [IntVal 32 0, IntVal 32 20, IntVal 32 100] \<leadsto> (n, m) | l}"
values "{l | x l . simple_if | [IntVal 32 0, IntVal 32 20, IntVal 32 100] \<leadsto> x | l}"
(* IntVal 120 *)
values "{m_val m 0 |n m l. simple_if | [IntVal 32 1, IntVal 32 20, IntVal 32 100] \<leadsto> (n, m) | l}"
values "{l | x l . simple_if | [IntVal 32 1, IntVal 32 20, IntVal 32 100] \<leadsto> x | l}"


definition loop :: IRGraph where
  "loop = irgraph [
    (13, (ReturnNode (Some 7) None), default_stamp),
    (12, (LoopEndNode 11), VoidStamp),
    (11, (BeginNode 12), VoidStamp),
    (10, (IfNode 9 11 13), VoidStamp),
    (9, (IntegerLessThanNode 7 6), default_stamp),
    (8, (AddNode 7 5), default_stamp),
    (7, (ValuePhiNode 7 [4,8] 3), default_stamp),
    (6, (ParameterNode 0), default_stamp),
    (5, (ConstantNode (IntVal 32 1)), default_stamp),
    (4, (ConstantNode (IntVal 32 0)), default_stamp),
    (3, (LoopBeginNode [2,12] None None 10), VoidStamp),
    (2, (EndNode), VoidStamp),
    (1, (BeginNode 2), VoidStamp),
    (0, (StartNode None 1), VoidStamp)
  ]"

(* IntVal 0 *)
values "{m_val m 0 |n m l. loop | [IntVal 32 0] \<leadsto> (n, m) | l}"
(* IntVal 1 *)
values "{m_val m 0 |n m l. loop | [IntVal 32 1] \<leadsto> (n, m) | l}"
(* IntVal 2 *)
values "{m_val m 0 |n m l. loop | [IntVal 32 2] \<leadsto> (n, m) | l}"
(* IntVal 5 *)
values "{m_val m 0 |n m l. loop | [IntVal 32 5] \<leadsto> (n, m) | l}"
(* IntVal 10 *)
values "{m_val m 0 |n m l. loop | [IntVal 32 10] \<leadsto> (n, m) | l}"
values "{l | x l . loop | [IntVal 32 10] \<leadsto> x | l}"

definition sum :: IRGraph where
  "sum = irgraph [
    (15, (ReturnNode (Some 10) None), default_stamp),
    (14, (LoopEndNode 13), VoidStamp),
    (13, (BeginNode 14), VoidStamp),
    (12, (IfNode 11 13 15), VoidStamp),
    (11, (IntegerLessThanNode 7 6), default_stamp),
    (10, (AddNode 8 7), default_stamp),
    (9, (AddNode 7 5), default_stamp),
    (8, (ValuePhiNode 8 [4,10] 3), default_stamp),
    (7, (ValuePhiNode 7 [4,9] 3), default_stamp),
    (6, (ParameterNode 0), default_stamp),
    (5, (ConstantNode (IntVal 32 1)), default_stamp),
    (4, (ConstantNode (IntVal 32 0)), default_stamp),
    (3, (LoopBeginNode [2,14] None None 12), VoidStamp),
    (2, (EndNode), VoidStamp),
    (1, (BeginNode 2), VoidStamp),
    (0, (StartNode None 1), VoidStamp)
  ]"

(* IntVal 1 *)
values "{m_val m 0 |n m l. sum | [IntVal 32 1] \<leadsto> (n, m) | l}"
(* IntVal 3 *)
values "{m_val m 0 |n m l. sum | [IntVal 32 2] \<leadsto> (n, m) | l}"
(* IntVal 15 *)
values "{m_val m 0 |n m l. sum | [IntVal 32 5] \<leadsto> (n, m) | l}"
(* IntVal 28 *)
values "{m_val m 0 |n m l. sum | [IntVal 32 7] \<leadsto> (n, m) | l}"
(* IntVal 210 *)
values "{m_val m 0 |n m l. sum | [IntVal 32 20] \<leadsto> (n, m) | l}"


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
 (0, (StartNode ((Some 2)) (8)), VoidStamp),
 (1, (ParameterNode (0)), IntegerStamp 32 (-2147483648) (2147483647)),
 (2, (FrameState ([]) (None) ((Some [1])) (None)), IllegalStamp),
 (3, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
 (4, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
 (5, (IntegerLessThanNode (1) (4)), VoidStamp),
 (6, (BeginNode (13)), VoidStamp),
 (7, (BeginNode (9)), VoidStamp),
 (8, (IfNode (5) (7) (6)), VoidStamp),
 (9, (ReturnNode ((Some 1)) (None)), VoidStamp),
 (10, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
 (11, (AddNode (1) (10)), IntegerStamp 32 (-2147483648) (2147483647)),
 (12, (MethodCallTargetNode (''Fib.fib(I)I'') ([11])), VoidStamp),
 (13, (InvokeNode (13) (12) (None) (None) ((Some 14)) (18)), IntegerStamp 32 (-2147483648) (2147483647)),
 (14, (FrameState ([]) (None) ((Some [1, 13])) (None)), IllegalStamp),
 (15, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
 (16, (AddNode (1) (15)), IntegerStamp 32 (-2147483648) (2147483647)),
 (17, (MethodCallTargetNode (''Fib.fib(I)I'') ([16])), VoidStamp),
 (18, (InvokeNode (18) (17) (None) (None) ((Some 19)) (21)), IntegerStamp 32 (-2147483648) (2147483647)),
 (19, (FrameState ([]) (None) ((Some [13, 18])) (None)), IllegalStamp),
 (20, (AddNode (13) (18)), IntegerStamp 32 (-2147483648) (2147483647)),
 (21, (ReturnNode ((Some 20)) (None)), VoidStamp)
])
"


export_code execProgE prog in SML module_name "IRInterpreter" file_prefix "IRInterpreter"

(* IntVal 1 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 32 1] \<leadsto> (n, m)}"
(* IntVal 1 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 32 2] \<leadsto> (n, m)}"
(* IntVal 2 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 32 3] \<leadsto> (n, m)}"
(* IntVal 3 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 32 4] \<leadsto> (n, m)}"
(* IntVal 5 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 32 5] \<leadsto> (n, m)}"
(* IntVal 8 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 32 6] \<leadsto> (n, m)}"
(* IntVal 13 *)
values "{m_val m 0 |n m l. prog | ''Fib.fib(I)I'' | [IntVal 32 7] \<leadsto> (n, m)}"



definition combs :: "string \<Rightarrow> IRGraph " where
"combs = ((\<lambda>x . start_end_graph)
(''Combinations.combinations(I, I)I'' := irgraph [
 (0, (StartNode ((Some 3)) (5)), VoidStamp),
 (1, (ParameterNode (0)), IntegerStamp 32 (-2147483648) (2147483647)),
 (2, (ParameterNode (1)), IntegerStamp 32 (-2147483648) (2147483647)),
 (3, (FrameState ([]) (None) ((Some [1, 2])) (None)), IllegalStamp),
 (4, (MethodCallTargetNode (''Combinations.fact(I)I'') ([1])), VoidStamp),
 (5, (InvokeNode (5) (4) (None) (None) ((Some 6)) (8)), IntegerStamp 32 (-2147483648) (2147483647)),
 (6, (FrameState ([]) (None) ((Some [1, 2, 5])) (None)), IllegalStamp),
 (7, (MethodCallTargetNode (''Combinations.fact(I)I'') ([2])), VoidStamp),
 (8, (InvokeNode (8) (7) (None) (None) ((Some 9)) (12)), IntegerStamp 32 (-2147483648) (2147483647)),
 (9, (FrameState ([]) (None) ((Some [1, 2, 5, 8])) (None)), IllegalStamp),
 (10, (SubNode (1) (2)), IntegerStamp 32 (-2147483648) (2147483647)),
 (11, (MethodCallTargetNode (''Combinations.fact(I)I'') ([10])), VoidStamp),
 (12, (InvokeNode (12) (11) (None) (None) ((Some 13)) (15)), IntegerStamp 32 (-2147483648) (2147483647)),
 (13, (FrameState ([]) (None) ((Some [5, 8, 12])) (None)), IllegalStamp),
 (14, (MulNode (8) (12)), IntegerStamp 32 (-2147483648) (2147483647)),
 (15, (SignedDivNode (5) (14) (None) (None) (16)), IntegerStamp 32 (-2147483648) (2147483647)),
 (16, (ReturnNode ((Some 15)) (None)), VoidStamp)
]))
(''Combinations.fact(I)I'' := irgraph [
 (0, (StartNode ((Some 2)) (5)), VoidStamp),
 (1, (ParameterNode (0)), IntegerStamp 32 (-2147483648) (2147483647)),
 (2, (FrameState ([]) (None) ((Some [1])) (None)), IllegalStamp),
 (3, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
 (5, (EndNode), VoidStamp),
 (6, (LoopBeginNode ([5, 21]) (None) ((Some 9)) (17)), VoidStamp),
 (7, (ValuePhiNode (7) ([1, 20, 9]) (6)), IntegerStamp 32 (-2147483648) (2147483647)),
 (8, (ValuePhiNode (8) ([3, 18, 9]) (6)), IntegerStamp 32 (-2147483648) (2147483647)),
 (9, (FrameState ([]) (None) ((Some [7, 8])) (None)), IllegalStamp),
 (10, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
 (11, (IntegerLessThanNode (7) (10)), VoidStamp),
 (12, (BeginNode (21)), VoidStamp),
 (14, (LoopExitNode (6) ((Some 16)) (22)), VoidStamp),
 (15, (ValueProxyNode (8) (14)), IntegerStamp 32 (-2147483648) (2147483647)),
 (16, (FrameState ([]) (None) ((Some [15])) (None)), IllegalStamp),
 (17, (IfNode (11) (14) (12)), VoidStamp),
 (18, (MulNode (7) (8)), IntegerStamp 32 (-2147483648) (2147483647)),
 (19, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
 (20, (AddNode (7) (19)), IntegerStamp 32 (-2147483648) (2147483647)),
 (21, (LoopEndNode (6)), VoidStamp),
 (22, (ReturnNode ((Some 15)) (None)), VoidStamp)
])
"


definition combs_params where "combs_params = new_map [IntVal 32 10, IntVal 32 6]"
definition combs_main where "combs_main = ''Combinations.combinations(I, I)I''"

values "{m_val m 0 |n m l. combs | combs_main | [IntVal 32 10, IntVal 32 6] \<leadsto> (n, m)}"

values "{l |x h l. combs \<turnstile> ([(combs_main, 0, combs_params), (combs_main, 0, combs_params)], new_heap) | [] \<longrightarrow>* (x, h) | l}"
values "{x |x h l. combs \<turnstile> ([(combs_main, 0, combs_params), (combs_main, 0, combs_params)], new_heap) | [] \<longrightarrow>* (x, h) | l}"
values "{m_values (prod.snd (prod.snd (x!0))) 12 |x h l. combs \<turnstile> ([(combs_main, 0, combs_params), (combs_main, 0, combs_params)], new_heap) | [] \<longrightarrow>* (x, h) | l}"


definition native_combs :: "string \<Rightarrow> IRGraph " where
"native_combs = ((\<lambda>x . start_end_graph)
(''Combinations.combinations(II)I'' := irgraph [
 (0, (StartNode ((Some 3)) (8)), VoidStamp),
 (1, (ParameterNode (0)), IntegerStamp 32 (-2147483648) (2147483647)),
 (2, (ParameterNode (1)), IntegerStamp 32 (-2147483648) (2147483647)),
 (3, (FrameState ([]) (None) ((Some [1, 2])) (None)), IllegalStamp),
 (4, (MethodCallTargetNode (''Combinations.fact(I)I'') ([1])), VoidStamp),
 (5, (ExceptionObjectNode ((Some 6)) (14)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (6, (FrameState ([]) (None) ((Some [1, 2, 5])) (None)), IllegalStamp),
 (8, (InvokeWithExceptionNode (8) (4) (None) (None) ((Some 9)) (10) (5)), IntegerStamp 32 (-2147483648) (2147483647)),
 (9, (FrameState ([]) (None) ((Some [1, 2, 8])) (None)), IllegalStamp),
 (10, (KillingBeginNode (18)), VoidStamp),
 (11, (MethodCallTargetNode (''Combinations.fact(I)I'') ([2])), VoidStamp),
 (12, (ExceptionObjectNode ((Some 13)) (16)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (13, (FrameState ([]) (None) ((Some [1, 2, 12])) (None)), IllegalStamp),
 (14, (EndNode), VoidStamp),
 (15, (MergeNode ([14, 16, 25, 38]) ((Some 41)) (42)), VoidStamp),
 (16, (EndNode), VoidStamp),
 (17, (ValuePhiNode (17) ([5, 12, 23, 32, 41]) (15)), ObjectStamp '''' False False False),
 (18, (InvokeWithExceptionNode (18) (11) (None) (None) ((Some 19)) (20) (12)), IntegerStamp 32 (-2147483648) (2147483647)),
 (19, (FrameState ([]) (None) ((Some [1, 2, 8, 18])) (None)), IllegalStamp),
 (20, (KillingBeginNode (26)), VoidStamp),
 (21, (SubNode (1) (2)), IntegerStamp 32 (-2147483648) (2147483647)),
 (22, (MethodCallTargetNode (''Combinations.fact(I)I'') ([21])), VoidStamp),
 (23, (ExceptionObjectNode ((Some 24)) (25)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (24, (FrameState ([]) (None) ((Some [23])) (None)), IllegalStamp),
 (25, (EndNode), VoidStamp),
 (26, (InvokeWithExceptionNode (26) (22) (None) (None) ((Some 27)) (28) (23)), IntegerStamp 32 (-2147483648) (2147483647)),
 (27, (FrameState ([]) (None) ((Some [8, 18, 26])) (None)), IllegalStamp),
 (28, (KillingBeginNode (35)), VoidStamp),
 (29, (MulNode (18) (26)), IntegerStamp 32 (-2147483648) (2147483647)),
 (30, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
 (31, (IntegerEqualsNode (29) (30)), VoidStamp),
 (32, (BytecodeExceptionNode ([]) ((Some 36)) (38)), ObjectStamp ''Ljava/lang/ArithmeticException;'' True True False),
 (33, (BeginNode (39)), VoidStamp),
 (34, (BeginNode (32)), VoidStamp),
 (35, (IfNode (31) (34) (33)), VoidStamp),
 (36, (FrameState ([]) (None) (None) (None)), IllegalStamp),
 (38, (EndNode), VoidStamp),
 (39, (SignedDivNode (8) (29) ((Some 33)) (None) (40)), IntegerStamp 32 (-2147483648) (2147483647)),
 (40, (ReturnNode ((Some 39)) (None)), VoidStamp),
 (41, (FrameState ([]) (None) ((Some [17])) (None)), IllegalStamp),
 (42, (UnwindNode (17)), VoidStamp)
]))
(''Combinations.fact(I)I'' := irgraph [
 (0, (StartNode ((Some 2)) (5)), VoidStamp),
 (1, (ParameterNode (0)), IntegerStamp 32 (-2147483648) (2147483647)),
 (2, (FrameState ([]) (None) ((Some [1])) (None)), IllegalStamp),
 (3, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
 (5, (EndNode), VoidStamp),
 (6, (LoopBeginNode ([5,21]) (None) ((Some 9)) (17)), VoidStamp),
 (7, (ValuePhiNode (7) ([1, 20, 9]) (6)), IntegerStamp 32 (-2147483648) (2147483647)),
 (8, (ValuePhiNode (8) ([3, 18, 9]) (6)), IntegerStamp 32 (-2147483648) (2147483647)),
 (9, (FrameState ([]) (None) ((Some [7, 8])) (None)), IllegalStamp),
 (10, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
 (11, (IntegerLessThanNode (7) (10)), VoidStamp),
 (12, (BeginNode (21)), VoidStamp),
 (14, (LoopExitNode (6) ((Some 16)) (22)), VoidStamp),
 (15, (ValueProxyNode (8) (14)), IntegerStamp 32 (-2147483648) (2147483647)),
 (16, (FrameState ([]) (None) ((Some [15])) (None)), IllegalStamp),
 (17, (IfNode (11) (14) (12)), VoidStamp),
 (18, (MulNode (7) (8)), IntegerStamp 32 (-2147483648) (2147483647)),
 (19, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
 (20, (AddNode (7) (19)), IntegerStamp 32 (-2147483648) (2147483647)),
 (21, (LoopEndNode (6)), VoidStamp),
 (22, (ReturnNode ((Some 15)) (None)), VoidStamp)
])
"

definition native_combs_params where "native_combs_params = new_map [IntVal 32 10, IntVal 32 6]"
definition native_combs_main where "native_combs_main = ''Combinations.combinations(II)I''"

values "{m_val m 0 |n m l. native_combs | native_combs_main | [IntVal 32 10, IntVal 32 6] \<leadsto> (n, m)}"

values "{m | m . native_combs \<turnstile> ([(native_combs_main, 0, native_combs_params)], new_heap) \<rightarrow>*7* m}"


definition simple_obj :: "string \<Rightarrow> IRGraph " where
"simple_obj = (((\<lambda>x . start_end_graph)
(''SimpleObject.objExample()I'' := irgraph [
 (0, (StartNode ((Some 1)) (2)), VoidStamp),
 (1, (FrameState ([]) (None) (None) (None)), IllegalStamp),
 (2, (NewInstanceNode (''SimpleObject'') (None) (7)), ObjectStamp ''LSimpleObject;'' True True False),
 (3, (MethodCallTargetNode (''SimpleObject.<init>()V'') ([2])), VoidStamp),
 (4, (ExceptionObjectNode ((Some 5)) (13)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (5, (FrameState ([]) (None) ((Some [4])) (None)), IllegalStamp),
 (7, (InvokeWithExceptionNode (7) (3) (None) (None) ((Some 8)) (9) (4)), VoidStamp),
 (8, (FrameState ([]) (None) ((Some [2])) (None)), IllegalStamp),
 (9, (KillingBeginNode (17)), VoidStamp),
 (10, (MethodCallTargetNode (''SimpleObject.assignFields()V'') ([2])), VoidStamp),
 (11, (ExceptionObjectNode ((Some 12)) (15)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (12, (FrameState ([]) (None) ((Some [2, 11])) (None)), IllegalStamp),
 (13, (EndNode), VoidStamp),
 (14, (MergeNode ([13, 15, 28]) ((Some 32)) (33)), VoidStamp),
 (15, (EndNode), VoidStamp),
 (16, (ValuePhiNode (16) ([4, 11, 22, 32]) (14)), ObjectStamp '''' False False False),
 (17, (InvokeWithExceptionNode (17) (10) (None) (None) ((Some 18)) (19) (11)), VoidStamp),
 (18, (FrameState ([]) (None) ((Some [2])) (None)), IllegalStamp),
 (19, (KillingBeginNode (20)), VoidStamp),
 (20, (LoadFieldNode (''SimpleObject.objField'') ((Some 2)) (25)), ObjectStamp ''LSimpleObject;'' True False False),
 (21, (IsNullNode (20)), VoidStamp),
 (22, (BytecodeExceptionNode ([]) ((Some 26)) (28)), ObjectStamp ''Ljava/lang/NullPointerException;'' True True False),
 (23, (BeginNode (30)), VoidStamp),
 (24, (BeginNode (22)), VoidStamp),
 (25, (IfNode (21) (24) (23)), VoidStamp),
 (26, (FrameState ([]) (None) ((Some [2])) (None)), IllegalStamp),
 (28, (EndNode), VoidStamp),
 (29, (PiNode (20) ((Some 23))), ObjectStamp ''LSimpleObject;'' True True False),
 (30, (LoadFieldNode (''SimpleObject.intField'') ((Some 29)) (31)), IntegerStamp 32 (-2147483648) (2147483647)),
 (31, (ReturnNode ((Some 30)) (None)), VoidStamp),
 (32, (FrameState ([]) (None) ((Some [16])) (None)), IllegalStamp),
 (33, (UnwindNode (16)), VoidStamp)
]))
(''SimpleObject.assignFields()V'' := irgraph [
 (0, (StartNode ((Some 2)) (3)), VoidStamp),
 (1, (ParameterNode (0)), ObjectStamp ''LSimpleObject;'' True True False),
 (2, (FrameState ([]) (None) ((Some [1])) (None)), IllegalStamp),
 (3, (NewInstanceNode (''SimpleObject'') (None) (8)), ObjectStamp ''LSimpleObject;'' True True False),
 (4, (MethodCallTargetNode (''SimpleObject.<init>()V'') ([3])), VoidStamp),
 (5, (ExceptionObjectNode ((Some 6)) (22)), ObjectStamp ''Ljava/lang/Throwable;'' False True False),
 (6, (FrameState ([]) (None) ((Some [1, 5])) (None)), IllegalStamp),
 (8, (InvokeWithExceptionNode (8) (4) (None) (None) ((Some 9)) (10) (5)), VoidStamp),
 (9, (FrameState ([]) (None) ((Some [1, 1, 3])) (None)), IllegalStamp),
 (10, (KillingBeginNode (11)), VoidStamp),
 (11, (StoreFieldNode (''SimpleObject.objField'') (3) ((Some 12)) ((Some 1)) (13)), VoidStamp),
 (12, (FrameState ([]) (None) ((Some [1])) (None)), IllegalStamp),
 (13, (LoadFieldNode (''SimpleObject.objField'') ((Some 1)) (19)), ObjectStamp ''LSimpleObject;'' True False False),
 (14, (ConstantNode (IntVal 32 (160))), IntegerStamp 32 (160) (160)),
 (15, (IsNullNode (13)), VoidStamp),
 (16, (BytecodeExceptionNode ([]) ((Some 20)) (24)), ObjectStamp ''Ljava/lang/NullPointerException;'' True True False),
 (17, (BeginNode (27)), VoidStamp),
 (18, (BeginNode (16)), VoidStamp),
 (19, (IfNode (15) (18) (17)), VoidStamp),
 (20, (FrameState ([]) (None) ((Some [1])) (None)), IllegalStamp),
 (22, (EndNode), VoidStamp),
 (23, (MergeNode ([22, 24]) ((Some 30)) (31)), VoidStamp),
 (24, (EndNode), VoidStamp),
 (25, (ValuePhiNode (25) ([5, 16, 30]) (23)), ObjectStamp '''' False False False),
 (26, (PiNode (13) ((Some 17))), ObjectStamp ''LSimpleObject;'' True True False),
 (27, (StoreFieldNode (''SimpleObject.intField'') (14) ((Some 28)) ((Some 26)) (29)), VoidStamp),
 (28, (FrameState ([]) (None) ((Some [1])) (None)), IllegalStamp),
 (29, (ReturnNode (None) (None)), VoidStamp),
 (30, (FrameState ([]) (None) ((Some [25])) (None)), IllegalStamp),
 (31, (UnwindNode (25)), VoidStamp)
]))
(''SimpleObject.<init>()V'' := irgraph [
 (0, (StartNode ((Some 2)) (4)), VoidStamp),
 (1, (ParameterNode (0)), ObjectStamp ''LSimpleObject;'' True True False),
 (2, (FrameState ([]) (None) ((Some [1])) (None)), IllegalStamp),
 (3, (ConstantNode (IntVal 32 (42))), IntegerStamp 32 (42) (42)),
 (4, (StoreFieldNode (''SimpleObject.intField'') (3) ((Some 5)) ((Some 1)) (7)), VoidStamp),
 (5, (FrameState ([]) (None) ((Some [1])) (None)), IllegalStamp),
 (6, (ConstantNode (ObjRef None)), ObjectStamp '''' False False True),
 (7, (StoreFieldNode (''SimpleObject.objField'') (6) ((Some 8)) ((Some 1)) (9)), VoidStamp),
 (8, (FrameState ([]) (None) ((Some [1])) (None)), IllegalStamp),
 (9, (ReturnNode (None) (None)), VoidStamp)
])
"

definition simple_obj_params where "simple_obj_params = new_map []"
definition simple_obj_main where "simple_obj_main = ''Combinations.combinations(II)I''"

values "{m_val m 0 |n m l. native_combs | native_combs_main | [IntVal 32 10, IntVal 32 6] \<leadsto> (n, m)}"

values "{m | m . native_combs \<turnstile> ([(native_combs_main, 0, native_combs_params)], new_heap) \<rightarrow>*7* m}"


definition exceptional_prog :: "string \<Rightarrow> IRGraph " where
"exceptional_prog = (((\<lambda>x . empty_graph)
(''Exceptional.main(I)V'' :=
  (add_node 0 (StartNode ((Some 2)) (3))
  (add_node 1 (ParameterNode (0))
  (add_node 2 (MethodCallTargetNode (''Exceptional.maybeException(I)V'') ([1]))
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
 (add_node 9 (MethodCallTargetNode (''java.lang.IllegalArgumentException.<init>()V'') ([8]))
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