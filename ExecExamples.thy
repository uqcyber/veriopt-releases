section \<open>Example program evaluation\<close>

theory ExecExamples
  imports
    IRStep
begin

(* NB: The starting state is duplicated causing the program to be executed twice
       The reason for this is that the top step of ReturnNode empties
       the state list to signal completion, this means we can't access the state

   Discuss ways to fix this
 *)
inductive exec_graph :: "IRGraph \<Rightarrow> Value list \<Rightarrow> (ID \<times> MapState) \<Rightarrow> ExecLog \<Rightarrow> bool" ("_|_\<leadsto>_|_")
  where
  "\<lbrakk>state = new_map ps;
    g \<turnstile> [(0, state), (0, state)] | [] \<longrightarrow>* (end # xs) | l\<rbrakk>
    \<Longrightarrow> exec_graph g ps end l"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o * o \<Rightarrow> o \<Rightarrow> bool as execE) "exec_graph" .


definition simple_return :: IRGraph where
  "simple_return =
    (add_node 2 (ReturnNode (Some 1) None)
    (add_node 1 (ConstantNode 42)
    (add_node 0 (StartNode None 2)
    empty_graph)))"

(* IntVal 42 *)
values "{m_val m 0 |n m l. simple_return | [] \<leadsto> (n, m) | l}"

values "{l | x l . simple_return | [] \<leadsto> x | l}"

definition double_param :: IRGraph where
  "double_param =
    (add_node 3 (ReturnNode (Some 2) None)
    (add_node 2 (AddNode 1 1)
    (add_node 1 (ParameterNode 0)
    (add_node 0 (StartNode None 3)
    empty_graph))))"

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
  "simple_if =
    (add_node 12 (ReturnNode (Some 11) None)
    (add_node 11 (ValuePhiNode [9,7] 10)
    (add_node 10 (MergeNode [5,6] None 12)
    (add_node 9 (AddNode 7 8)
    (add_node 8 (ParameterNode 2)
    (add_node 7 (ParameterNode 1)
    (add_node 6 (EndNode)
    (add_node 5 (EndNode)
    (add_node 4 (BeginNode 6)
    (add_node 3 (BeginNode 5)
    (add_node 2 (IfNode 1 3 4) 
    (add_node 1 (ParameterNode 0)
    (add_node 0 (StartNode None 2)
    empty_graph)))))))))))))"

(* IntVal 20 *)
values "{m_val m 0 |n m l. simple_if | [IntVal 0, IntVal 20, IntVal 100] \<leadsto> (n, m) | l}"
values "{l | x l . simple_if | [IntVal 0, IntVal 20, IntVal 100] \<leadsto> x | l}"
(* IntVal 120 *)
values "{m_val m 0 |n m l. simple_if | [IntVal 1, IntVal 20, IntVal 100] \<leadsto> (n, m) | l}"
values "{l | x l . simple_if | [IntVal 1, IntVal 20, IntVal 100] \<leadsto> x | l}"

definition simple_call :: IRGraph where
  "simple_call =
    (add_node 7 (ReturnNode (Some 6) None)
    (add_node 6 (AddNode 1 5)
    (add_node 5 (CallNode 2 [] [7])
    (add_node 4 (ReturnNode (Some 3) None)
    (add_node 3 (ConstantNode 12)
    (add_node 2 (StartNode None 4)
    (add_node 1 (CallNode 2 [] [5])
    (add_node 0 (StartNode None 1)
    empty_graph))))))))"

(* IntVal 24 *)
values "{m_val m 0 |n m l. simple_call | [] \<leadsto> (n, m) | l}"

definition loop :: IRGraph where
  "loop =
    (add_node 13 (ReturnNode (Some 7) None)
    (add_node 12 (LoopEndNode 11)
    (add_node 11 (BeginNode 12)
    (add_node 10 (IfNode 9 11 13)
    (add_node 9 (IntegerLessThanNode 7 6)
    (add_node 8 (AddNode 7 5)
    (add_node 7 (ValuePhiNode [4,8] 3)
    (add_node 6 (ParameterNode 0)
    (add_node 5 (ConstantNode 1)
    (add_node 4 (ConstantNode 0)
    (add_node 3 (LoopBeginNode [2,12] None None 10)
    (add_node 2 (EndNode)
    (add_node 1 (BeginNode 2)
    (add_node 0 (StartNode None 1)
    empty_graph))))))))))))))"

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
  "sum =
    (add_node 15 (ReturnNode (Some 10) None)
    (add_node 14 (LoopEndNode 13)
    (add_node 13 (BeginNode 14)
    (add_node 12 (IfNode 11 13 15)
    (add_node 11 (IntegerLessThanNode 7 6)
    (add_node 10 (AddNode 8 7)
    (add_node 9 (AddNode 7 5)
    (add_node 8 (ValuePhiNode [4,10] 3)
    (add_node 7 (ValuePhiNode [4,9] 3)
    (add_node 6 (ParameterNode 0)
    (add_node 5 (ConstantNode 1)
    (add_node 4 (ConstantNode 0)
    (add_node 3 (LoopBeginNode [2,14] None None 12)
    (add_node 2 (EndNode)
    (add_node 1 (BeginNode 2)
    (add_node 0 (StartNode None 1)
    empty_graph))))))))))))))))"

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


(* TODO: fix seafoam generation *)
(* Examples generated from Java code *)

(*
definition real_fact :: IRGraph where
"real_fact = 
 (add_node 0 (StartNode (Some 2) 5)
 (add_node 1 (ParameterNode 0)
 (add_node 2 (FrameState None [1])
 (add_node 3 (ConstantNode (1))
 (add_node 5 (EndNode)
 (add_node 6 (LoopBeginNode None None [5, 21] 17)
 (add_node 7 (ValuePhiNode 6 [1, 20])
 (add_node 8 (ValuePhiNode 6 [3, 18])
 (add_node 9 (FrameState None [7, 8])
 (add_node 10 (ConstantNode (2))
 (add_node 11 (IntegerLessThanNode 7 10)
 (add_node 12 (BeginNode 21)
 (add_node 14 (LoopExitNode 16 None 22)
 (add_node 15 (ValueProxyNode 14 8)
 (add_node 16 (FrameState None [15])
 (add_node 17 (IfNode 11 14 12)
 (add_node 18 (MulNode 7 8)
 (add_node 19 (ConstantNode (-1))
 (add_node 20 (AddNode 7 19)
 (add_node 21 (LoopEndNode 12)
 (add_node 22 (ReturnNode (Some 15) None)
 empty_graph)))))))))))))))))))))"
lemma "wff_graph real_fact"
  unfolding real_fact_def by simp

(* IntVal 1 *)
values "{m_val m 0 |n m. (real_fact \<diamondop> [IntVal 1]) (n, m)}"
(* IntVal 2 *)
values "{m_val m 0 |n m. (real_fact \<diamondop> [IntVal 2]) (n, m)}"
(* IntVal 6 *)
values "{m_val m 0 |n m. (real_fact \<diamondop> [IntVal 3]) (n, m)}"
(* IntVal 24 *)
values "{m_val m 0 |n m. (real_fact \<diamondop> [IntVal 4]) (n, m)}"
(* IntVal 120 *)
values "{m_val m 0 |n m. (real_fact \<diamondop> [IntVal 5]) (n, m)}"
(* IntVal 720 *)
values "{m_val m 0 |n m. (real_fact \<diamondop> [IntVal 6]) (n, m)}"
(* IntVal 5040 *)
values "{m_val m 0 |n m. (real_fact \<diamondop> [IntVal 7]) (n, m)}"

definition real_fib :: IRGraph where
"real_fib = 
 (add_node 0 (StartNode (Some 2) 8)
 (add_node 1 (ParameterNode 0)
 (add_node 2 (FrameState None [1])
 (add_node 3 (ConstantNode 1)
 (add_node 4 (ConstantNode 2)
 (add_node 5 (IntegerLessThanNode 1 4)
 (add_node 6 (BeginNode 13)
 (add_node 7 (BeginNode 9)
 (add_node 8 (IfNode 5 7 6)
 (add_node 9 (ReturnNode (Some 1) None)
 (add_node 10 (ConstantNode (-1))
 (add_node 11 (AddNode 1 10)
 (add_node 13 (CallNode 0 [11] [18])
 (add_node 14 (FrameState None [1, 13])
 (add_node 15 (ConstantNode (-2))
 (add_node 16 (AddNode 1 15)
 (add_node 18 (CallNode 0 [16] [21])
 (add_node 19 (FrameState None [13, 18])
 (add_node 20 (AddNode 13 18)
 (add_node 21 (ReturnNode (Some 20) None)
 empty_graph))))))))))))))))))))"

(* IntVal 1 *)
values "{m_val m 0 |n m. (real_fib \<diamondop> [IntVal 1]) (n, m)}"
(* IntVal 1 *)
values "{m_val m 0 |n m. (real_fib \<diamondop> [IntVal 2]) (n, m)}"
(* IntVal 2 *)
values "{m_val m 0 |n m. (real_fib \<diamondop> [IntVal 3]) (n, m)}"
(* IntVal 3 *)
values "{m_val m 0 |n m. (real_fib \<diamondop> [IntVal 4]) (n, m)}"
(* IntVal 5 *)
values "{m_val m 0 |n m. (real_fib \<diamondop> [IntVal 5]) (n, m)}"
(* IntVal 8 *)
values "{m_val m 0 |n m. (real_fib \<diamondop> [IntVal 6]) (n, m)}"
(* IntVal 13 *)
values "{m_val m 0 |n m. (real_fib \<diamondop> [IntVal 7]) (n, m)}"
*)

end