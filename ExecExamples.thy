section \<open>Example program evaluation\<close>

theory ExecExamples
  imports
    IRStep
begin

definition simple_return :: IRGraph where
  "simple_return =
    (add_node 2 (ReturnNode (Some 1) None)
    (add_node 1 (ConstantNode 42)
    (add_node 0 (StartNode None 2)
    empty_graph)))"

(*
definition double_param_graph :: IRGraph where
  "double_param_graph =
    (add_node 3 ReturnNode [2] []
    (add_node 2 AddNode [1, 1] []
    (add_node 1 (ParameterNode 0) [] []
    (add_node 0 (StartNode None 3)
    empty_graph))))"

definition simple_if_graph :: IRGraph where
  "simple_if_graph =
    (add_node 12 ReturnNode [11] []
    (add_node 11 PhiNode [10,9,7] []
    (add_node 10 MergeNode [5,6] [12]
    (add_node 9 AddNode [7,8] []
    (add_node 8 (ParameterNode 2) [] []
    (add_node 7 (ParameterNode 1) [] []
    (add_node 6 EndNode [] []
    (add_node 5 EndNode [] []
    (add_node 4 BeginNode [] [6]
    (add_node 3 BeginNode [] [5]
    (add_node 2 IfNode [1] [3,4] 
    (add_node 1 (ParameterNode 0) [] []
    (add_node 0 StartNode [] [2]
    empty_graph)))))))))))))"

definition simple_call_graph :: IRGraph where
  "simple_call_graph =
    (add_node 7 ReturnNode [6] []
    (add_node 6 AddNode [1, 5] []
    (add_node 5 (CallNode 2) [] [7]
    (add_node 4 ReturnNode [3] []
    (add_node 3 (ConstantNode 12) [] []
    (add_node 2 StartNode [] [4]
    (add_node 1 (CallNode 2) [] [5]
    (add_node 0 StartNode [] [1]
    empty_graph))))))))"

definition factorial_graph :: IRGraph where
  "factorial_graph =
    (add_node 13 ReturnNode [12] []
    (add_node 12 (CallNode 1) [2] [13]
    (add_node 11 ReturnNode [10] []
    (add_node 10 MulNode [2,9] []
    (add_node 9 (CallNode 1) [8] [11]
    (add_node 8 SubNode [2,7] []
    (add_node 7 (ConstantNode 1) [] []
    (add_node 6 ReturnNode [2] []
    (add_node 5 IfNode [4] [6,9]
    (add_node 4 IntegerEqualsNode [2,3] []
    (add_node 3 (ConstantNode 1) [] []
    (add_node 2 (ParameterNode 0) [] []
    (add_node 1 StartNode [] [5]
    (add_node 0 StartNode [] [12]
    empty_graph))))))))))))))"
*)
(* TODO: fix up CallNode s! *)
definition fib :: IRGraph where
  "fib =
    (add_node 16 (ReturnNode (Some 15) None)
    (add_node 15 (CallNode 1 [2] [16])
    (add_node 14 (ReturnNode (Some 13) None)
    (add_node 13 (AddNode 11 12)
    (add_node 12 (CallNode 1 [10] [14])
    (add_node 11 (CallNode 1 [9] [12])
    (add_node 10 (SubNode 2 8)
    (add_node 9 (SubNode 2 7)
    (add_node 8 (ConstantNode 2)
    (add_node 7 (ConstantNode 1)
    (add_node 6 (ReturnNode (Some 2) None)
    (add_node 5 (IfNode 4 6 11)
    (add_node 4 (IntegerLessThanNode 2 3)
    (add_node 3 (ConstantNode 2)
    (add_node 2 (ParameterNode 0)
    (add_node 1 (StartNode None 5)
    (add_node 0 (StartNode None 15)
    empty_graph)))))))))))))))))"
(*
definition loop_graph :: IRGraph where
  "loop_graph =
    (add_node 13 ReturnNode [7] []
    (add_node 12 LoopEndNode [] []
    (add_node 11 BeginNode [] [12]
    (add_node 10 IfNode [9] [11,13]
    (add_node 9 IntegerLessThanNode [7,6] []
    (add_node 8 AddNode [7,5] []
    (add_node 7 PhiNode [3,4,8] []
    (add_node 6 (ParameterNode 0) [] []
    (add_node 5 (ConstantNode 1) [] []
    (add_node 4 (ConstantNode 0) [] []
    (add_node 3 LoopBeginNode [2,12] [10]
    (add_node 2 EndNode [] []
    (add_node 1 BeginNode [] [2]
    (add_node 0 StartNode [] [1]
    empty_graph))))))))))))))"

definition sum_graph :: IRGraph where
  "sum_graph =
    (add_node 15 ReturnNode [10] []
    (add_node 14 LoopEndNode [] []
    (add_node 13 BeginNode [] [14]
    (add_node 12 IfNode [11] [13,15]
    (add_node 11 IntegerLessThanNode [7,6] []
    (add_node 10 AddNode [8,7] []
    (add_node 9 AddNode [7,5] []
    (add_node 8 PhiNode [3,4,10] []
    (add_node 7 PhiNode [3,4,9] []
    (add_node 6 (ParameterNode 0) [] []
    (add_node 5 (ConstantNode 1) [] []
    (add_node 4 (ConstantNode 0) [] []
    (add_node 3 LoopBeginNode [2,14] [12]
    (add_node 2 EndNode [] []
    (add_node 1 BeginNode [] [2]
    (add_node 0 StartNode [] [1]
    empty_graph))))))))))))))))"
*)



(* NB: The starting state is duplicated causing the program to be executed twice
       The reason for this is that the top step of ReturnNode empties
       the state list to signal completion, this means we can't access the state

   Discuss ways to fix this
 *)
inductive exec_graph :: "IRGraph \<Rightarrow> Value list \<Rightarrow> (ID \<times> MapState) \<Rightarrow> bool" ("_\<diamondop>_")
  where
  "\<lbrakk>state = new_map ps;
    g \<turnstile> [(0, state), (0, state)] \<longrightarrow>* (end # xs)\<rbrakk>
    \<Longrightarrow> exec_graph g ps end"
code_pred [show_modes] "exec_graph" .


(* Simple Return *)
(* IntVal 42 *)
values "{m_val m 0 |n m. (simple_return \<diamondop> []) (n, m)}"

(* Double Param *)
(* IntVal 10 *)
values "{m_val m 0 |n m. (double_param \<diamondop> [IntVal 5]) (n, m)}"
(* IntVal 50 *)
values "{m_val m 0 |n m. (double_param \<diamondop> [IntVal 25]) (n, m)}"
(* IntVal 256 *)
values "{m_val m 0 |n m. (double_param \<diamondop> [IntVal 128]) (n, m)}"
(* IntVal 198 *)
values "{m_val m 0 |n m. (double_param \<diamondop> [IntVal 99]) (n, m)}"

(* Simple If *)
(* IntVal 20 *)
values "{m_val m 0 |n m. (simple_if \<diamondop> [IntVal 0, IntVal 20, IntVal 100]) (n, m)}"
(* IntVal 120 *)
values "{m_val m 0 |n m. (simple_if \<diamondop> [IntVal 1, IntVal 20, IntVal 100]) (n, m)}"

(* Simple Call *)
(* IntVal 24 *)
values "{m_val m 0 |n m. (simple_call \<diamondop> []) (n, m)}"

(* Factorial *)
(* IntVal 1 *)
values "{m_val m 0 |n m. (factorial \<diamondop> [IntVal 1]) (n, m)}"
(* IntVal 2 *)
values "{m_val m 0 |n m. (factorial \<diamondop> [IntVal 2]) (n, m)}"
(* IntVal 6 *)
values "{m_val m 0 |n m. (factorial \<diamondop> [IntVal 3]) (n, m)}"
(* IntVal 24 *)
values "{m_val m 0 |n m. (factorial \<diamondop> [IntVal 4]) (n, m)}"
(* IntVal 120 *)
values "{m_val m 0 |n m. (factorial \<diamondop> [IntVal 5]) (n, m)}"
(* IntVal 720 *)
values "{m_val m 0 |n m. (factorial \<diamondop> [IntVal 6]) (n, m)}"
(* IntVal 5040 *)
values "{m_val m 0 |n m. (factorial \<diamondop> [IntVal 7]) (n, m)}"

(* Fibonacci *)
(* IntVal 0 *)
values "{m_val m 0 |n m. (fib \<diamondop> [IntVal 0]) (n, m)}"
(* IntVal 1 *)
values "{m_val m 0 |n m. (fib \<diamondop> [IntVal 1]) (n, m)}"
(* IntVal 1 *)
values "{m_val m 0 |n m. (fib \<diamondop> [IntVal 2]) (n, m)}"
(* IntVal 2 *)
values "{m_val m 0 |n m. (fib \<diamondop> [IntVal 3]) (n, m)}"
(* IntVal 3 *)
values "{m_val m 0 |n m. (fib \<diamondop> [IntVal 4]) (n, m)}"
(* IntVal 5 *)
values "{m_val m 0 |n m. (fib \<diamondop> [IntVal 5]) (n, m)}"
(* IntVal 8 *)
values "{m_val m 0 |n m. (fib \<diamondop> [IntVal 6]) (n, m)}"
(* IntVal 13 *)
values "{m_val m 0 |n m. (fib \<diamondop> [IntVal 7]) (n, m)}"
(* IntVal 21 *)
values "{m_val m 0 |n m. (fib \<diamondop> [IntVal 8]) (n, m)}"

(* Loop *)
(* IntVal 0 *)
values "{m_val m 0 |n m. (loop \<diamondop> [IntVal 0]) (n, m)}"
(* IntVal 1 *)
values "{m_val m 0 |n m. (loop \<diamondop> [IntVal 1]) (n, m)}"
(* IntVal 2 *)
values "{m_val m 0 |n m. (loop \<diamondop> [IntVal 2]) (n, m)}"
(* IntVal 5 *)
values "{m_val m 0 |n m. (loop \<diamondop> [IntVal 5]) (n, m)}"
(* IntVal 10 *)
values "{m_val m 0 |n m. (loop \<diamondop> [IntVal 10]) (n, m)}"


(* Sum *)
(* IntVal 1 *)
values "{m_val m 0 |n m. (sum \<diamondop> [IntVal 1]) (n, m)}"
(* IntVal 3 *)
values "{m_val m 0 |n m. (sum \<diamondop> [IntVal 2]) (n, m)}"
(* IntVal 15 *)
values "{m_val m 0 |n m. (sum \<diamondop> [IntVal 5]) (n, m)}"
(* IntVal 28 *)
values "{m_val m 0 |n m. (sum \<diamondop> [IntVal 7]) (n, m)}"
(* IntVal 210 *)
values "{m_val m 0 |n m. (sum \<diamondop> [IntVal 20]) (n, m)}"


(* Examples generated from Java code *)
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

end