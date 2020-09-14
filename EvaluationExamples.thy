section \<open>Example program evaluation\<close>

theory EvaluationExamples
  imports
    InductiveSemantics
begin
fun ir_to_graph_i :: "IRGraph \<Rightarrow> ID list \<Rightarrow> Graph \<Rightarrow> Graph" where
  "ir_to_graph_i ir [] g = g" |
  "ir_to_graph_i ir (n # ns) g = fmupd n (N (g_nodes ir n) (g_inputs ir n) (g_successors ir n)) (ir_to_graph_i ir ns g)"

fun ir_to_graph :: "IRGraph \<Rightarrow> Graph" where
  "ir_to_graph g = ir_to_graph_i g 
      (sorted_list_of_set (g_ids g)) fmempty"

definition simple_return_graph :: IRGraph where
  "simple_return_graph =
    (add_node 2 ReturnNode [1] []
    (add_node 1 (ConstantNode 42) [] []
    (add_node 0 StartNode [] [2]
    empty_graph)))"
lemma "wff_graph simple_return_graph"
  unfolding simple_return_graph_def by simp
definition simple_return :: "Graph" where
  "simple_return = (ir_to_graph simple_return_graph)"

definition double_param_graph :: IRGraph where
  "double_param_graph =
    (add_node 3 ReturnNode [2] []
    (add_node 2 AddNode [1, 1] []
    (add_node 1 (ParameterNode 0) [] []
    (add_node 0 StartNode [] [3]
    empty_graph))))"
lemma "wff_graph double_param_graph"
  unfolding double_param_graph_def by simp
definition double_param :: "Graph" where
  "double_param = (ir_to_graph double_param_graph)"

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
lemma "wff_graph simple_if_graph"
  unfolding simple_if_graph_def by simp
definition simple_if :: "Graph" where
  "simple_if = (ir_to_graph simple_if_graph)"

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
lemma "wff_graph simple_call_graph"
  unfolding simple_call_graph_def by simp
definition simple_call :: "Graph" where
  "simple_call = (ir_to_graph simple_call_graph)"

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
lemma "wff_graph factorial_graph"
  unfolding factorial_graph_def by simp
definition factorial :: "Graph" where
  "factorial = (ir_to_graph factorial_graph)"

definition fib_graph :: IRGraph where
  "fib_graph =
    (add_node 16 ReturnNode [15] []
    (add_node 15 (CallNode 1) [2] [16]
    (add_node 14 ReturnNode [13] []
    (add_node 13 AddNode [11,12] []
    (add_node 12 (CallNode 1) [10] [14]
    (add_node 11 (CallNode 1) [9] [12]
    (add_node 10 SubNode [2,8] []
    (add_node 9 SubNode [2,7] []
    (add_node 8 (ConstantNode 2) [] []
    (add_node 7 (ConstantNode 1) [] []
    (add_node 6 ReturnNode [2] []
    (add_node 5 IfNode [4] [6,11]
    (add_node 4 IntegerLessThanNode [2,3] []
    (add_node 3 (ConstantNode 2) [] []
    (add_node 2 (ParameterNode 0) [] []
    (add_node 1 StartNode [] [5]
    (add_node 0 StartNode [] [15]
    empty_graph)))))))))))))))))"
lemma "wff_graph fib_graph"
  unfolding fib_graph_def by simp
definition fib :: "Graph" where
  "fib = (ir_to_graph fib_graph)"

(* NB: The starting state is duplicated causing the program to be executed twice
       The reason for this is that the top step of ReturnNode empties
       the state list to signal completion, this means we can't access the state

   Discuss ways to fix this
 *)
inductive eval_graph :: "Graph \<Rightarrow> Value list \<Rightarrow> (ID \<times> MapState) \<Rightarrow> bool" ("_\<diamondop>_")
  where
  "\<lbrakk>state = new_map g params;
    g \<turnstile> [(0, state), (0, state)] \<longrightarrow>* (end # xs)\<rbrakk>
    \<Longrightarrow> eval_graph g params end"
code_pred "eval_graph" .


(* Simple Return *)
(* IntVal 42 *)
values "{m 0 |n m. (simple_return \<diamondop> []) (n, m)}"

(* Double Param *)
(* IntVal 10 *)
values "{m 0 |n m. (double_param \<diamondop> [IntVal 5]) (n, m)}"
(* IntVal 50 *)
values "{m 0 |n m. (double_param \<diamondop> [IntVal 25]) (n, m)}"
(* IntVal 256 *)
values "{m 0 |n m. (double_param \<diamondop> [IntVal 128]) (n, m)}"
(* IntVal 198 *)
values "{m 0 |n m. (double_param \<diamondop> [IntVal 99]) (n, m)}"

(* Simple If *)
(* IntVal 20 *)
values "{m 0 |n m. (simple_if \<diamondop> [IntVal 0, IntVal 20, IntVal 100]) (n, m)}"
(* IntVal 120 *)
values "{m 0 |n m. (simple_if \<diamondop> [IntVal 1, IntVal 20, IntVal 100]) (n, m)}"

(* Simple Call *)
(* IntVal 24 *)
values "{m 0 |n m. (simple_call \<diamondop> []) (n, m)}"

(* Factorial *)
(* IntVal 1 *)
values "{m 0 |n m. (factorial \<diamondop> [IntVal 1]) (n, m)}"
(* IntVal 2 *)
values "{m 0 |n m. (factorial \<diamondop> [IntVal 2]) (n, m)}"
(* IntVal 6 *)
values "{m 0 |n m. (factorial \<diamondop> [IntVal 3]) (n, m)}"
(* IntVal 24 *)
values "{m 0 |n m. (factorial \<diamondop> [IntVal 4]) (n, m)}"
(* IntVal 120 *)
values "{m 0 |n m. (factorial \<diamondop> [IntVal 5]) (n, m)}"
(* IntVal 720 *)
values "{m 0 |n m. (factorial \<diamondop> [IntVal 6]) (n, m)}"
(* IntVal 5040 *)
values "{m 0 |n m. (factorial \<diamondop> [IntVal 7]) (n, m)}"

(* Fibonacci *)
(* IntVal 0 *)
values "{m 0 |n m. (fib \<diamondop> [IntVal 0]) (n, m)}"
(* IntVal 1 *)
values "{m 0 |n m. (fib \<diamondop> [IntVal 1]) (n, m)}"
(* IntVal 1 *)
values "{m 0 |n m. (fib \<diamondop> [IntVal 2]) (n, m)}"
(* IntVal 2 *)
values "{m 0 |n m. (fib \<diamondop> [IntVal 3]) (n, m)}"
(* IntVal 3 *)
values "{m 0 |n m. (fib \<diamondop> [IntVal 4]) (n, m)}"
(* IntVal 5 *)
values "{m 0 |n m. (fib \<diamondop> [IntVal 5]) (n, m)}"
(* IntVal 8 *)
values "{m 0 |n m. (fib \<diamondop> [IntVal 6]) (n, m)}"
(* IntVal 13 *)
values "{m 0 |n m. (fib \<diamondop> [IntVal 7]) (n, m)}"
(* IntVal 21 *)
values "{m 0 |n m. (fib \<diamondop> [IntVal 8]) (n, m)}"

end