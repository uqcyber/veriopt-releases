section \<open>Inductive semantics of nodes\<close>

theory InductiveSemantics
  imports
    "AbsGraph"
    "HOL-Word.More_Word"
begin

type_synonym int32 = "32 word"

datatype Value =
  UndefVal |
  IntVal int32

type_synonym MapState = "ID \<Rightarrow> Value"


fun val_to_bool :: "int32 \<Rightarrow> bool" where
  "val_to_bool x = (if x = 0 then False else True)" 

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal 1)" |
  "bool_to_val False = (IntVal 0)"

fun unary_expr :: "IRNode \<Rightarrow> Value \<Rightarrow> Value" where
  "unary_expr AbsNode (IntVal x) = (IntVal (if (x < 0) then -x else x))" |
  "unary_expr NegateNode (IntVal x) = (IntVal (uminus x))" |
  "unary_expr LogicNegationNode (IntVal x) = (bool_to_val (\<not>(val_to_bool x)))" |
  "unary_expr _ _ = UndefVal"

fun binary_expr :: "IRNode \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "binary_expr AddNode (IntVal x) (IntVal y) = (IntVal (x + y))" |
  "binary_expr SubNode (IntVal x) (IntVal y) = (IntVal (x - y))" |
  "binary_expr MulNode (IntVal x) (IntVal y) = (IntVal (x * y))" |
  "binary_expr AndNode (IntVal x) (IntVal y) = (IntVal (x AND y))" |
  "binary_expr OrNode (IntVal x) (IntVal y) = (IntVal (x OR y))" |
  "binary_expr XorNode (IntVal x) (IntVal y) = (IntVal (x XOR y))" |
  "binary_expr IntegerLessThanNode (IntVal x) (IntVal y) = (bool_to_val (x < y))" |
  "binary_expr IntegerEqualsNode (IntVal x) (IntVal y) = (bool_to_val (x = y))" |
  "binary_expr _ _ _ = UndefVal"

definition unary_nodes :: "IRNode set" where
  "unary_nodes = {AbsNode, NegateNode}"

definition binary_nodes :: "IRNode set" where
  "binary_nodes = {AddNode, SubNode, MulNode, AndNode, 
                   OrNode, XorNode, IntegerLessThanNode,
                   IntegerEqualsNode}"

definition merge_nodes :: "IRNode set" where
  "merge_nodes = {MergeNode, LoopBeginNode}"

definition end_nodes :: "IRNode set" where
  "end_nodes = {EndNode, LoopEndNode}"

(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index val (x # xs) = (if (x=val) then 0 else find_index val xs + 1)"

fun phi_list :: "Graph \<Rightarrow> ID \<Rightarrow> ID list" where
  "phi_list g nid = 
    (filter (\<lambda>x.((kind g x)=PhiNode))
      (sorted_list_of_set (usagex g nid)))"

fun input_index :: "Graph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index g n n' = find_index n' (inp g n)"

fun phi_inputs :: "Graph \<Rightarrow> nat \<Rightarrow> ID list \<Rightarrow> ID list" where
  "phi_inputs g i nodes = (map (\<lambda>n. (inp g n)!(i + 1)) nodes)"

fun set_phis :: "ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_phis [] [] m = m" |
  "set_phis (nid # xs) (v # vs) m = (set_phis xs vs (m(nid := v)))" |
  "set_phis [] (v # vs) m = m" |
  "set_phis (x # xs) [] m = m"

fun set_params :: "Graph \<Rightarrow> ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_params g [] vs m = m" |
  "set_params g (nid # xs) vs m = (let m' = (set_params g xs vs m) in 
   (case (kind g nid) of 
    (ParameterNode i) \<Rightarrow> m'(nid := (vs!i)) |
    _ \<Rightarrow> m'))"


fun usage :: "Graph \<Rightarrow> ID \<Rightarrow> nat \<Rightarrow> ID" where
  "usage g nid i = (sorted_list_of_set (usagex g nid))!i"


inductive
  eval :: "Graph \<Rightarrow> (ID \<times> MapState) \<Rightarrow> Value \<Rightarrow> bool" (" _ _\<rightarrow>_" 55) and
  eval_all :: "Graph \<Rightarrow> ID list \<Rightarrow> MapState \<Rightarrow> Value list \<Rightarrow> bool" ("_ _ _\<longmapsto>_" 55)
  for g
  where

  CallNodeEval:
  "\<lbrakk>kind g nid = CallNode start\<rbrakk>
    \<Longrightarrow> g (nid, m) \<rightarrow> m nid" |

  ParameterNode:
  "\<lbrakk>kind g nid = ParameterNode i\<rbrakk>
    \<Longrightarrow> g (nid, m) \<rightarrow> m nid" |

  PhiNode:
  "\<lbrakk>kind g nid = PhiNode\<rbrakk>
    \<Longrightarrow>  g (nid, m) \<rightarrow> m nid" |

  ConstantNode:
  "\<lbrakk>kind g nid = ConstantNode c\<rbrakk>
    \<Longrightarrow> g (nid, m) \<rightarrow> (IntVal (word_of_int c))" |

  UnaryNode:
  "\<lbrakk>kind g nid \<in> unary_nodes;
    g ((inp g nid)!0, m) \<rightarrow> v\<rbrakk> 
    \<Longrightarrow> g (nid, m) \<rightarrow> (unary_expr (kind g nid) v)" |

  BinaryNode:
  "\<lbrakk>kind g nid \<in> binary_nodes;
    g ((inp g nid)!0, m) \<rightarrow> v1;
    g ((inp g nid)!1, m) \<rightarrow> v2\<rbrakk> 
    \<Longrightarrow> g (nid, m) \<rightarrow> (binary_expr (kind g nid) v1 v2)" |

  "g [] m \<longmapsto> []" |
  "\<lbrakk>g (nid, m) \<rightarrow> v; g xs m \<longmapsto> vs\<rbrakk> \<Longrightarrow> g (nid # xs) m \<longmapsto> (v # vs)"

code_pred eval .
code_pred eval_all .
  

inductive
  step :: "Graph \<Rightarrow> (ID \<times> MapState) \<Rightarrow> (ID \<times> MapState) \<Rightarrow> bool" ("_ \<turnstile> _\<mapsto>_" 55) and
  step_top :: "Graph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool" ("_ \<turnstile> _ \<longrightarrow> _" 55) 
  for g
  where

  "\<lbrakk>g \<turnstile> (nid, m) \<mapsto> (nid', m')\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) # xs \<longrightarrow> (nid', m') # xs" |

  CallNodeStep:
  "\<lbrakk>kind g nid = CallNode start;
    g (inp g nid) m \<longmapsto> vs;
    m' = (set_params g (sorted_list_of_set (fset (fmdom g))) vs m)\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m)#xs \<longrightarrow> (start, m')#(nid,m)#xs" |

  ReturnNode:
  "\<lbrakk>kind g nid = ReturnNode;
    g ((inp g nid)!0, m) \<rightarrow> v;
    m' = call_m(call_nid := v)\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m)#(call_nid,call_m)#xs \<longrightarrow> ((succ g call_nid)!0,m')#xs" |

  ExitReturnNode:
  "\<lbrakk>kind g nid = ReturnNode;
    g ((inp g nid)!0, m) \<rightarrow> v;
    m' = m(nid := v)\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m)#[] \<longrightarrow> []" |

  SequentialNode:
  "\<lbrakk>node = kind g nid;
    node \<in> {StartNode, BeginNode} \<union> merge_nodes\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) \<mapsto> ((succ g nid)!0, m)" |

  IfNode:
  "\<lbrakk>kind g nid = IfNode;
    g ((inp g nid)!0, m) \<rightarrow> (IntVal cond)\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m) \<mapsto> ((succ g nid)!(if val_to_bool cond then 0 else 1), m)" |  

  (* Solution to the eval_all but the evalution gives up :(
   * \<forall> i. i < length inputs \<longrightarrow> (\<exists> s' . (inputs!i \<mapsto> (s',vs!i))); *)

  EndNodes:
  "\<lbrakk>kind g nid \<in> end_nodes;

    merge = usage g nid 0;
    kind g merge \<in> merge_nodes;

    i = input_index g merge nid;

    phis = (phi_list g merge);
    inputs = (phi_inputs g i phis);
    g inputs m \<longmapsto> vs;

    m' = (set_phis phis vs m)\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) \<mapsto> (merge, m')"


code_pred step .
code_pred step_top .

fun ir_to_graph_i :: "IRGraph \<Rightarrow> ID list \<Rightarrow> Graph \<Rightarrow> Graph" where
  "ir_to_graph_i ir [] g = g" |
  "ir_to_graph_i ir (n # ns) g = fmupd n (N (g_nodes ir n) (g_inputs ir n) (g_successors ir n)) (ir_to_graph_i ir ns g)"

fun ir_to_graph :: "IRGraph \<Rightarrow> Graph" where
  "ir_to_graph g = ir_to_graph_i g 
      (sorted_list_of_set (g_ids g)) fmempty"

(* Example graph evaluation *)
fun new_map_i :: "IRGraph \<Rightarrow> Value list \<Rightarrow> ID list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "new_map_i g ps [] m = m" |
  "new_map_i g ps (nid # xs) m = (let m' = (new_map_i g ps xs m) in 
   (case ((g_nodes g) nid) of 
    (ParameterNode i) \<Rightarrow> m'(nid := (ps!i)) |
    _ \<Rightarrow> m'))"

fun new_map :: "IRGraph \<Rightarrow> Value list \<Rightarrow> MapState" where
  "new_map graph params = new_map_i graph params 
    (sorted_list_of_set (g_ids graph)) (\<lambda> x . UndefVal)"


definition simple_return_graph :: IRGraph where
  "simple_return_graph =
    (add_node 2 ReturnNode [1] []
    (add_node 1 (ConstantNode 42) [] []
    (add_node 0 StartNode [] [2]
    empty_graph)))"
lemma "wff_graph simple_return_graph"
  unfolding simple_return_graph_def by simp
definition simple_return_map :: "MapState" where
  "simple_return_map = new_map simple_return_graph []"
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
definition double_param_map :: "MapState" where
  "double_param_map = new_map double_param_graph [IntVal 5]"
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
definition simple_if_map :: "MapState" where
  "simple_if_map = new_map simple_if_graph [IntVal 0, IntVal 20, IntVal 100]"
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
definition simple_call_map :: "MapState" where
  "simple_call_map = new_map simple_call_graph []"
definition simple_call :: "Graph" where
  "simple_call = (ir_to_graph simple_call_graph)"

definition factorial_graph :: IRGraph where
  "factorial_graph =
    (add_node 14 ReturnNode [13] []
    (add_node 13 (CallNode 1) [12] [14]
    (add_node 12 (ConstantNode 5) [] []
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
    (add_node 0 StartNode [] [13]
    empty_graph)))))))))))))))"
lemma "wff_graph factorial_graph"
  unfolding factorial_graph_def by simp
definition factorial_map :: "MapState" where
  "factorial_map = new_map factorial_graph []"
definition factorial :: "Graph" where
  "factorial = (ir_to_graph factorial_graph)"

definition fib_graph :: IRGraph where
  "fib_graph =
    (add_node 17 ReturnNode [16] []
    (add_node 16 (CallNode 1) [15] [17]
    (add_node 15 (ConstantNode 8) [] []
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
    (add_node 0 StartNode [] [16]
    empty_graph))))))))))))))))))"
lemma "wff_graph fib_graph"
  unfolding fib_graph_def by simp
definition fib_map :: "MapState" where
  "fib_map = new_map fib_graph []"
definition fib :: "Graph" where
  "fib = (ir_to_graph fib_graph)"

notepad begin 
  have "input_index simple_if 10 5 = 0" by eval
  have "input_index simple_if 10 6 = 1" by eval
  have "input_index simple_if 11 10 = 0" by eval
  have "input_index simple_if 11 9 = 1" by eval
  have "input_index simple_if 11 7 = 2" by eval
  have "input_index simple_if 11 20 = 3" by eval
  have "phi_list simple_if 10 = [11]" by eval
end


inductive exec :: "Graph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow>* _")
  where
  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    length s' \<noteq> 0;
    exec g s' s''\<rbrakk> 
    \<Longrightarrow> exec g s s''" |

  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    length s' = 0\<rbrakk>
    \<Longrightarrow> exec g s s"
code_pred "exec" .

inductive exec_debug :: "Graph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> nat \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool" ("_ \<turnstile> _ \<longrightarrow>*_* _")
  where
  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    n > 0;
    exec_debug g s' (n - 1) s''\<rbrakk> 
    \<Longrightarrow> exec_debug g s n s''" |

  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    n = 0\<rbrakk>
    \<Longrightarrow> exec_debug g s n s"
code_pred "exec_debug" .

(* NB: The starting state is duplicated causing the program to be executed twice
       The reason for this is that the top step of ReturnNode empties
       the state list to signal completion, this means we can't access the state

   Discuss ways to fix this
 *)
inductive eval_graph :: "Graph \<Rightarrow> (ID \<times> MapState) \<Rightarrow> (ID \<times> MapState) \<Rightarrow> bool" where
  "\<lbrakk>g \<turnstile> [start, start] \<rightarrow>* (end # xs)\<rbrakk>
    \<Longrightarrow> eval_graph g start end"
code_pred "eval_graph" .


(* Simple Return *)
(* IntVal 42 *)
values "{map m [0] |n m. eval_graph simple_return (0, double_param_map) (n, m)}"

(* Double Param *)
(* IntVal 10 *)
values "{map m [0] |n m. eval_graph double_param (0, double_param_map) (n, m)}"

(* Simple If *)
(* IntVal 20 *)
values "{map m [0] |n m. eval_graph simple_if (0, simple_if_map) (n, m)}"
(* IntVal 120 *)
values "{map m [0] |n m. eval_graph simple_if (0, (new_map simple_if_graph [IntVal 1, IntVal 20, IntVal 100])) (n, m)}"

(* Simple Call *)
(* IntVal 24 *)
values "{map m [0] |n m. eval_graph simple_call (0, simple_call_map) (n, m)}"

(* Factorial *)
values "{snd (s!0) 2 |s. factorial \<turnstile> [(0, factorial_map)] \<longrightarrow>*6* s}"


values "{s |s. factorial \<turnstile> [(0, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(13, factorial_map)] \<longrightarrow> s}"
definition factorial_map' :: "MapState" where
  "factorial_map' = set_params factorial 
    (sorted_list_of_set (fset (fmdom factorial)))
    [IntVal 5] factorial_map"
values "{s |s. factorial \<turnstile> [(1, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(5, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
definition factorial_map'' :: "MapState" where
  "factorial_map'' = set_params factorial 
    (sorted_list_of_set (fset (fmdom factorial)))
    [IntVal 4] factorial_map'"
values "{s |s. factorial \<turnstile> [(1, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(5, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
definition factorial_map''' :: "MapState" where
  "factorial_map''' = set_params factorial 
    (sorted_list_of_set (fset (fmdom factorial)))
    [IntVal 3] factorial_map''"
values "{s |s. factorial \<turnstile> [(1, factorial_map'''),(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(5, factorial_map'''),(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(9, factorial_map'''),(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
definition factorial_map'''' :: "MapState" where
  "factorial_map'''' = set_params factorial 
    (sorted_list_of_set (fset (fmdom factorial)))
    [IntVal 2] factorial_map'''"
values "{s |s. factorial \<turnstile> [(1, factorial_map''''),(9, factorial_map'''),(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(5, factorial_map''''),(9, factorial_map'''),(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(9, factorial_map''''),(9, factorial_map'''),(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
definition factorial_map''''' :: "MapState" where
  "factorial_map''''' = set_params factorial 
    (sorted_list_of_set (fset (fmdom factorial)))
    [IntVal 1] factorial_map'''"
values "{s |s. factorial \<turnstile> [(9, factorial_map'''''),(9, factorial_map''''),(9, factorial_map'''),(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(1, factorial_map'''''),(9, factorial_map''''),(9, factorial_map'''),(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(5, factorial_map'''''),(9, factorial_map''''),(9, factorial_map'''),(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"

values "{s |s. factorial \<turnstile> [(6, factorial_map'''''),(9, factorial_map''''),(9, factorial_map'''),(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"
values "{s |s. factorial \<turnstile> [(6, factorial_map'''''),(9, factorial_map''''),(9, factorial_map'''),(9, factorial_map''),(9, factorial_map'),(13, factorial_map)] \<longrightarrow> s}"

(* IntVal 120 *)
values "{map m [0] |n m. eval_graph factorial (0, factorial_map) (n, m)}"

(* IntVal 21 *)
values "{map m [0] |n m. eval_graph fib (0, fib_map) (n, m)}"

end