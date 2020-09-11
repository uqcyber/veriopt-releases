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

fun input_index :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index g n n' = find_index n' (g_inputs g n)"

fun phi_inputs :: "Graph \<Rightarrow> nat \<Rightarrow> ID list \<Rightarrow> ID list" where
  "phi_inputs g i nodes = (map (\<lambda>n. (inp g n)!(i + 1)) nodes)"

fun set_phis :: "ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_phis [] [] m = m" |
  "set_phis (nid # xs) (v # vs) m = (set_phis xs vs (m(nid := v)))" |
  "set_phis [] (v # vs) m = m" |
  "set_phis (x # xs) [] m = m"

fun inpu :: "Graph \<Rightarrow> ID \<Rightarrow> nat \<Rightarrow> ID" where
  "inpu g nid i = (inp g nid)!i"


inductive
  step :: "Graph \<Rightarrow> (ID \<times> MapState) \<Rightarrow> (ID \<times> MapState) \<Rightarrow> bool" ("_ \<turnstile> _\<mapsto>_" 55) and
  step_top :: "Graph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool" ("_ \<turnstile> _ \<longrightarrow> _" 55) and 
  eval_exp :: "Graph \<Rightarrow> (ID \<times> MapState) \<Rightarrow> Value \<Rightarrow> bool" (" _ _\<rightarrow>_" 55) and

  eval_all :: "Graph \<Rightarrow> ID list \<Rightarrow> MapState \<Rightarrow> Value list \<Rightarrow> bool" ("_ _ _\<longmapsto>_" 55)
  for g
  where


  "g [] m \<longmapsto> []" |
  "\<lbrakk>g (nid, m) \<rightarrow> v; g xs m \<longmapsto> vs\<rbrakk> \<Longrightarrow> g (nid # xs) m \<longmapsto> (v # vs)" |
  "\<lbrakk>g \<turnstile> (nid, m) \<mapsto> (nid', m')\<rbrakk> \<Longrightarrow> g \<turnstile> (nid, m) # xs \<longrightarrow> (nid', m') # xs" |

  CallNodeStep:
  "\<lbrakk>kind g nid = CallNode start\<rbrakk>
   \<Longrightarrow> g \<turnstile> (nid, m)#xs \<longrightarrow> (start, (\<lambda>id. UndefVal))#(nid,m)#xs" |


  CallNodeEval:
  "\<lbrakk>kind g nid = CallNode start\<rbrakk>
  \<Longrightarrow> g (nid, m) \<rightarrow> m nid" |

(*
  ReturnNode:
  "\<lbrakk>kind g nid = ReturnNode;
    g ((inp g nid)!0, m) \<rightarrow> v;
    m' = m(call_nid := v)
    \<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m)#(call_nid,call_m)#xs \<longrightarrow> ((succ g call_nid)!0,m')#xs" |
*)
  ReturnNode:
  "\<lbrakk>kind g nid = ReturnNode;
    g ((inp g nid)!0, m) \<rightarrow> v\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) \<mapsto> (0, m(0 := v))" |

  SequentialNode:
  "\<lbrakk>node = kind g nid;
    node \<in> {StartNode, BeginNode} \<union> merge_nodes\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) \<mapsto> ((succ g nid)!0, m)" |

  ParameterNode:
  "\<lbrakk>kind g nid = ParameterNode i\<rbrakk>
  \<Longrightarrow> g (nid, m) \<rightarrow> (m nid)" |

  ConstantNode:
  "\<lbrakk>kind g nid = ConstantNode c\<rbrakk>
  \<Longrightarrow> g (nid, m) \<rightarrow> (IntVal (word_of_int c))" |

  UnaryNode:
  "\<lbrakk>kind g nid \<in> unary_nodes;
    g ((inp g nid)!0, m) \<rightarrow> v\<rbrakk> 
    \<Longrightarrow> g (nid, m) \<rightarrow> (unary_expr (kind g nid) v)" |

  BinaryNode:
  "\<lbrakk>
    kind g nid \<in> binary_nodes;
    g (inpu g nid 0, m) \<rightarrow> v1;
    g (inpu g nid 1, m) \<rightarrow> v2\<rbrakk> 
    \<Longrightarrow> g (nid, m) \<rightarrow> (binary_expr (kind g nid) v1 v2)" |

  IfNode:
  "\<lbrakk>kind g nid = IfNode;
    g ((inp g nid)!0, m) \<rightarrow> (IntVal cond)\<rbrakk>
   \<Longrightarrow> g \<turnstile> (nid, m) \<mapsto> ((succ g nid)!(if val_to_bool cond then 0 else 1), m)"  

  (* Solution to the eval_all but the evalution gives up :(
   * \<forall> i. i < length inputs \<longrightarrow> (\<exists> s' . (inputs!i \<mapsto> (s',vs!i))); *)
(*
  EndNodes:
  "\<lbrakk>node = kind g nid;
    node \<in> end_nodes;
    kind g merge = MergeNode;

    (inp g merge)!i = nid;

    phis = (phi_list g merge);
    inputs = (phi_inputs g i phis);
    g inputs m \<longmapsto> vs;

    m' = (set_phis phis vs m)\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) \<mapsto> (merge, m')" |

  PhiNode:
  "\<lbrakk>kind g nid = PhiNode\<rbrakk>
   \<Longrightarrow>  g (nid, m) \<rightarrow> m nid"
*)

code_pred step .
code_pred step_top .
code_pred eval_exp .
code_pred eval_all .


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

fun ir_to_graph_i :: "IRGraph \<Rightarrow> ID list \<Rightarrow> Graph \<Rightarrow> Graph" where
  "ir_to_graph_i ir [] g = g" |
  "ir_to_graph_i ir (n # ns) g = (ir_to_graph_i ir ns g)(n := (N (g_nodes ir n) (g_inputs ir n) (g_successors ir n)))"

fun ir_to_graph :: "IRGraph \<Rightarrow> Graph" where
  "ir_to_graph g = ir_to_graph_i g 
      (sorted_list_of_set (g_ids g)) (\<lambda>x . (N StartNode [] []))"

notepad begin 
  have "input_index simple_if_graph 10 5 = 0" by eval
  have "input_index simple_if_graph 10 6 = 1" by eval
  have "input_index simple_if_graph 11 10 = 0" by eval
  have "input_index simple_if_graph 11 9 = 1" by eval
  have "input_index simple_if_graph 11 7 = 2" by eval
  have "input_index simple_if_graph 11 20 = 3" by eval
  have "phi_list (ir_to_graph simple_if_graph) 10 = [11]" by eval
end


inductive eval_graph :: "Graph \<Rightarrow> ID \<times> MapState \<Rightarrow> ID \<times> MapState \<Rightarrow> bool" where
  "\<lbrakk>g \<turnstile> (nid, m) \<mapsto> (next, m');
    next = 0\<rbrakk> \<Longrightarrow> eval_graph g (nid, m) (next, m')" |

  "\<lbrakk>g \<turnstile> (nid, m) \<mapsto> (next, m');
    next \<noteq> 0;
    eval_graph g (next, m') (next', m'')\<rbrakk> \<Longrightarrow> eval_graph g (nid, m) (next', m'')"

code_pred "eval_graph" .

(* IntVal 10 *)
definition simple_return :: "Graph" where
  "simple_return = (ir_to_graph simple_return_graph)"
values "{(n, map m [0]) |n m. simple_return \<turnstile> (0, simple_return_map) \<mapsto> (n, m)}"
values "{(n, map m [0]) |n m. simple_return \<turnstile> (2, simple_return_map) \<mapsto> (n, m)}"
value "(inp simple_return 2)!0"
values "{v |v. simple_return (1, simple_return_map) \<rightarrow> v}"

values "{map m [0] |n m. eval_graph simple_return (0, double_param_map) (n, m)}"

definition double_param :: "Graph" where
  "double_param = (ir_to_graph double_param_graph)"
values "{(n, map m [0]) |n m. double_param \<turnstile> (0, double_param_map) \<mapsto> (n, m)}"
values "{(n, map m [0]) |n m. double_param \<turnstile> (3, double_param_map) \<mapsto> (n, m)}"

values "{map m [0] |n m. eval_graph double_param (0, double_param_map) (n, m)}"

definition simple_if :: "Graph" where
  "simple_if = (ir_to_graph simple_if_graph)"
(* IntVal 20 *)
values "{(n, map m [0]) |n m. simple_if \<turnstile> (0, simple_if_map) \<mapsto> (n, m)}"
values "{map m [0] |n m. eval_graph simple_if_graph (0, StartNode) simple_if_map (n, m)}"
(* IntVal 120 *)
values "{(n, map m [0]) |n m. simple_if_graph (0, StartNode) (new_map simple_if_graph [IntVal 1, IntVal 20, IntVal 100]) \<mapsto> (n, m)}"
values "{map m [0] |n m. eval_graph simple_if_graph (0, StartNode) (new_map simple_if_graph [IntVal 1, IntVal 20, IntVal 100]) (n, m)}"

end