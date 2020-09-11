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

fun node_type :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRNode" where
  "node_type nid g = (g_nodes g) nid"

fun to_node_pair :: "ID \<Rightarrow> IRGraph \<Rightarrow> (ID \<times> IRNode)" where
  "to_node_pair nid g = (nid, (node_type nid g))"

fun get_input :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> ID" where 
  "get_input nid i g = ((g_inputs g nid)!i)"
fun input :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> (ID \<times> IRNode)" where
  "input nid i g = (to_node_pair (get_input nid i g) g)"

fun successor :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> ID" where
  "successor nid i g = ((g_successors g nid)!i)"

fun usage :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> ID" where
  "usage nid i g =
    ((sorted_list_of_set (g_usages g nid))!i)"


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

fun binary_bool_expr :: "IRNode \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> Value" where
  "binary_bool_expr AndNode x y = (bool_to_val (x \<and> y))" |
  "binary_bool_expr OrNode x y = (bool_to_val (x \<or> y))" |
  "binary_bool_expr XorNode x y = (bool_to_val (x \<noteq> y))" |
  "binary_bool_expr _ _ _ = UndefVal"

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


fun phi_listx :: "Graph \<Rightarrow> ID \<Rightarrow> ID list" where
  "phi_listx g nid = 
    (filter (\<lambda>x.((kind g x)=PhiNode))
      (sorted_list_of_set (usagex g nid)))"

fun input_index :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index g n n' = find_index n' (g_inputs g n)"

fun phi_inputsx :: "Graph \<Rightarrow> nat \<Rightarrow> ID list \<Rightarrow> ID list" where
  "phi_inputsx g i nodes = (map (\<lambda>n. (inp g n)!(i + 1)) nodes)"

fun set_phis :: "ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_phis [] [] m = m" |
  "set_phis (nid # xs) (v # vs) m = (set_phis xs vs (m(nid := v)))" |
  "set_phis [] (v # vs) m = m" |
  "set_phis (x # xs) [] m = m"


inductive
  step :: "Graph \<Rightarrow> (ID \<times> MapState) \<Rightarrow> (ID \<times> MapState) \<Rightarrow> bool" ("_ \<turnstile> _\<mapsto>_" 55) and
  step_top :: "Graph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool" ("_ \<turnstile> _ \<longrightarrow> _" 55) and 
  eval_exp :: "Graph \<Rightarrow>  ID \<times> MapState \<Rightarrow> Value \<Rightarrow> bool" (" _ _\<rightarrow>_" 55) and

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

  ReturnNode:
  "\<lbrakk>kind g nid = ReturnNode;
    g ((inp g nid)!0, m) \<rightarrow> v;
    m' = m(call_nid := v)
    \<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m)#(call_nid,call_m)#xs \<longrightarrow> ((succ g call_nid)!0,m')#xs" |
    
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
  "\<lbrakk>node = kind g nid;
    node \<in> unary_nodes;
    g ((inp g nid)!0, m) \<rightarrow> v\<rbrakk> 
    \<Longrightarrow> g (nid, m) \<rightarrow> (unary_expr node v)" |

  BinaryNode:
  "\<lbrakk>node = kind g nid;
    node \<in> binary_nodes;
    g ((inp g nid)!0, m) \<rightarrow> v1;
    g ((inp g nid)!1, m) \<rightarrow> v2\<rbrakk> 
    \<Longrightarrow> g (nid, m) \<rightarrow> (binary_expr node v1 v2)" |

  IfNode:
  "\<lbrakk>kind g nid = IfNode;
    g ((inp g nid)!0, m) \<rightarrow> (IntVal cond)\<rbrakk>
   \<Longrightarrow> g \<turnstile> (nid, m) \<mapsto> ((succ g nid)!(if val_to_bool cond then 0 else 1), m)" | 

  (* Solution to the eval_all but the evalution gives up :(
   * \<forall> i. i < length inputs \<longrightarrow> (\<exists> s' . (inputs!i \<mapsto> (s',vs!i))); *)
  EndNodes:
  "\<lbrakk>node = kind g nid;
    node \<in> end_nodes;
    kind g merge = MergeNode;

    (inp g merge)!i = nid;

    phis = (phi_listx g merge);
    inputs = (phi_inputsx g i phis);
    g inputs m \<longmapsto> vs;

    m' = (set_phis phis vs m)\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) \<mapsto> (merge, m')" |

  PhiNode:
  "\<lbrakk>kind g nid = PhiNode\<rbrakk>
   \<Longrightarrow>  g (nid, m) \<rightarrow> m nid"


code_pred step .
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

notepad begin 
  have "input_index simple_if_graph 10 5 = 0" by eval
  have "input_index simple_if_graph 10 6 = 1" by eval
  have "input_index simple_if_graph 11 10 = 0" by eval
  have "input_index simple_if_graph 11 9 = 1" by eval
  have "input_index simple_if_graph 11 7 = 2" by eval
  have "input_index simple_if_graph 11 20 = 3" by eval
  have "usage 5 0 simple_if_graph = 10" by eval
  have "usage 6 0 simple_if_graph = 10" by eval
  have "phi_listx simple_if_graph 10 = [11]" by eval
end


(* Currently causes a wellsortedness error which is resolved by removing
 * all IRNode constructors which have parameters e.g (ParameterNode i)
 * Specifically it is unhappy as nat \<Rightarrow> IRNode is not a sort equal
 * cause nat is not of sort enum
 * 
 * export_code eval in Scala module_name Compiler
 *
 * Code generated when removing the offending IRNode constructors is
 * available in the code_gen folder.
 * 
 * Note: "code_pred eval ." is required to generate code equations from
 * inductive rules
 *)

inductive eval_graph :: "Graph \<Rightarrow> ID \<times> MapState \<Rightarrow> ID \<times> MapState \<Rightarrow> bool" where
  "\<lbrakk>g \<turnstile> (nid, m) \<mapsto> (next, m');
    next = 0\<rbrakk> \<Longrightarrow> eval_graph g (nid, m) (next, m')" |

  "\<lbrakk>g \<turnstile> (nid, m) \<mapsto> (next, m');
    next \<noteq> 0;
    eval_graph g (next, m') (next', m'')\<rbrakk> \<Longrightarrow> eval_graph g (nid, m) (next', m'')"

code_pred "eval_graph" .

(* IntVal 10 *)
values "{(n, map m [0]) |n m. double_param_graph (0, StartNode) double_param_map \<mapsto> (n, m)}"
values "{map m [0] |n m. eval_graph double_param_graph (0, StartNode) double_param_map (n, m)}"

(* IntVal 20 *)
values "{(n, map m [0]) |n m. simple_if_graph (0, StartNode) simple_if_map \<mapsto> (n, m)}"
values "{map m [0] |n m. eval_graph simple_if_graph (0, StartNode) simple_if_map (n, m)}"
(* IntVal 120 *)
values "{(n, map m [0]) |n m. simple_if_graph (0, StartNode) (new_map simple_if_graph [IntVal 1, IntVal 20, IntVal 100]) \<mapsto> (n, m)}"
values "{map m [0] |n m. eval_graph simple_if_graph (0, StartNode) (new_map simple_if_graph [IntVal 1, IntVal 20, IntVal 100]) (n, m)}"

end