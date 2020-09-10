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

fun get_graph_node :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRNode" where
  "get_graph_node nid g = (g_nodes g) nid"

fun to_node_pair :: "ID \<Rightarrow> IRGraph \<Rightarrow> (ID \<times> IRNode)" where
  "to_node_pair nid g = (nid, (get_graph_node nid g))"

fun get_input :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> ID" where 
  "get_input nid i g = ((g_inputs g nid)!i)"
fun input :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> (ID \<times> IRNode)" where
  "input nid i g = (to_node_pair (get_input nid i g) g)"

fun get_successor :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> ID" where
  "get_successor nid i g = ((g_successors g nid)!i)"
fun successor :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> ID \<times> IRNode" where
  "successor nid i g = (to_node_pair (get_successor nid i g) g)"

fun get_usage :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> ID" where
  "get_usage nid i g =
    ((sorted_list_of_set (g_usages g nid))!i)"
fun usage :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> ID \<times> IRNode"  where
  "usage nid i g = (to_node_pair (get_usage nid i g) g)"



fun val_to_bool :: "Value \<Rightarrow> bool" where
  "val_to_bool (IntVal x) = (if x = 0 then False else True)" |
  "val_to_bool (UndefVal) = False"

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal 1)" |
  "bool_to_val False = (IntVal 0)"

fun unary_expr :: "IRNode \<Rightarrow> Value \<Rightarrow> Value" where
  "unary_expr AbsNode (IntVal x) = (IntVal (if (x < 0) then -x else x))" |
  "unary_expr NegateNode x = (bool_to_val (\<not>(val_to_bool x)))" |
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
  "binary_expr AndNode x y = (binary_bool_expr AddNode (val_to_bool x) (val_to_bool y))" |
  "binary_expr OrNode x y = (binary_bool_expr OrNode (val_to_bool x) (val_to_bool y))" |
  "binary_expr XorNode x y = (binary_bool_expr XorNode (val_to_bool x) (val_to_bool y))" |
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


fun phi_list :: "ID \<Rightarrow> IRGraph \<Rightarrow> ID list" where
  "phi_list nid g = 
    (filter (\<lambda>x.((get_graph_node x g)=PhiNode))
      (sorted_list_of_set (g_usages g nid)))"

fun input_index :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index g n n' = find_index n' (g_inputs g n)"

fun phi_inputs :: "nat \<Rightarrow> IRGraph \<Rightarrow> ID list \<Rightarrow> (ID \<times> IRNode) list" where
  "phi_inputs i g nodes = (map (\<lambda>n. (input n (i + 1) g)) nodes)"

fun set_phis :: "ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_phis [] [] m = m" |
  "set_phis (nid # xs) (v # vs) m = (set_phis xs vs (m(nid := v)))" |
  "set_phis [] (v # vs) m = m" |
  "set_phis (x # xs) [] m = m"


inductive
  eval :: "IRGraph \<Rightarrow> ID \<times> IRNode \<Rightarrow> MapState \<Rightarrow> ID \<times> MapState \<Rightarrow> bool" ("_ _ _\<mapsto>_" 55) and
  eval_exp :: "IRGraph \<Rightarrow> MapState \<Rightarrow> ID \<times> IRNode \<Rightarrow> Value \<Rightarrow> bool" ("_ _ _\<rightarrow>_" 55) and
  eval_all :: "IRGraph \<Rightarrow> (ID \<times> IRNode) list \<Rightarrow> MapState \<Rightarrow> Value list \<Rightarrow> bool" ("_ _ _\<longmapsto>_" 55)
  for g
  where


  "g [] m \<longmapsto> []" |
  "\<lbrakk>g m (nid, node) \<rightarrow> v; g xs m \<longmapsto> vs\<rbrakk> \<Longrightarrow> g ((nid, node) # xs) m \<longmapsto> (v # vs)" |


  StartNode:
  "g (nid, StartNode) m \<mapsto> ((get_successor nid 0 g), m)" |

  BeginNode: 
  "g (nid, BeginNode) m \<mapsto> ((get_successor nid 0 g), m)" |

  MergeNodes:
  "\<lbrakk>node \<in> merge_nodes\<rbrakk> 
    \<Longrightarrow> g (nid, node) m \<mapsto> ((get_successor nid 0 g), m)" |

  ParameterNode:
  "g m (nid, (ParameterNode i)) \<rightarrow> (m nid)" |

  ConstantNode:
  "g m (nid, (ConstantNode c)) \<rightarrow> (IntVal (word_of_int c))" |

  UnaryNode:
  "\<lbrakk>node \<in> unary_nodes;
    g m (input nid 0 g) \<rightarrow> v\<rbrakk> 
    \<Longrightarrow> g m (nid, node) \<rightarrow> (unary_expr node v)" |

  BinaryNode:
  "\<lbrakk>node \<in> binary_nodes;
    g m (input nid 0 g) \<rightarrow> v1;
    g m (input nid 1 g) \<rightarrow> v2\<rbrakk> 
    \<Longrightarrow> g m (nid, node) \<rightarrow> (binary_expr node v1 v2)" |

  IfNodeTrue:
  "\<lbrakk>g m (input nid 0 g) \<rightarrow> cond;
    (val_to_bool cond)\<rbrakk> 
    \<Longrightarrow> g (nid, IfNode) m \<mapsto> ((get_successor nid 0 g), m)" |

  IfNodeFalse:
  "\<lbrakk>g m (input nid 0 g) \<rightarrow> cond;
    (\<not>(val_to_bool cond))\<rbrakk> 
    \<Longrightarrow> g (nid, IfNode) m \<mapsto> ((get_successor nid 1 g), m)" |

  ReturnNode:
  "\<lbrakk>g m (input nid 0 g) \<rightarrow> v\<rbrakk> 
    \<Longrightarrow> g (nid, ReturnNode) m \<mapsto> (0, m(0 := v))" |
 

  (* Solution to the eval_all but the evalution gives up :(
   * \<forall> i. i < length inputs \<longrightarrow> (\<exists> s' . (inputs!i \<mapsto> (s',vs!i))); *)
  EndNodes:
  "\<lbrakk>node \<in> end_nodes;

    (merge, merge_node) = (usage nid 0 g);
    i = (input_index g merge nid);

    phis = (phi_list merge g);
    inputs = (phi_inputs i g phis);
    g inputs m \<longmapsto> vs;

    m' = (set_phis phis vs m)\<rbrakk> 
    \<Longrightarrow> g (nid, node) m \<mapsto> (merge, m')" |

  PhiNode:
  "g m (nid, PhiNode) \<rightarrow> m nid"


code_pred eval .
code_pred eval_all .


(* Example graph evaluation *)
fun new_map_i :: "IRGraph \<Rightarrow> Value list \<Rightarrow> ID list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "new_map_i g ps [] m = m" |
  "new_map_i g ps (nid # xs) m = (let m' = (new_map_i g ps xs m) in 
   (case ((g_nodes g) nid) of 
    (ParameterNode i) \<Rightarrow> m'(nid := (ps!(nat i))) |
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
  have "usage 5 0 simple_if_graph = (10, MergeNode)" by eval
  have "usage 6 0 simple_if_graph = (10, MergeNode)" by eval
  have "phi_list 10 simple_if_graph = [11]" by eval
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

inductive eval_graph :: "IRGraph \<Rightarrow> ID \<times> IRNode \<Rightarrow> MapState \<Rightarrow> ID \<times> MapState \<Rightarrow> bool" where
  "\<lbrakk>g node m \<mapsto> (next, m');
    next = 0\<rbrakk> \<Longrightarrow> eval_graph g node m (next, m')" |

  "\<lbrakk>g node m \<mapsto> (next, m');
    next \<noteq> 0;
    eval_graph g (next, get_graph_node next g) m' (next', m'')\<rbrakk> \<Longrightarrow> eval_graph g node m (next', m'')"

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