section \<open>Inductive semantics of nodes\<close>

theory InductiveSemantics
  imports
    "AbsGraph"
    "HOL-Library.Datatype_Records"
    "HOL-Library.LaTeXsugar"
begin

datatype Value =
  UndefVal |
  IntVal int

datatype EvalState = 
  EvalState 
    (s_graph: "IRGraph")
    (s_params: "Value list")
    (s_phi: "ID \<Rightarrow> Value")

type_synonym MapState = "ID \<Rightarrow> Value"

(* Adds the ability to update fields of datatype without making it a record *)
local_setup \<open>Datatype_Records.mk_update_defs \<^type_name>\<open>EvalState\<close>\<close>

type_synonym EvalNode = "ID \<times> IRNode \<times> EvalState"

(* Get the type of node for a node id in an eval state *)
fun get_node :: "ID \<Rightarrow> EvalState \<Rightarrow> IRNode" where
  "get_node nid s = ((g_nodes (s_graph s)) nid)"

fun to_eval_node :: "ID \<Rightarrow> EvalState \<Rightarrow> EvalNode" where
  "to_eval_node nid s = (nid, (get_node nid s), s)"

fun to_eval_node_new :: "ID \<Rightarrow> EvalState \<Rightarrow> (ID \<times> IRNode)" where
  "to_eval_node_new nid s = (nid, (get_node nid s))"

fun get_input :: "ID \<Rightarrow> nat \<Rightarrow> EvalState \<Rightarrow> ID" where 
  "get_input nid i s = ((g_inputs (s_graph s) nid)!i)"
fun input :: "ID \<Rightarrow> nat \<Rightarrow> EvalState \<Rightarrow> ID \<times> IRNode" where
  "input nid i s = (to_eval_node_new (get_input nid i s) s)"

fun get_successor :: "ID \<Rightarrow> nat \<Rightarrow> EvalState \<Rightarrow> ID" where
  "get_successor nid i s = ((g_successors (s_graph s) nid)!i)"
fun successor :: "ID \<Rightarrow> nat \<Rightarrow> EvalState \<Rightarrow> ID \<times> IRNode" where
  "successor nid i s = (to_eval_node_new (get_successor nid i s) s)"

fun get_usage :: "ID \<Rightarrow> nat \<Rightarrow> EvalState \<Rightarrow> ID" where
  "get_usage nid i s =
    ((sorted_list_of_set (g_usages (s_graph s) nid))!i)"
fun usage :: "ID \<Rightarrow> nat \<Rightarrow> EvalState \<Rightarrow> EvalNode"  where
  "usage nid i s = (to_eval_node (get_usage nid i s) s)"

(*
   ====
   Functions to aid evaluating expressions
   ====
*)
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
  "binary_bool_expr XorNode x y = (bool_to_val ((x \<or> y) \<and> \<not>(x \<and> y)))" |
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


fun phi_list :: "EvalNode \<Rightarrow> EvalNode list" where
  "phi_list (n, node, s) = 
      (map (\<lambda>x. (x, (get_node x s), s))
        (filter (\<lambda>x.((get_node x s)=PhiNode))
          (sorted_list_of_set (g_usages (s_graph s) n))))"

fun input_index :: "EvalState \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index s n n' = find_index n' (g_inputs (s_graph s) n)"

(* TODO: Deprecate *)
fun get_input_old :: "ID \<Rightarrow> nat \<Rightarrow> EvalState \<Rightarrow> ID" where 
  "get_input_old nid i s = ((g_inputs (s_graph s) nid)!i)"
fun input_old :: "ID \<Rightarrow> nat \<Rightarrow> EvalState \<Rightarrow> ID \<times> IRNode \<times> EvalState" where
  "input_old nid i s = (to_eval_node (get_input nid i s) s)"

fun phi_inputs :: "nat \<Rightarrow> EvalState \<Rightarrow> EvalNode list \<Rightarrow> EvalNode list" where
  "phi_inputs i s nodes = (map (\<lambda>(n, _, s). (input_old n (i + 1) s)) nodes)"

fun set_phis :: "MapState \<Rightarrow> EvalNode list \<Rightarrow> Value list \<Rightarrow> MapState" where
  "set_phis m [] [] = m" |
  "set_phis m ((x, _, _) # xs) (v # vs) = (set_phis (m(x := v)) xs vs)" |
  "set_phis m [] (v # vs) = m" |
  "set_phis m (x # xs) [] = m"

inductive
  eval :: "EvalState \<Rightarrow> ID \<times> IRNode \<Rightarrow> MapState \<Rightarrow> MapState \<times> Value \<Rightarrow> bool" ("_ _ _\<mapsto>_" 55) and
  eval_exp :: "EvalState \<Rightarrow> MapState \<Rightarrow> ID \<times> IRNode \<Rightarrow> Value \<Rightarrow> bool" ("_ _ _\<rightarrow>_" 55) and
  eval_all :: "EvalState \<Rightarrow> EvalNode list \<Rightarrow> MapState \<Rightarrow> Value list \<Rightarrow> bool" ("_ _ _\<longmapsto>_" 55)
  for g
  where


  "g [] m \<longmapsto> []" |
  "\<lbrakk>g m (nid, node) \<rightarrow> v; g xs m \<longmapsto> vs\<rbrakk> \<Longrightarrow> g ((nid, node, _) # xs) m \<longmapsto> (v # vs)" |


  StartNode:
  "\<lbrakk>g (successor nid 0 g) m \<mapsto> succ\<rbrakk> 
    \<Longrightarrow> g (nid, StartNode) m \<mapsto> succ" |

  BeginNode: 
  "\<lbrakk>g (successor nid 0 g) m \<mapsto> succ\<rbrakk>
    \<Longrightarrow> g (nid, BeginNode) m \<mapsto> succ" |

  MergeNodes:
  "\<lbrakk>node \<in> merge_nodes;
    g (successor nid 0 g) m \<mapsto> succ\<rbrakk> 
    \<Longrightarrow> g (nid, node) m \<mapsto> succ" |

  ParameterNode:
  "g m (nid, (ParameterNode i)) \<rightarrow> (m nid)" |

  ConstantNode:
  "g m (nid, (ConstantNode c)) \<rightarrow> (IntVal c)" |

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
    (val_to_bool cond);
    g (successor nid 0 g) m \<mapsto> m'\<rbrakk> 
    \<Longrightarrow> g (nid, IfNode) m \<mapsto> m'" |

  IfNodeFalse:
  "\<lbrakk>g m (input nid 0 g) \<rightarrow> cond;
    (\<not>(val_to_bool cond));
    g (successor nid 1 g) m \<mapsto> m'\<rbrakk> 
    \<Longrightarrow> g (nid, IfNode) m \<mapsto> m'" |

  ReturnNode:
  "\<lbrakk>g m (input nid 0 g) \<rightarrow> v\<rbrakk> 
    \<Longrightarrow> g (nid, ReturnNode) m \<mapsto> (m, v)" |
 

  (* Solution to the eval_all but the evalution gives up :(
   * \<forall> i. i < length inputs \<longrightarrow> (\<exists> s' . (inputs!i \<mapsto> (s',vs!i))); *)
  EndNodes:
  "\<lbrakk>node \<in> end_nodes;

    (merge, merge_node, _) = (usage nid 0 g);
    i = (input_index g merge nid);

    phis = (phi_list (merge, merge_node, g));
    inputs = (phi_inputs i g phis);
    g inputs m \<longmapsto> vs;

    m' = (set_phis m phis vs);

    g (merge, merge_node) m' \<mapsto> succ\<rbrakk> 
    \<Longrightarrow> g (nid, node) m \<mapsto> succ" |

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

fun new_state :: "IRGraph \<Rightarrow> MapState \<Rightarrow> EvalState" where
  "new_state graph m = (EvalState graph [] m)"

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

definition double_param_state :: "EvalState" where
  "double_param_state = new_state double_param_graph double_param_map"

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

definition simple_if_state :: "EvalState" where
  "simple_if_state = new_state simple_if_graph simple_if_map"

notepad begin 
  have "input_index simple_if_state 10 5 = 0" by eval
  have "input_index simple_if_state 10 6 = 1" by eval
  have "input_index simple_if_state 11 10 = 0" by eval
  have "input_index simple_if_state 11 9 = 1" by eval
  have "input_index simple_if_state 11 7 = 2" by eval
  have "input_index simple_if_state 11 20 = 3" by eval
end

value "usage 5 0 simple_if_state" (* (10, MergeNode, ...) *)
value "usage 6 0 simple_if_state" (* (10, MergeNode, ...) *)

value "phi_list (10, MergeNode, simple_if_state)" (* [(11, PhiNode, ...)] *)


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

definition initial_mapping :: "ID \<Rightarrow> Value" where
  "initial_mapping = (\<lambda> x . UndefVal)"

(* IntVal 10 *)
values "{(s, v). double_param_state (0, StartNode) double_param_map \<mapsto> (s, v)}"

(* IntVal 20 *)
values "{(s, v). simple_if_state (0, StartNode) simple_if_map \<mapsto> (s, v)}"
(* IntVal 120 *)
values "{(s, v). simple_if_state (0, StartNode) (new_map simple_if_graph [IntVal 1, IntVal 20, IntVal 100])  \<mapsto> (s, v)}"

end