section \<open>Inductive semantics of nodes\<close>

theory InductiveSemantics
  imports
    "AbsGraph"
    "HOL-Library.Datatype_Records"
    "HOL-Library.LaTeXsugar"
begin

type_synonym field_name = string

datatype Value =
  UndefVal |
  IntVal int

datatype EvalState = 
  EvalState 
    (s_graph: "IRGraph")
    (s_params: "Value list")
    (s_phi: "ID \<Rightarrow> Value")
    (s_flow: "ID \<Rightarrow> nat")

(* Adds the ability to update fields of datatype without making it a record *)
local_setup \<open>Datatype_Records.mk_update_defs \<^type_name>\<open>EvalState\<close>\<close>

type_synonym EvalNode = "ID \<times> IRNode \<times> EvalState"

(* Get the type of node for a node id in an eval state *)
fun get_node :: "ID \<Rightarrow> EvalState \<Rightarrow> IRNode" where
  "get_node n state = ((g_nodes (s_graph state)) n)"

fun get_input :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID" where 
  "get_input n state i = ((g_inputs (s_graph state) n)!i)"

(* Get the nth input edge of a node id in an eval state *)
fun input :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> EvalNode" where
  "input nid state i = 
    (let next_id = (get_input nid state i) in
    (next_id, (get_node next_id state), state))"

fun get_successor :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID" where
  "get_successor n state i = ((g_successors (s_graph state) n)!i)"

(* Get the nth successor edge of a node id in an eval state *)
fun successor :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> EvalNode" where
  "successor nid state i =
    (let next_id = (get_successor nid state 0) in
    (next_id, (get_node next_id state), state))"

fun get_usage :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID" where
  "get_usage nid state i =
    ((sorted_list_of_set (g_usages (s_graph state) nid))!i)"

(* Get the nth usage edge of a node id in an eval state *)
fun usage :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> EvalNode"  where
  "usage nid state i =
    (let use = (get_usage nid state i) in 
    (use, (get_node use state), state))"

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

(*
  ====
  Funtions to filter different types of nodes
  ====
*)
fun is_unary_node :: "IRNode \<Rightarrow> bool" where
  "is_unary_node AbsNode = True" |
  "is_unary_node NegateNode = True" |
  "is_unary_node _ = False"

fun is_binary_node :: "IRNode \<Rightarrow> bool" where
  "is_binary_node AddNode = True" |
  "is_binary_node SubNode = True" |
  "is_binary_node MulNode = True" |
  "is_binary_node AndNode = True" |
  "is_binary_node OrNode = True" |
  "is_binary_node XorNode = True" |
  "is_binary_node IntegerLessThanNode = True" |
  "is_binary_node IntegerEqualsNode = True" |
  "is_binary_node _ = False"

fun is_merge_node :: "IRNode \<Rightarrow> bool" where
  "is_merge_node MergeNode = True" |
  "is_merge_node LoopBeginNode = True" |
  "is_merge_node _ = False"

fun is_end_node :: "IRNode \<Rightarrow> bool" where
  "is_end_node EndNode = True" |
  "is_end_node LoopEndNode = True" |
  "is_end_node _ = False"

fun is_phi_node :: "IRNode \<Rightarrow> bool" where
  "is_phi_node PhiNode = True" |
  "is_phi_node _ = False"

(* 
update_state f a b = f'
in the function f', passing a results in b, passing
any other parameter, x, results in f(x)
*)
fun update_state :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "update_state state ident val = (\<lambda> x. (if x = ident then val else (state x)))"

(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
primrec find_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
"find_index _ [] = 0" |
"find_index P (x#xs) = (if P x then 0 else find_index P xs + 1)"

definition index_list :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"index_list xs = (\<lambda>a. find_index (\<lambda>x. x=a) xs)"


fun phi_list :: "EvalNode \<Rightarrow> EvalNode list" where
  "phi_list (n, node, s) = (if (is_merge_node node)
      then 
        (map (\<lambda>x. (x, (get_node x s), s))
          (filter (\<lambda>x.(is_phi_node (get_node x s)))
            (sorted_list_of_set (g_usages (s_graph s) n))))
      else [])"

fun input_index :: "EvalState \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index s n n' = index_list (g_inputs (s_graph s) n) n'"

fun update_flow :: "EvalState \<Rightarrow> ID \<Rightarrow> nat \<Rightarrow> EvalState" where
  "update_flow s p i = (let preds = (s_flow s) in
    (update_s_flow (\<lambda>_. (update_state preds p i)) s))"

fun phi_input :: "EvalNode \<Rightarrow> EvalNode" where
  "phi_input (n, node, s) = (
    let merge = (get_input n s 0) in (
    let i = ((s_flow s) merge) in
    let input = (get_input n s (i + 1)) in
    (input, (get_node input s), s)))"

fun phi_input_list :: "EvalNode list \<Rightarrow> EvalNode list" where
  "phi_input_list nodes = (map (\<lambda>x. (phi_input x)) nodes)"

fun update_phi :: "EvalState \<Rightarrow> ID \<Rightarrow> Value \<Rightarrow> EvalState" where
  "update_phi s n v = (update_s_phi (\<lambda>_. (update_state (s_phi s) n v)) s)"

fun set_phis :: "EvalState \<Rightarrow> EvalNode list \<Rightarrow> Value list \<Rightarrow> EvalState" where
  "set_phis s [] [] = s" |
  "set_phis s ((x, _, _) # xs) (v # vs) = (set_phis (update_phi s x v) xs vs)" |
  "set_phis s [] (v # vs) = s" |
  "set_phis s (x # xs) [] = s"

inductive
  eval :: "EvalNode \<Rightarrow> EvalState \<times> Value \<Rightarrow> bool" ("_\<mapsto>_" 55) and
  eval_all :: "EvalNode list \<Rightarrow> Value list \<Rightarrow> bool" ("_\<longmapsto>_" 55)
  where


  "[] \<longmapsto> []" |
  "\<lbrakk>x \<mapsto> (s', v); xs \<longmapsto> vs\<rbrakk> \<Longrightarrow> (x # xs) \<longmapsto> (v # vs)" |


  StartNode: "\<lbrakk>(successor num s 0) \<mapsto> succ\<rbrakk> 
              \<Longrightarrow> (num, StartNode, s) \<mapsto> succ" |

  ParameterNode: "(num, (ParameterNode i), s) \<mapsto> (s, ((s_params s)!(nat i)))" |

  ConstantNode: "(num, (ConstantNode c), s) \<mapsto> (s, (IntVal c))" |

  UnaryNode: "\<lbrakk>is_unary_node node;
              (input num s 0) \<mapsto> (s1, v1)\<rbrakk> 
              \<Longrightarrow> (num, node, s) \<mapsto> (s1, (unary_expr node v1))" |

  BinaryNode: "\<lbrakk>is_binary_node node;
                (input num s 0) \<mapsto> (s1, v1);
                (input num s1 1) \<mapsto> (s2, v2)\<rbrakk> 
                \<Longrightarrow> (num, node, s) \<mapsto> (s2, (binary_expr node v1 v2))" |

  IfNodeTrue: "\<lbrakk>(input num s 0) \<mapsto> (s1, v1);
                (val_to_bool v1);
                (successor num s1 0) \<mapsto> s2\<rbrakk> 
                \<Longrightarrow> (num, IfNode, s) \<mapsto> s2" |

  IfNodeFalse: "\<lbrakk>(input num s 0) \<mapsto> (s1, v1);
                 (\<not>(val_to_bool v1));
                 (successor num s1 1) \<mapsto> s2\<rbrakk> 
                 \<Longrightarrow> (num, IfNode, s) \<mapsto> s2" |

  ReturnNode: "\<lbrakk>(input n s 0) \<mapsto> (s1, v1)\<rbrakk> 
                \<Longrightarrow> (n, ReturnNode, s) \<mapsto> (s1, v1)" |

(* WIP *)
  
  (* Solution to the eval_all but the evalution gives up :(
   * \<forall> i. i < length inputs \<longrightarrow> (\<exists> s' . (inputs!i \<mapsto> (s',vs!i))); *)
  MergeNodes: "\<lbrakk>is_merge_node node;
                phis = (phi_list (n, node, s));
                inputs = (phi_input_list phis);
                inputs \<longmapsto> vs;
                (successor n (set_phis s phis vs)  0) \<mapsto> succ\<rbrakk> 
                \<Longrightarrow> (n, node, s) \<mapsto> succ" |


  EndNodes: "\<lbrakk>is_end_node node;
              (merge, merge_node, _) = (usage n s 0);
              i = (input_index s merge n);
              s' = (update_flow s merge i);
              (merge, merge_node, s') \<mapsto> succ\<rbrakk> 
              \<Longrightarrow> (n, node, s) \<mapsto> succ" |


  PhiNode: "(n, PhiNode, s) \<mapsto> (s, (s_phi s) n)" |

  BeginNode: "\<lbrakk>(successor n s 0) \<mapsto> succ\<rbrakk>
               \<Longrightarrow> (n, BeginNode, s) \<mapsto> succ"


instance IRNode :: equal by standard

code_pred eval .
code_pred eval_all .


(* Example graph evaluation *)
fun new_state :: "IRGraph \<Rightarrow> Value list \<Rightarrow> EvalState" where
  "new_state graph params = (EvalState graph params (\<lambda> x. UndefVal) (\<lambda> x. 0))"

definition ex_graph :: IRGraph where
  "ex_graph =
    (add_node 3 ReturnNode [2] []
    (add_node 2 AddNode [1, 1] []
    (add_node 1 (ParameterNode 0) [] []
    (add_node 0 StartNode [] [3]
    empty_graph))))"
lemma "wff_graph ex_graph"
  unfolding ex_graph_def by simp

definition ex_graph2 :: IRGraph where
  "ex_graph2 =
    (add_node 5 ReturnNode [1] []
    (add_node 4 ReturnNode [2] []
    (add_node 3 IfNode [1] [4, 5]
    (add_node 2 (ConstantNode 30) [] []
    (add_node 1 (ConstantNode 1) [] []
    (add_node 0 StartNode [] [3]
    empty_graph))))))"
lemma "wff_graph ex_graph2"
  unfolding ex_graph2_def by simp

definition eg3 :: IRGraph where
  "eg3 =
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
lemma "wff_graph eg3"
  unfolding eg3_def by simp

notepad begin 
  have "input_index (new_state eg3 []) 10 5 = 0" by eval
  have "input_index (new_state eg3 []) 10 6 = 1" by eval
  have "(s_flow (update_flow (new_state eg3 []) 10 0)) 10 = 0" by eval
  have "(s_flow (update_flow (new_state eg3 []) 10 1)) 10 = 1" by eval
  have "input_index (new_state eg3 []) 11 10 = 0" by eval
  have "input_index (new_state eg3 []) 11 9 = 1" by eval
  have "input_index (new_state eg3 []) 11 7 = 2" by eval
  have "input_index (new_state eg3 []) 11 20 = 3" by eval
end

value "phi_input (11, PhiNode, (new_state eg3 []))"
value "phi_input (11, PhiNode, (update_flow (new_state eg3 []) 10 0))"
value "phi_input (11, PhiNode, (update_flow (new_state eg3 []) 10 1))"

value "usage 5 (new_state eg3 []) 0" (* (10, MergeNode, ...) *)
value "usage 6 (new_state eg3 []) 0" (* (10, MergeNode, ...) *)

value "phi_list (10, MergeNode, (new_state eg3 []))" (* [(11, PhiNode, ...)] *)

definition eg4 :: IRGraph where
  "eg4 =
    (add_node 14 (ParameterNode 0) [] []
    (add_node 13 ReturnNode [2] []
    (add_node 12 EndNode [] [13]
    (add_node 11 BeginNode [] [12]
    (add_node 10 LoopEndNode [7] []
    (add_node 9 BeginNode [] [10]
    (add_node 8 IfNode [3] [9,11]
    (add_node 7 LoopBeginNode [1] [8]
    (add_node 6 (ConstantNode 4) [] []
    (add_node 5 (ConstantNode 0) [] []
    (add_node 4 AddNode [2,6] []
    (add_node 3 IntegerLessThanNode [2,14] []
    (add_node 2 PhiNode [7,5,4] [] 
    (add_node 1 EndNode [] []
    (add_node 0 StartNode [] [1]
    empty_graph)))))))))))))))"

datatype GraphBuilder = 
  GraphBuilder |
  AddNode (gb_node_id: "nat") (gb_graph: "IRGraph")

fun build :: "GraphBuilder \<Rightarrow> IRNode \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> GraphBuilder" ("_ _ _ _;")
  where
  "build GraphBuilder n i s = AddNode 0 (add_node 0 n i s empty_graph)" |
  "build (AddNode nid graph) n i s = (AddNode (nid + 1) (add_node (nid + 1) n i s graph))"

fun unpack :: "GraphBuilder \<Rightarrow> IRGraph" where
  "unpack GraphBuilder = empty_graph" |
  "unpack (AddNode nid graph) = graph"

definition ex_graph3 :: IRGraph where
  "ex_graph3 =            
  unpack
  (GraphBuilder
    StartNode [] [3];
    (ConstantNode 1) [] [];
    (ConstantNode 30) [] [];
    IfNode [1] [4, 5];
    ReturnNode [2] [];
    ReturnNode [1] [];)
  "

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

values "{(s, v). (0, StartNode, (new_state ex_graph [IntVal 5])) \<mapsto> (s, v)}"

values "{(s, v). (0, StartNode, (new_state ex_graph2 [])) \<mapsto> (s, v)}"

values "{(s, v). (0, StartNode, (new_state ex_graph3 [])) \<mapsto> (s, v)}"

values "{(s, v). (0, StartNode, (new_state eg3 [IntVal 0, IntVal 20, IntVal 100])) \<mapsto> (s, v)}"

export_code eval in SML

values "{(s, v). (0, StartNode, (new_state eg4 [IntVal 0, IntVal 20, IntVal 100])) \<mapsto> (s, v)}"

end