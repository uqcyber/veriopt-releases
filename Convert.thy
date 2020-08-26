theory Convert 
  imports
    AbsGraph 
    (*IRSemantics*)
    "exprs/CodeGen"
begin

type_synonym GraphNode = "(ID \<times> IRNode)"
type_synonym ConvertedGraphNode = "(ID \<times> Node)"

fun graph_nodes :: "IRGraph \<Rightarrow> GraphNode list" where
  "graph_nodes graph = 
    map (\<lambda>id.(id, (g_nodes graph)id)) (sorted_list_of_set (g_ids graph))"

fun replace_node :: "ID \<Rightarrow> ID \<Rightarrow> IRNode \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "replace_node oldId newId node graph = 
    (update_edges oldId newId (add_node newId node [] [] graph))"

fun input :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> ID" where
  "input n i graph = (nth ((g_inputs graph) n) i)"

function
  tree_node_to_graph :: "IRNode \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> Node" and
  convert :: "ID \<Rightarrow> IRGraph \<Rightarrow> Node" ("* _ _" 500)
  where
  "convert n graph = tree_node_to_graph ((g_nodes graph) n) n graph" |

  "tree_node_to_graph AddNode n graph = 
    (BinaryNode AddOp (* (input n 0 graph) graph) (* (input n 1 graph) graph))" |
  "tree_node_to_graph SubNode n graph = 
    (BinaryNode SubOp (* (input n 0 graph) graph) (* (input n 1 graph) graph))" |
  "tree_node_to_graph MulNode n graph = 
    (BinaryNode MulOp (* (input n 0 graph) graph) (* (input n 1 graph) graph))" |
  "tree_node_to_graph AndNode n graph = 
    (BinaryNode AndOp (* (input n 0 graph) graph) (* (input n 1 graph) graph))" |
  "tree_node_to_graph OrNode n graph = 
    (BinaryNode OrOp (* (input n 0 graph) graph) (* (input n 1 graph) graph))" |  
  "tree_node_to_graph XorNode n graph = 
    (BinaryNode XorOp (* (input n 0 graph) graph) (* (input n 1 graph) graph))" |
 
  "tree_node_to_graph (ConstantNode v) n graph =
    (ConstNode (IntegerValue (word_of_int v)))" |

  (* this is likely an incorrect conversion but aids for now *)
  "tree_node_to_graph (ParameterNode v) n graph =
    (ConstNode (IntegerValue (word_of_int v)))" |

  "tree_node_to_graph _ n graph =
    (ConstNode (UndefinedValue))"
  sorry
termination
  sorry

fun convertable_node :: "GraphNode \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "convertable_node (n, node) graph = ((convert n graph) \<noteq> (ConstNode UndefinedValue))"

fun convertable_nodes :: "IRGraph \<Rightarrow> GraphNode list" where
  "convertable_nodes graph = 
    (let nodes = (graph_nodes graph) in 
    (filter (\<lambda>x.(convertable_node x graph)) nodes))"

fun convert_nodes :: "IRGraph \<Rightarrow> ConvertedGraphNode list" where
  "convert_nodes graph = 
    (map (\<lambda>(n,node).(n,(convert n graph))) (convertable_nodes graph))"

fun canonical :: "IRGraph \<Rightarrow> IRGraph" where
  "canonical graph = graph"

definition ex_graph :: IRGraph where
  "ex_graph =
    (add_node 3 ReturnNode [2] []
    (add_node 2 AddNode [1, 1] []
    (add_node 1 (ParameterNode 5) [] []
    (add_node 0 StartNode [] [2]
    empty_graph))))"
lemma "wff_graph ex_graph"
  unfolding ex_graph_def by simp

value "map (\<lambda>(n,node) . node) (convert_nodes ex_graph)"
value "map (\<lambda>(n,node) . (Rewrite.rewrite node)) (convert_nodes ex_graph)"

end