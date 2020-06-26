theory AbsGraph 
imports GraalIR1_fromID
begin

(*
datatype IRGraph =
  Graph
    (g_ids: "ID set")
    (g_node: "ID \<Rightarrow> IRNode")
    (g_inputs: "InputEdges")
    (g_successors: "SuccessorEdges")
*)
definition empty_graph :: IRGraph where
  "empty_graph =  (Graph {0} (\<lambda>i.(StartNode)) (\<lambda>i.[]) (\<lambda>i.[]))"

lemma empty0 [simp]: "i \<in> g_ids empty_graph = (i = 0)"
  unfolding empty_graph_def
    by auto

(* Get next free ID. *)
fun next_id :: "IRGraph \<Rightarrow> nat" where
  "next_id graph =  Max(g_ids graph) + 1"

(* Get next n free IDs. *)
fun next_ids :: "IRGraph \<Rightarrow> nat \<Rightarrow> nat list" where
  "next_ids graph n = (let next = next_id graph in [next ..< next + n])"

(* Extend a graph by adding one node to it. *)
fun add_node :: "ID \<Rightarrow> IRNode \<Rightarrow> ID list \<Rightarrow> ID list \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "add_node i node ins sucs g = (Graph
      (g_ids g \<union> {i})
      ((g_node g)(i := node))
      ((g_inputs g)(i := ins))
      ((g_successors g)(i := sucs))
  )"

(* Example 2:
  public static int sq(int x) { return x * x; }

             [1 P(0)]
               \ /
  [0 Start]   [4 *]
       |      /
       V     /
      [5 Return]
*)
definition eg2_abs :: IRGraph where
  "eg2_abs =
    (add_node 5 ReturnNode [4] []
    (add_node 4 MulNode [1, 1] []
    (add_node 1 (ParameterNode 0) [] []
    (add_node 0 StartNode [] [0]
    empty_graph))))"

lemma eg2node: "(g_node empty_graph)
    (Suc 0 := ParameterNode 0,
     4 := MulNode,
     5 := ReturnNode) = eg2_node" 
  unfolding fun_upd_apply
  apply (simp only: fun_eq_iff)
  unfolding empty_graph_def
  apply auto
  done

lemma eq2: "eg2_abs = eg2_sq"
  unfolding eg2_abs_def eg2_sq_def empty_graph_def
  apply auto
  
end
