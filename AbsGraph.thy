theory AbsGraph 
imports GraalIR1_fromID
begin

(*
datatype IRGraph =
  Graph
    (g_ids: "ID set")
    (g_nodes: "ID \<Rightarrow> IRNode")
    (g_inputs: "InputEdges")
    (g_successors: "SuccessorEdges")
*)
definition empty_graph :: IRGraph where
  "empty_graph =  (Graph {0} (\<lambda>i.(StartNode)) (\<lambda>i.[]) (\<lambda>i.[]))"

lemma empty0 [simp]: "i \<in> g_ids empty_graph = (i = 0)"
  unfolding empty_graph_def
    by auto

(* Simplification rules for empty_graph. *)
lemma empty_ids [simp]: "g_ids empty_graph = {0}"
  by auto
lemma empty_nodes [simp]: "g_nodes empty_graph = (\<lambda>i.(StartNode))"
  by (simp add: empty_graph_def)
lemma empty_inputs [simp]: "g_inputs empty_graph = (\<lambda>i.[])"
  by (simp add: empty_graph_def)
lemma empty_succs [simp]: "g_successors empty_graph = (\<lambda>i.[])"
  by (simp add: empty_graph_def)


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
      ((g_nodes g)(i := node))
      ((g_inputs g)(i := ins))
      ((g_successors g)(i := sucs))
  )"

(* Remove one node from a graph, mapping any refs to a given ID. *)
fun del_node :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "del_node n g = (Graph
      (g_ids g - {n} \<union> {0})
      ((g_nodes g)(n := StartNode))
      ((g_inputs g)(n := []))
      ((g_successors g)(n := []))
  )"

fun g_predecessor :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "g_predecessor (Graph ids nodes inputs successors) n = {i. n \<in> set(successors i)}"

(* update some input/successor edges to point to a new node. *)
fun update_edges :: "ID \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "update_edges oldID newID (Graph ids nodes inputs succs) =
    (let old2new = (\<lambda>i. if i=oldID then newID else i) in
      (Graph ids nodes (\<lambda>n. map old2new (inputs n)) (\<lambda>n. (map old2new (succs n)))))"

(* Deleting a freshly-added node (that does not reuse an existing ID)
   leaves the graph unchanged.
   NOTE: this was surprisingly hard to prove - should have been trivial?
         Especially, Isabelle seemed to struggle more when this used selectors.
*)
theorem del_add:
  fixes d n i s node inputs succs
  assumes wff: "wff_graph (Graph d ns i s)"
  assumes fresh: "n \<notin> d" (* g_ids (Graph d ns i s)" *)
  shows "del_node n (add_node n node inputs succs (Graph d ns i s)) = (Graph d ns i s)"
proof -
  have 0: "0 \<in> d" using wff wff_graph.simps by simp
  then have "n \<noteq> 0" using wff fresh by meson
  have ns: "ns n = StartNode" using wff fresh by simp
    (* harder with selectors: by (metis IRGraph.exhaust IRGraph.sel(1) IRGraph.sel(2) wff_graph.simps) *)
  have i: "i n = []" using wff fresh by simp
  have s: "s n = []" using wff fresh by simp
  then show ?thesis using wff fresh 0 ns i s by auto
qed


(* Example 2:
  =============================================
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
    (add_node 0 StartNode [] [5]
    empty_graph))))"

lemma eg2node: "(g_nodes empty_graph)
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
  done

lemma "del_node 0 (del_node 1 (del_node 4 (del_node 5 eg2_abs))) = empty_graph"
  unfolding eg2_abs_def eg2_sq_def empty_graph_def
  apply (simp add: del_add fun_upd_idem)
  (* This left just: insert 0 ({0, 4, Suc 0, 0} - {4}) - {Suc 0} \<subseteq> {0}.
     Why didn't simp deal with this ground term?
     Answer: it needs an extra simp rule like: 
         Set.Diff_subset_conv: (?A - ?B \<subseteq> ?C) = (?A \<subseteq> ?B \<union> ?C)
     or (more general): 
         Set.insert_Diff_if: insert ?x ?A - ?B = (if ?x \<in> ?B then ?A - ?B else insert ?x (?A - ?B))
  *)
  by (simp add: insert_Diff_if)


lemma "(insert 0 ({0, 4, Suc 0, 0} - {4})) - {Suc 0} \<subseteq> {0}"
  by (simp add: insert_Diff_if)

value "g_inputs eg2_abs 4"

(* Test the update_edges function. *)
lemma "g_inputs (update_edges 1 999 eg2_abs) 4 = [999, 999]"
  unfolding eg2_abs_def
  apply (simp add: Let_def)
  done

lemma "g_successors (update_edges 5 999 eg2_abs) 0 = [999]"
  unfolding eg2_abs_def
  apply (simp add: Let_def)
  done

end
