section \<open>GraalVM graph representation\<close>

theory IRGraph
  imports 
    IRNodes
    "HOL-Library.Finite_Map"
    "HOL.Relation"
begin

(* This theory defines the main Graal data structure - an entire IR Graph. *)
text_raw \<open>\snip{graphdef}{\<close>
type_synonym IRGraph = "(ID, IRNode) fmap"
text_raw \<open>}%endsnip\<close>

(* Get ALL the IDs in the graph. *)
fun graph_nodes :: "IRGraph \<Rightarrow> ID set" where
  "graph_nodes g = fset (fmdom g)"

(* Look up a given ID in the graph and return the whole node. *)
fun kind :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRNode" where
  "kind g nid = (case fmlookup g nid of Some n \<Rightarrow> n | None \<Rightarrow> NoNode)"

(* Get the inputs list of a given node ID. *)
fun inp :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "inp g nid = inputs_of(kind g nid)"

(* Get the successor list of a given node ID. *)
fun succ :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "succ g nid = successors_of(case fmlookup g nid of Some n \<Rightarrow> n | None \<Rightarrow> NoNode)"

(* Gives a relation between node IDs - between a node and its input nodes. *)
fun input_edges :: "IRGraph \<Rightarrow> ID rel" where
  "input_edges g = (\<Union> i\<in>fset(fmdom g). {(i,j)|j. j \<in> fset(fset_of_list (inputs_of (kind g i)))})"
(* or this definition (but it cannot generate code):
  "input_edges g = {(i,j). i \<in> fset(fmdom g) \<and> j \<in> set (inputs_of (kind g i))}"
*)

(* Find all the nodes in the graph that have nid as an input. *)
fun usages :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "usages g nid = {j. j \<in> graph_nodes g \<and> (j,nid) \<in> input_edges g}"
(* WAS:
  "usages g nid = fset (ffilter (\<lambda> nid' . nid \<in> set(inp g nid')) (fmdom g))"
*)




(* First well-formedness predicate for IR graphs.
   This function uses field names.
*
fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph g = (
    0 \<in> g_ids g \<and>
    g_nodes g 0 = StartNode \<and>
    (\<forall> n. n \<in> g_ids g \<longrightarrow> set(g_successors g n) \<subseteq> g_ids g) \<and>
    (\<forall> n. n \<in> g_ids g \<longrightarrow> set(g_inputs g n) \<subseteq> g_ids g)
  )
  "
*)
(* Alternative definition using pattern matching.
  TODO: add invariants about no loops through input arrows?
       (certainly ShortCircuitOrNode.canonicalizeNegation assumes 

   (and also through successor arrows?)
*)

(* We define these helper functions to make it easier to debug non-well-formed graphs.
   E.g. if "wff_graph g" 
   fails then try to prove each of:
       "(\<forall>n. has_good_inputs n g)"
       "(\<forall>n. has_good_successors n g)"
       "(\<forall>n. wff_node (g_nodes g n) (g_inputs g n) (g_successors g n))"
   and use 'nitpick' to find the bad n.
*)

(* graph closure invariants *)
fun has_good_inputs :: "ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "has_good_inputs n g = list_all (\<lambda>i. i |\<in>| fmdom g) (inputs_of (kind g n))"

fun has_good_successors :: "ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "has_good_successors n g = list_all (\<lambda>i. i |\<in>| fmdom g) (successors_of (kind g n))"

fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph g = (
    (g \<noteq> fmempty \<longrightarrow> is_StartNode (kind g 0)) \<and>
    (\<forall> n. n |\<in>| fmdom g \<longrightarrow> has_good_inputs n g) \<and>
    (\<forall> n. n |\<in>| fmdom g \<longrightarrow> has_good_successors n g) \<and>
    (\<forall> n. n |\<in>| fmdom g \<longrightarrow> kind g n \<noteq> NoNode)
   )"
(* TODO: add these other invariants?
    (\<forall> n. n \<notin> ids \<longrightarrow> nodes n = StartNode) \<and>
    (\<forall> n. n \<notin> ids \<longrightarrow> successors n = []) \<and>
    (\<forall> n. n \<notin> ids \<longrightarrow> inputs n = []) \<and>
    (\<forall> n. n \<in> ids \<longrightarrow> wff_node (nodes n) (inputs n) (successors n))
  )
  "
*)

lemma wff_kind [simp]:
  assumes "wff_graph g"
  assumes "n |\<in>| fmdom g"
  shows "kind g n \<noteq> NoNode"
  using assms by auto


definition empty_graph:: IRGraph where
  "empty_graph = fmempty"

lemma empty_graph [simp]: "empty_graph = fmempty"
  by (rule empty_graph_def)

(* Example 1: empty graph (just a start node) *)
lemma wff_empty: "wff_graph empty_graph"
  by simp


(* Example 2:
  public static int sq(int x) { return x * x; }

             [1 P(0)]
               \ /
  [0 Start]   [4 *]
       |      /
       V     /
      [5 Return]
*)
definition eg2_sq :: IRGraph where
  "eg2_sq = fmap_of_list [
    (0, StartNode None 5),
    (1, ParameterNode 0),
    (4, MulNode 1 1),
    (5, ReturnNode (Some 4) None)
   ]"

(* Now check some basic properties of this example. *)
lemma wff_eg2_sq: "wff_graph eg2_sq"
  unfolding eg2_sq_def by simp

(* Test the code generation. *)
value "input_edges eg2_sq"
value "usages eg2_sq 1"

end

