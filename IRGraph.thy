section \<open>GraalVM Graph Representation\<close>

theory IRGraph
  imports 
    IRNodes
    "HOL-Library.FSet"
    "HOL.Relation"
begin

text \<open>This theory defines the main Graal data structure - an entire IR Graph.\<close>

text \<open>
IRGraph is defined as a partial map with a finite domain.
The finite domain is required to be able to generate code and produce an interpreter.
\<close>
text_raw \<open>\Snip{graphdef}\<close>
typedef IRGraph = "{g :: ID \<rightharpoonup> IRNode . finite (dom g)}"
proof -
  have "finite(dom(Map.empty))" by auto
  then show ?thesis by blast
qed
text_raw \<open>\EndSnip\<close>

setup_lifting type_definition_IRGraph

lift_definition ids :: "IRGraph \<Rightarrow> ID set"
  is Map.dom .

lift_definition kind :: "IRGraph \<Rightarrow> (ID \<rightharpoonup> IRNode)"
  is Rep_IRGraph .

lift_definition irgraph :: "(ID \<times> IRNode) list \<Rightarrow> IRGraph"
  is map_of
  by (simp add: finite_dom_map_of)

(* Theories are required for code generation to work *)
code_datatype irgraph

lemma irgraph[code]: "ids (irgraph m) = set (map fst m)"
  by transfer (simp add: dom_map_of_conv_image_fst ids.rep_eq irgraph.rep_eq)

lemma [code]: "(Rep_IRGraph (irgraph m)) = map_of m"
  using Abs_IRGraph_inverse
  by (simp add: irgraph.rep_eq)


text_raw \<open>\Snip{helpers}%\<close>
(* Get the inputs list of a given node ID. *)
fun inp :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "inp g nid = (case kind g nid of Some n \<Rightarrow> inputs_of n | None \<Rightarrow> [])"
(* Get the successor list of a given node ID. *)
fun succ :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "succ g nid = (case kind g nid of Some n \<Rightarrow> successors_of n | None \<Rightarrow> [])"
(* Gives a relation between node IDs - between a node and its input nodes. *)
fun input_edges :: "IRGraph \<Rightarrow> ID rel" where
  "input_edges g = (\<Union> i \<in> ids g. {(i,j)|j. j \<in> fset(fset_of_list (inp g i))})"
(* Find all the nodes in the graph that have nid as an input. *)
fun usages :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "usages g nid = {j. j \<in> ids g \<and> (j,nid) \<in> input_edges g}"

fun successor_edges :: "IRGraph \<Rightarrow> ID rel" where
  "successor_edges g = (\<Union> i \<in> ids g. {(i,j)|j . j \<in> fset(fset_of_list (succ  g i))})"

fun predecessors :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "predecessors g nid = sorted_list_of_set {j. j \<in> ids g \<and> (j,nid) \<in> successor_edges g}"

fun is_empty :: "IRGraph \<Rightarrow> bool" where
  "is_empty g = ((ids g = {}) \<and> (kind g = Map.empty))"

fun add_node :: "nat \<Rightarrow> IRNode \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "add_node nid node g = 
    Abs_IRGraph ((kind g)(nid \<mapsto> node))"

fun remove_node :: "nat \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "remove_node nid g =
    Abs_IRGraph ((kind g)(nid := None))"
text_raw \<open>\EndSnip\<close>


text_raw \<open>\Snip{wff_graph}%\<close>
fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph g = (
    0 \<in> ids g \<and> isType is_StartNode (kind g 0) \<and> 
    (\<forall> n. n \<in> ids g \<longrightarrow> 
      set (inp g n) \<subseteq> ids g \<and>
      set (succ g n) \<subseteq> ids g \<and>
      kind g n \<noteq> None)
  )"
text_raw \<open>\EndSnip\<close>

lemma ids_some[simp]: "x \<in> ids g \<longleftrightarrow> kind g x \<noteq> None" using ids.rep_eq kind_def by auto

lemma valid_creation[simp]:
  "finite (dom g) \<longleftrightarrow> Rep_IRGraph (Abs_IRGraph g) = g"
  using Abs_IRGraph_inverse by (metis Rep_IRGraph mem_Collect_eq)

lemma [simp]: "finite (ids g)" using Rep_IRGraph ids.rep_eq by auto

lemma [simp]: "finite (ids (irgraph g))" by (simp add: finite_dom_map_of)

lemma [simp]: "finite (dom g) \<longrightarrow> ids (Abs_IRGraph g) = dom g" using ids.rep_eq by simp

lemma [simp]: "finite (dom g) \<longrightarrow> kind (Abs_IRGraph g) = g" using kind.abs_eq by simp

lemma [simp]: "ids (irgraph g) = set (map fst g)" using irgraph by auto

lemma [simp]: "kind (irgraph g) = map_of g" using irgraph.rep_eq kind.transfer by auto


subsection "Example Graphs"
text "Example 1: empty graph (just a start and end node)"
definition start_end_graph:: IRGraph where
  "start_end_graph = irgraph [(0, StartNode None 1), (1, EndNode)]"

lemma wff_empty: "wff_graph start_end_graph"
  unfolding start_end_graph_def wff_graph.simps by simp

text \<open>Example 2:
  public static int sq(int x) { return x * x; }

             [1 P(0)]
               \ /
  [0 Start]   [4 *]
       |      /
       V     /
      [5 Return]
\<close>
definition eg2_sq :: "IRGraph" where
  "eg2_sq = irgraph [
    (0, StartNode None 5),
    (1, ParameterNode 0),
    (4, MulNode 1 1),
    (5, ReturnNode (Some 4) None)
   ]"

lemma wff_eg2_sq: "wff_graph eg2_sq"
  unfolding eg2_sq_def wff_graph.simps by simp

(* Test the code generation. *)
value "input_edges eg2_sq"
value "usages eg2_sq 1"

end

