section \<open>GraalVM graph representation\<close>

theory IRGraph
  imports 
    IRNodes
    "HOL-Library.FSet"
    "HOL-Library.Finite_Map"
    "HOL.Relation"
begin

(* This theory defines the main Graal data structure - an entire IR Graph. 
type_synonym RealGraph = "(ID fset \<times> (ID \<rightharpoonup> IRNode))" *)

text_raw \<open>\Snip{graphdef}\<close>
typedef IRGraph = "{g :: ID \<rightharpoonup> IRNode . finite (dom g)}"
proof -
  have "finite(dom(Map.empty))" by auto
  then show ?thesis by blast
qed
text_raw \<open>\EndSnip\<close>

(*
fun is_valid :: "RealGraph \<Rightarrow> bool" where
  "is_valid g = (\<forall> n . n |\<in>| fst g \<longleftrightarrow> n \<in> dom (snd g))"
*)

lemma valid_creation[simp]:
  assumes "finite (dom g)"
  shows "Rep_IRGraph (Abs_IRGraph g) = g"
  using Abs_IRGraph_inverse assms by auto


(*typedef IRGraph = "{g :: (ID fset \<times> (ID \<rightharpoonup> IRNode)) 
                    . (\<forall> n . n |\<notin>| fst g \<longrightarrow> n \<notin> dom (snd g))}"*)

setup_lifting type_definition_IRGraph

lift_definition ids :: "IRGraph \<Rightarrow> ID set"
  is Map.dom .

lift_definition irgraph :: "(ID \<times> IRNode) list \<Rightarrow> IRGraph"
  is map_of
  by (simp add: finite_dom_map_of)

lift_definition kind :: "IRGraph \<Rightarrow> (ID \<rightharpoonup> IRNode)"
  is Rep_IRGraph .

lemma irgraph[code]: "ids (irgraph m) = set (map fst m)"
  by transfer (simp add: dom_map_of_conv_image_fst ids.rep_eq irgraph.rep_eq)

(* Get ALL the IDs in the graph. *)
(*fun ids :: "IRGraph \<Rightarrow> ID set" where
  "ids g = dom (Rep_IRGraph g)"*)

text_raw \<open>\Snip{helpers}%\<close>
(* Look up a given ID in the graph and return the whole node. 
definition kind :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRNode option" where
  "kind = snd"


lemma simp_kind_def[simp]:
  "kind g n = snd g n"
  by (simp add: kind_def)
lemma elim_kind_def[simp,elim]: 
  assumes "x = kind g n"
  shows "x = snd g n"
  by (simp add: assms kind_def)
*)

lemma [simp]: "finite (ids g)"
  using Rep_IRGraph ids.rep_eq by auto

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
text_raw \<open>\EndSnip\<close>
(* usages WAS:
  "usages g nid = fset (ffilter (\<lambda> nid' . nid \<in> set(inp g nid')) (fmdom g))"
*)

fun successor_edges :: "IRGraph \<Rightarrow> ID rel" where
  "successor_edges g = (\<Union> i \<in> ids g. {(i,j)|j . j \<in> fset(fset_of_list (succ  g i))})"

fun predecessors :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "predecessors g nid = sorted_list_of_set {j. j \<in> ids g \<and> (j,nid) \<in> successor_edges g}"

fun is_empty :: "IRGraph \<Rightarrow> bool" where
  "is_empty g = ((ids g = {}) \<and> (kind g = Map.empty))"


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
text_raw \<open>\Snip{graphinvar}%\<close>
fun has_good_inputs :: "ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "has_good_inputs n g = list_all (\<lambda>i. i \<in> ids g) (inp g n)"

fun has_good_successors :: "ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "has_good_successors n g = list_all (\<lambda>i. i \<in> ids g) (succ g n)"

fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph g = (
    0 \<in> ids g \<and> isType is_StartNode (kind g 0) \<and> 
    (\<forall> n. n \<in> ids g \<longrightarrow> 
      set (inp g n) \<subseteq> ids g \<and>
      set (succ g n) \<subseteq> ids g \<and>
      kind g n \<noteq> None))" (* \<and>
    (\<not>(is_empty g) \<longrightarrow> 
      (case kind g 0 of None \<Rightarrow> False | Some n \<Rightarrow> is_StartNode n)) \<and> 
    (\<forall> n. n \<in> ids g \<longrightarrow> n \<in> dom (snd g))
      has_good_inputs n g \<and>
      has_good_successors n g \<and>
   )"*)
text_raw \<open>\EndSnip\<close>
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
  assumes "n \<in> ids g"
  shows "kind g n \<noteq> None"
  using wff_graph.simps  assms by auto

(*fun irgraph :: "(ID \<times> IRNode) list \<Rightarrow> (ID \<rightharpoonup> IRNode)" where
  "irgraph g = map_of g"*)

fun add_node :: "nat \<Rightarrow> IRNode \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "add_node nid node g = 
    Abs_IRGraph ((kind g)(nid \<mapsto> node))"

fun remove_node :: "nat \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "remove_node nid g =
    Abs_IRGraph ((kind g)(nid := None))"

(*
lemma add_node_valid[simp]:         
  assumes "gup = add_node nid k g"
  shows "is_valid (Rep_IRGraph gup)"
  using Rep_IRGraph by auto

lemma remove_node_valid[simp]:
  assumes "gup = remove_node nid g"
  shows "is_valid (Rep_IRGraph gup)"
  using Rep_IRGraph by auto
*)

lemma [simp]: "finite (ids (irgraph g))" by (simp add: finite_dom_map_of)

lemma [simp]: "finite (dom g) \<longrightarrow> ids (Abs_IRGraph g) = dom g" using ids.rep_eq by simp

lemma [simp]: "finite (dom g) \<longrightarrow> kind (Abs_IRGraph g) = g" using kind.abs_eq by simp

lemma [simp]: "ids (irgraph g) = set (map fst g)" using irgraph by auto

lemma [simp]: "kind (irgraph g) = map_of g" using irgraph.rep_eq kind.transfer by auto


(* Example 1: empty graph (just a start and end node) *)
definition start_end_graph:: IRGraph where
  "start_end_graph = irgraph [(0, StartNode None 1), (1, EndNode)]"

lemma wff_empty: "wff_graph start_end_graph"
  unfolding start_end_graph_def wff_graph.simps by simp

(* Example 2:
  public static int sq(int x) { return x * x; }

             [1 P(0)]
               \ /
  [0 Start]   [4 *]
       |      /
       V     /
      [5 Return]
*)
definition eg2_sq :: "IRGraph" where
  "eg2_sq = irgraph [
    (0, StartNode None 5),
    (1, ParameterNode 0),
    (4, MulNode 1 1),
    (5, ReturnNode (Some 4) None)
   ]"

lemma ids_some: "x \<in> ids g \<longleftrightarrow> kind g x \<noteq> None"
  using ids.rep_eq kind_def by auto


(* Now check some basic properties of this example. *)
lemma wff_eg2_sq: "wff_graph eg2_sq"
  unfolding eg2_sq_def wff_graph.simps by simp
  
(*
proof -
  have wff_0: "0 \<in> ids eg2_sq"
    unfolding eg2_sq_def eg2_sq_rep_def esy_ids by simp
  have wff_1: "kind eg2_sq 0 = Some (StartNode None 5)" 
    unfolding eg2_sq_def eg2_sq_rep_def esy_kind by simp
  have wff_2: "\<forall> n \<in> ids eg2_sq . set (inp eg2_sq n) \<subseteq> ids eg2_sq"
    unfolding eg2_sq_def eg2_sq_rep_def esy_ids esy_kind inp.simps by simp
  have wff_3: "\<forall> n \<in> ids eg2_sq . set (succ eg2_sq n) \<subseteq> ids eg2_sq"
    unfolding eg2_sq_def eg2_sq_rep_def esy_ids esy_kind succ.simps by simp
  have wff_4: "\<forall> n \<in> ids eg2_sq . kind eg2_sq n \<noteq> None"
    using ids_some by simp
  from wff_0 wff_1 wff_2 wff_3 wff_4 show ?thesis unfolding wff_graph.simps by simp
qed
*)

code_datatype Abs_IRGraph irgraph

lemma [code]: "(Rep_IRGraph (irgraph m)) = map_of m"
  using Abs_IRGraph_inverse
  by (simp add: irgraph.rep_eq)

(* Test the code generation. *)
value "input_edges eg2_sq"
value "usages eg2_sq 1"

end

