section \<open>GraalVM graph representation\<close>

theory IRGraph
  imports 
    IRNodes
    "HOL-Library.FSet"
    "HOL.Relation"
begin

(* This theory defines the main Graal data structure - an entire IR Graph. *)
type_synonym RealGraph = "(ID fset \<times> (ID \<rightharpoonup> IRNode))"

text_raw \<open>\Snip{graphdef}\<close>
typedef IRGraph = "{g :: RealGraph 
                    . (\<forall> n . n |\<in>| fst g \<longleftrightarrow> n \<in> dom (snd g))}"
  apply auto
  done
text_raw \<open>\EndSnip\<close>

fun is_valid :: "RealGraph \<Rightarrow> bool" where
  "is_valid g = (\<forall> n . n |\<in>| fst g \<longleftrightarrow> n \<in> dom (snd g))"

lemma valid_creation[simp]:
  assumes "is_valid g"
  shows "Rep_IRGraph (Abs_IRGraph g) = g"
  using Abs_IRGraph_inverse assms by auto

(*typedef IRGraph = "{g :: (ID fset \<times> (ID \<rightharpoonup> IRNode)) 
                    . (\<forall> n . n |\<notin>| fst g \<longrightarrow> n \<notin> dom (snd g))}"*)

setup_lifting type_definition_IRGraph
lift_definition fst :: "IRGraph \<Rightarrow> ID fset"
  is Product_Type.fst .

lift_definition snd :: "IRGraph \<Rightarrow> (ID \<rightharpoonup> IRNode)"
  is Product_Type.snd .


(* Get ALL the IDs in the graph. *)
fun ids :: "IRGraph \<Rightarrow> ID set" where
  "ids g = fset (fst g)"

text_raw \<open>\Snip{helpers}%\<close>
(* Look up a given ID in the graph and return the whole node. *)
fun kind :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRNode" where
  "kind g nid = (case snd g nid of 
                 Some n \<Rightarrow> n | 
                 None \<Rightarrow> NoNode)"
(* Get the inputs list of a given node ID. *)
fun inp :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "inp g nid = inputs_of(kind g nid)"
(* Gives a relation between node IDs - between a node and its input nodes. *)
fun input_edges :: "IRGraph \<Rightarrow> ID rel" where
  "input_edges g = (\<Union> i \<in> ids g. {(i,j)|j. j \<in> fset(fset_of_list (inputs_of (kind g i)))})"
(* Find all the nodes in the graph that have nid as an input. *)
fun usages :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "usages g nid = {j. j \<in> ids g \<and> (j,nid) \<in> input_edges g}"
text_raw \<open>\EndSnip\<close>
(* usages WAS:
  "usages g nid = fset (ffilter (\<lambda> nid' . nid \<in> set(inp g nid')) (fmdom g))"
*)


(* Get the successor list of a given node ID. *)
fun succ :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "succ g nid = successors_of(kind g nid)"

fun is_empty :: "IRGraph \<Rightarrow> bool" where
  "is_empty g = ((ids g = {}) \<and> (snd g = Map.empty))"

definition empty_graph:: IRGraph where
  "empty_graph = Abs_IRGraph (fset_of_list [], Map.empty)"

lemma empty_graph [simp]: "empty_graph = Abs_IRGraph (fset_of_list [], Map.empty)"
  by (rule empty_graph_def)


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
  "has_good_inputs n g = list_all (\<lambda>i. i \<in> ids g) (inputs_of (kind g n))"

fun has_good_successors :: "ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "has_good_successors n g = list_all (\<lambda>i. i \<in> ids g) (successors_of (kind g n))"

fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph g = (
    (\<not>(is_empty g) \<longrightarrow> is_StartNode (kind g 0)) \<and>
    (\<forall> n. n \<in> ids g \<longrightarrow> has_good_inputs n g) \<and>
    (\<forall> n. n \<in> ids g \<longrightarrow> has_good_successors n g) \<and>
    (\<forall> n. n \<in> ids g \<longrightarrow> kind g n \<noteq> NoNode))" (* \<and>
    (\<forall> n. n \<in> ids g \<longrightarrow> n \<in> dom (snd g))
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
  shows "kind g n \<noteq> NoNode"
  using assms by auto

fun irgraph :: "(ID \<times> IRNode) list \<Rightarrow> RealGraph" where
  "irgraph g = (fset_of_list (map prod.fst g), map_of g)"

fun add_node :: "nat \<Rightarrow> IRNode \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "add_node nid node g = 
    Abs_IRGraph (
      (fset_of_list [nid]) |\<union>| (fst g),
      (snd g)(nid \<mapsto> node)
    )"

lemma add_node_valid[simp]:         
  assumes "gup = add_node nid k g"
  shows "is_valid (Rep_IRGraph gup)"
  using Rep_IRGraph by auto

(* Example 1: empty graph (just a start node) *)
lemma wff_empty: "wff_graph empty_graph"
  unfolding empty_graph
  by (simp add: eq_onp_same_args fst.abs_eq snd.abs_eq)


(* Example 2:
  public static int sq(int x) { return x * x; }

             [1 P(0)]
               \ /
  [0 Start]   [4 *]
       |      /
       V     /
      [5 Return]
*)
definition eg2_sq_rep :: RealGraph where
  "eg2_sq_rep = irgraph [
    (0, StartNode None 5),
    (1, ParameterNode 0),
    (4, MulNode 1 1),
    (5, ReturnNode (Some 4) None)
   ]"

definition eg2_sq :: IRGraph where
  "eg2_sq = Abs_IRGraph eg2_sq_rep"

lemma irgraph_dom[simp]: 
  assumes "\<forall>nid. nid |\<in>| fs \<longleftrightarrow> fm nid \<noteq> None"
  shows "IRGraph.fst(Abs_IRGraph(fs,fm)) = fs"
  using Abs_IRGraph_inverse assms fst.rep_eq
  by (simp add: domIff)

lemma irgraph_dom_x:
  assumes "nid \<in> ids g"
  shows "(snd g) nid \<noteq> None"
  using Rep_IRGraph assms fst.rep_eq snd.rep_eq
  using notin_fset by fastforce

lemma irgraph_dom_inv:
  assumes "nid \<notin> ids g"
  shows "(snd g) nid = None"
  using Rep_IRGraph assms
  using fst.rep_eq notin_fset snd.rep_eq by fastforce 

lemma irgraph_rng[simp]: 
  assumes "\<forall>nid. nid |\<in>| fs \<longleftrightarrow> fm nid \<noteq> None"
  shows "IRGraph.snd(Abs_IRGraph(fs,fm)) = fm"
  using Abs_IRGraph_inverse assms snd.rep_eq
  by (simp add: domIff)

(* Now check some basic properties of this example. *)
lemma wff_eg2_sq: "wff_graph eg2_sq"
  unfolding eg2_sq_def eg2_sq_rep_def  irgraph.simps
  apply simp 
  done

code_datatype Abs_IRGraph

lemma [code]: "Rep_IRGraph (Abs_IRGraph m) = m"
  using Abs_IRGraph_inverse sorry

lemma eg2_sq_inv: 
  "\<forall>nid. nid |\<in>| prod.fst eg2_sq_rep \<longleftrightarrow> prod.snd eg2_sq_rep nid \<noteq> None"
  unfolding eg2_sq_rep_def irgraph.simps
  apply simp
  done

lemma rep_eg2: "Rep_IRGraph eg2_sq = eg2_sq_rep"
proof -
  have "\<forall>n. n |\<in>| prod.fst eg2_sq_rep \<longleftrightarrow> prod.snd eg2_sq_rep n \<noteq> None"
    using eg2_sq_inv by fastforce
  then show ?thesis
    by (simp add: Abs_IRGraph_inverse domIff eg2_sq_def)
qed


(* Test the code generation. *)
value "input_edges eg2_sq"
value "usages eg2_sq 1"

end

