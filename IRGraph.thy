section \<open>GraalVM Graph Representation\<close>

theory IRGraph
  imports 
    IRNodeHierarchy
    Stamp
    "HOL-Library.FSet"
    "HOL.Relation"
begin

text \<open>This theory defines the main Graal data structure - an entire IR Graph.\<close>

text \<open>
IRGraph is defined as a partial map with a finite domain.
The finite domain is required to be able to generate code and produce an interpreter.
\<close>
text_raw \<open>\Snip{graphdef}\<close>
typedef IRGraph = "{g :: ID \<rightharpoonup> (IRNode \<times> Stamp) . finite (dom g)}"
text_raw \<open>\EndSnip\<close>
proof -
  have "finite(dom(Map.empty)) \<and> ran Map.empty = {}" by auto
  then show ?thesis
    by fastforce
qed

text_raw \<open>\Snip{graphdefnostamp}
@{bold \<open>typedef\<close>} @{term[source] \<open>IRGraph = {g :: ID \<rightharpoonup> IRNode . finite (dom g)}\<close>}
\EndSnip\<close>

setup_lifting type_definition_IRGraph

text_raw \<open>\Snip{fake_lifted_helpers}\<close>
fun ids_fake :: "(ID \<rightharpoonup> IRNode) \<Rightarrow> ID set" where
  "ids_fake g = {nid \<in> dom g . g nid \<noteq> (Some NoNode)}"

fun kind_fake :: "(ID \<rightharpoonup> IRNode) \<Rightarrow> (ID \<Rightarrow> IRNode)" where
  "kind_fake g = (\<lambda>nid. (case g nid of None \<Rightarrow> NoNode | Some v \<Rightarrow> v))"
text_raw \<open>\EndSnip\<close>

lift_definition ids :: "IRGraph \<Rightarrow> ID set"
  is "\<lambda>g. {nid \<in> dom g . \<nexists>s. g nid = (Some (NoNode, s))}" .

fun with_default :: "'c \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> (('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> 'c)" where
  "with_default def conv = (\<lambda>m k.
    (case m k of None \<Rightarrow> def | Some v \<Rightarrow> conv v))"

lift_definition kind :: "IRGraph \<Rightarrow> (ID \<Rightarrow> IRNode)"
  is "with_default NoNode fst" .

lift_definition stamp :: "IRGraph \<Rightarrow> ID \<Rightarrow> Stamp"
  is "with_default IllegalStamp snd" .

lift_definition add_node :: "ID \<Rightarrow> (IRNode \<times> Stamp) \<Rightarrow> IRGraph \<Rightarrow> IRGraph"
  is "\<lambda>nid k g. if fst k = NoNode then g else g(nid \<mapsto> k)" by simp

lift_definition remove_node :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph"
  is "\<lambda>nid g. g(nid := None)" by simp

lift_definition replace_node :: "ID \<Rightarrow> (IRNode \<times> Stamp) \<Rightarrow> IRGraph \<Rightarrow> IRGraph"
  is "\<lambda>nid k g. if fst k = NoNode then g else g(nid \<mapsto> k)" by simp

lift_definition as_list :: "IRGraph \<Rightarrow> (ID \<times> IRNode \<times> Stamp) list"
  is "\<lambda>g. map (\<lambda>k. (k, the (g k))) (sorted_list_of_set (dom g))" .

fun no_node :: "(ID \<times> (IRNode \<times> Stamp)) list \<Rightarrow> (ID \<times> (IRNode \<times> Stamp)) list" where
  "no_node g = filter (\<lambda>n. fst (snd n) \<noteq> NoNode) g"

lift_definition irgraph :: "(ID \<times> (IRNode \<times> Stamp)) list \<Rightarrow> IRGraph"
  is "map_of \<circ> no_node"
  by (simp add: finite_dom_map_of)

(* Theories are required for code generation to work *)
code_datatype irgraph

fun filter_none where
  "filter_none g = {nid \<in> dom g . \<nexists>s. g nid = (Some (NoNode, s))}"

lemma no_node_clears:
  "res = no_node xs \<longrightarrow> (\<forall>x \<in> set res. fst (snd x) \<noteq> NoNode)"
  by simp

lemma dom_eq:
  assumes "\<forall>x \<in> set xs. fst (snd x) \<noteq> NoNode"
  shows "filter_none (map_of xs) = dom (map_of xs)"
  unfolding filter_none.simps using assms map_of_SomeD
  by fastforce

lemma fil_eq:
  "filter_none (map_of (no_node xs)) = set (map fst (no_node xs))"
  using no_node_clears
  by (metis dom_eq dom_map_of_conv_image_fst list.set_map)

lemma irgraph[code]: "ids (irgraph m) = set (map fst (no_node m))"
  unfolding irgraph_def ids_def using fil_eq
  by (smt Rep_IRGraph comp_apply eq_onp_same_args filter_none.simps ids.abs_eq ids_def irgraph.abs_eq irgraph.rep_eq irgraph_def mem_Collect_eq)

lemma [code]: "Rep_IRGraph (irgraph m) = map_of (no_node m)"
  using Abs_IRGraph_inverse
  by (simp add: irgraph.rep_eq)


text_raw \<open>\Snip{helpers}%\<close>
(* Get the inputs list of a given node ID. *)
fun inp :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "inp g nid = (inputs_of (kind g nid))"
(* Get the successor list of a given node ID. *)
fun succ :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "succ g nid = (successors_of (kind g nid))"
(* Gives a relation between node IDs - between a node and its input nodes. *)
fun input_edges :: "IRGraph \<Rightarrow> ID rel" where
  "input_edges g = (\<Union> i \<in> ids g. {(i,j)|j. j \<in> fset(fset_of_list (inp g i))})"
(* Find all the nodes in the graph that have nid as an input. *)
fun usages :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "usages g nid = {j. j \<in> ids g \<and> (j,nid) \<in> input_edges g}"

fun successor_edges :: "IRGraph \<Rightarrow> ID rel" where
  "successor_edges g = (\<Union> i \<in> ids g. {(i,j)|j . j \<in> fset(fset_of_list (succ  g i))})"

fun predecessors :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "predecessors g nid = {j. j \<in> ids g \<and> (j,nid) \<in> successor_edges g}"

fun nodes_of :: "IRGraph \<Rightarrow> (IRNode \<Rightarrow> bool) \<Rightarrow> ID set" where
  "nodes_of g sel = {nid \<in> ids g . sel (kind g nid)}"

fun edge :: "(IRNode \<Rightarrow> 'a) \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> 'a" where
  "edge sel nid g = sel (kind g nid)"
text_raw \<open>\EndSnip\<close>

fun is_empty :: "IRGraph \<Rightarrow> bool" where
  "is_empty g = (ids g = {})"

text_raw \<open>\Snip{wff_graph}%\<close>
fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph g = (
    0 \<in> ids g \<and> is_StartNode (kind g 0) \<and> 
    (\<forall> n \<in> ids g .
      set (inp g n) \<subseteq> ids g \<and>
      set (succ g n) \<subseteq> ids g \<and>
      kind g n \<noteq> NoNode) \<and>
    (\<forall> n \<in> (nodes_of g isPhiNodeType) .
      length (edge ir_values n g)
       = length (edge ir_ends (edge ir_merge n g) g))
  )"
text_raw \<open>\EndSnip\<close>


lemma ids_some[simp]: "x \<in> ids g \<longleftrightarrow> kind g x \<noteq> NoNode" 
proof -
  have that: "x \<in> ids g \<longrightarrow> kind g x \<noteq> NoNode"
    using ids.rep_eq kind.rep_eq by force
  have "kind g x \<noteq> NoNode \<longrightarrow> x \<in> ids g"
    unfolding with_default.simps kind_def ids_def
    by (cases "Rep_IRGraph g x = None"; auto)
  from this that show ?thesis by auto
qed

lemma valid_creation[simp]:
  "finite (dom g) \<longleftrightarrow> Rep_IRGraph (Abs_IRGraph g) = g"
  using Abs_IRGraph_inverse by (metis Rep_IRGraph mem_Collect_eq)

lemma [simp]: "finite (ids g)" 
  using Rep_IRGraph ids.rep_eq by simp

lemma [simp]: "finite (ids (irgraph g))" 
  by (simp add: finite_dom_map_of)

lemma [simp]: "finite (dom g) \<longrightarrow> ids (Abs_IRGraph g) = {nid \<in> dom g . \<nexists>s. g nid = Some (NoNode, s)}"
  using ids.rep_eq by simp

lemma [simp]: "finite (dom g) \<longrightarrow> kind (Abs_IRGraph g) = (\<lambda>x . (case g x of None \<Rightarrow> NoNode | Some n \<Rightarrow> fst n))"
  by (simp add: kind.rep_eq)

lemma [simp]: "finite (dom g) \<longrightarrow> stamp (Abs_IRGraph g) = (\<lambda>x . (case g x of None \<Rightarrow> IllegalStamp | Some n \<Rightarrow> snd n))"
  using stamp.abs_eq stamp.rep_eq by auto

lemma [simp]: "ids (irgraph g) = set (map fst (no_node g))" 
  using irgraph by auto

lemma [simp]: "kind (irgraph g) = (\<lambda>nid. (case (map_of (no_node g)) nid of None \<Rightarrow> NoNode | Some n \<Rightarrow> fst n))" 
  using irgraph.rep_eq kind.transfer kind.rep_eq by auto

lemma [simp]: "stamp (irgraph g) = (\<lambda>nid. (case (map_of (no_node g)) nid of None \<Rightarrow> IllegalStamp | Some n \<Rightarrow> snd n))" 
  using irgraph.rep_eq stamp.transfer stamp.rep_eq by auto

lemma map_of_upd: "(map_of g)(k \<mapsto> v) = (map_of ((k, v) # g))"
  by simp

(* this proof should be simplier *)
lemma [code]: "replace_node nid k (irgraph g) = (irgraph ( ((nid, k) # g)))"
proof (cases "fst k = NoNode")
  case True
  then show ?thesis
    by (metis (mono_tags, lifting) Rep_IRGraph_inject filter.simps(2) irgraph.abs_eq no_node.simps replace_node.rep_eq snd_conv)
next
  case False
  then show ?thesis unfolding irgraph_def replace_node_def no_node.simps
    by (smt (verit, best) Rep_IRGraph comp_apply eq_onp_same_args filter.simps(2) id_def irgraph.rep_eq map_fun_apply map_of_upd mem_Collect_eq no_node.elims replace_node.abs_eq replace_node_def snd_eqD)
qed

lemma [code]: "add_node nid k (irgraph g) = (irgraph (((nid, k) # g)))"
  by (smt (z3) Rep_IRGraph_inject add_node.rep_eq filter.simps(2) irgraph.rep_eq map_of_upd no_node.simps snd_conv)

lemma add_node_lookup:
  "gup = add_node nid (k, s) g \<longrightarrow> 
    (if k \<noteq> NoNode then kind gup nid = k \<and> stamp gup nid = s else True)"
proof (cases "k = NoNode")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis
    by (simp add: kind.rep_eq add_node.rep_eq stamp.rep_eq)
qed

lemma remove_node_lookup:
  "gup = remove_node nid g \<longrightarrow> kind gup nid = NoNode \<and> stamp gup nid = IllegalStamp"
  by (simp add: kind.rep_eq remove_node.rep_eq stamp.rep_eq)

lemma replace_node_lookup[simp]:
  "gup = replace_node nid (k, s) g \<and> k \<noteq> NoNode \<longrightarrow> kind gup nid = k \<and> stamp gup nid = s"
  by (simp add: replace_node.rep_eq kind.rep_eq stamp.rep_eq)

lemma replace_node_unchanged:
  "gup = replace_node nid (k, s) g \<longrightarrow> (\<forall> n \<in> (ids g - {nid}) . n \<in> ids g \<and> n \<in> ids gup \<and> kind g n = kind gup n)" 
  by (simp add: kind.rep_eq replace_node.rep_eq)

subsection "Example Graphs"
text "Example 1: empty graph (just a start and end node)"
definition start_end_graph:: IRGraph where
  "start_end_graph = irgraph [(0, StartNode None 1, VoidStamp), (1, EndNode, VoidStamp)]"

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
    (0, StartNode None 5, VoidStamp),
    (1, ParameterNode 0, default_stamp),
    (4, MulNode 1 1, default_stamp),
    (5, ReturnNode (Some 4) None, default_stamp)
   ]"

lemma wff_eg2_sq: "wff_graph eg2_sq"
  unfolding eg2_sq_def wff_graph.simps by simp

(* TODO: to include the float type (used by stamps) we need
         a code equation for float_of but it is not clear how
         to implement this correctly *)
lemma[code]: "float_of n = 0" sorry

(* Test the code generation. *)
value "input_edges eg2_sq"
value "usages eg2_sq 1"

end

