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

setup_lifting type_definition_IRGraph

text_raw \<open>\Snip{lifted_helpers}%\<close>
fun has_no_node :: "(ID \<rightharpoonup> (IRNode \<times> Stamp)) \<Rightarrow> ID \<Rightarrow> bool" where
  "has_no_node g nid = (\<exists>s . g nid = (Some (NoNode, s)))"

definition node_ids :: "(ID \<rightharpoonup> (IRNode \<times> Stamp)) \<Rightarrow> ID set" where
  "node_ids g = {nid \<in> dom g . \<not>(has_no_node g nid)}"

lift_definition ids :: "IRGraph \<Rightarrow> ID set"
  is node_ids .

definition node_kind :: "(ID \<rightharpoonup> (IRNode \<times> Stamp)) \<Rightarrow> ID \<Rightarrow> IRNode" where
  "node_kind g nid = (case g nid of 
    None \<Rightarrow> NoNode 
    | Some n \<Rightarrow> fst n)"

lift_definition kind :: "IRGraph \<Rightarrow> (ID \<Rightarrow> IRNode)"
  is node_kind .

definition node_stamp :: "(ID \<rightharpoonup> (IRNode \<times> Stamp)) \<Rightarrow> ID \<Rightarrow> Stamp" where
  "node_stamp g nid = (case g nid of 
    None \<Rightarrow> IllegalStamp 
    | Some n \<Rightarrow> snd n)"

lift_definition stamp :: "IRGraph \<Rightarrow> ID \<Rightarrow> Stamp"
  is node_stamp .
text_raw \<open>\EndSnip\<close>

lemma node_ids_imp:
  "\<nexists>nid . nid \<in> (node_ids g) \<and> has_no_node g nid"
  by (auto simp: node_ids_def)

lemma node_ids_defs:
  "node_ids g = dom g - {nid \<in> dom g . has_no_node g nid}"
  using node_ids_def by auto

definition map_upd :: "ID \<Rightarrow> (IRNode \<times> Stamp) \<Rightarrow> (ID \<rightharpoonup> (IRNode \<times> Stamp)) \<Rightarrow> (ID \<rightharpoonup> (IRNode \<times> Stamp))" where
  "map_upd nid k g = g(nid \<mapsto> k)"

lift_definition add_node :: "ID \<Rightarrow> (IRNode \<times> Stamp) \<Rightarrow> IRGraph \<Rightarrow> IRGraph"
  is map_upd
  by (simp add: map_upd_def)

definition map_rm :: "ID \<Rightarrow> (ID \<rightharpoonup> (IRNode \<times> Stamp)) \<Rightarrow> (ID \<rightharpoonup> (IRNode \<times> Stamp))" where
  "map_rm nid g = g(nid := None)"

lift_definition remove_node :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph"
  is map_rm
  by (simp add: map_rm_def)

lemma ran_not_in:
  "\<forall>x l. (\<nexists>n. n \<in> set l \<and> snd n = x) \<longrightarrow> x \<notin> ran (map_of l)"
  by (smt map_of_SomeD mem_Collect_eq prod.sel(2) ran_def)

fun no_node :: "(ID \<times> (IRNode \<times> Stamp)) list \<Rightarrow> (ID \<times> (IRNode \<times> Stamp)) list" where
  "no_node g = filter (\<lambda>n. fst (snd n) \<noteq> NoNode) g"

lift_definition irgraph :: "(ID \<times> (IRNode \<times> Stamp)) list \<Rightarrow> IRGraph"
  is map_of
  by (simp add: finite_dom_map_of)

(* Theories are required for code generation to work *)
code_datatype irgraph

lemma irgraph[code]: "ids (irgraph m) = set (map fst (no_node m))"
  using dom_map_of_conv_image_fst ids.rep_eq irgraph.rep_eq apply simp
  using node_ids_def sorry

lemma [code]: "(Rep_IRGraph (irgraph m)) = map_of m"
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

fun predecessors :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "predecessors g nid = sorted_list_of_set {j. j \<in> ids g \<and> (j,nid) \<in> successor_edges g}"

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
    (\<forall> n. n \<in> ids g \<longrightarrow> 
      set (inp g n) \<subseteq> ids g \<and>
      set (succ g n) \<subseteq> ids g \<and>
      kind g n \<noteq> NoNode) \<and>
    (\<forall> n. n \<in> (nodes_of g isPhiNodeType) \<longrightarrow>
      length (edge ir_values n g)
       = length (edge ir_ends (edge ir_merge n g) g)) \<and>
    (\<forall> n. n \<in> (nodes_of g is_IfNode) \<longrightarrow>
      stamp g (edge ir_condition n g) = IntegerStamp 1 0 1)
  )"
text_raw \<open>\EndSnip\<close>


lemma ids_some[simp]: "x \<in> ids g \<longleftrightarrow> kind g x \<noteq> NoNode" 
proof -
  have that: "x \<in> ids g \<longrightarrow> kind g x \<noteq> NoNode"
    using ids.rep_eq kind.rep_eq node_ids_defs node_kind_def by force
  have "kind g x \<noteq> NoNode \<longrightarrow> x \<in> ids g"
    by (metis (mono_tags, lifting) domIff fst_conv has_no_node.simps ids.rep_eq kind.rep_eq mem_Collect_eq node_ids_def node_kind_def option.case_eq_if option.sel)
  from this that show ?thesis by auto
qed

lemma valid_creation[simp]:
  "finite (dom g) \<longleftrightarrow> Rep_IRGraph (Abs_IRGraph g) = g"
  using Abs_IRGraph_inverse by (metis Rep_IRGraph mem_Collect_eq)

lemma [simp]: "finite (ids g)" 
  using Rep_IRGraph ids.rep_eq node_ids_def by simp

lemma [simp]: "finite (ids (irgraph g))" 
  by (simp add: finite_dom_map_of)

lemma sup: "\<not>(has_no_node g nid) \<and> g nid = Some n \<longrightarrow> fst n \<noteq> NoNode"
  unfolding has_no_node.simps
  by (metis eq_fst_iff)

lemma [simp]: "finite (dom g) \<longrightarrow> ids (Abs_IRGraph g) = {nid \<in> dom g . \<not> has_no_node g nid}"
  using ids.rep_eq node_ids_def by simp

lemma [simp]: "finite (dom g) \<longrightarrow> kind (Abs_IRGraph g) = (\<lambda>x . (case g x of None \<Rightarrow> NoNode | Some n \<Rightarrow> fst n))"
  using kind.abs_eq node_kind_def
  by (metis eq_onp_live_step)

lemma [simp]: "finite (dom g) \<longrightarrow> stamp (Abs_IRGraph g) = (\<lambda>x . (case g x of None \<Rightarrow> IllegalStamp | Some n \<Rightarrow> snd n))"
  using stamp.abs_eq node_stamp_def
  using stamp.rep_eq by auto

lemma [simp]: "ids (irgraph g) = set (map fst (no_node g))" 
  using irgraph by auto

lemma [simp]: "kind (irgraph g) = (\<lambda>nid. (case (map_of g) nid of None \<Rightarrow> NoNode | Some n \<Rightarrow> fst n))" 
  using irgraph.rep_eq kind.transfer node_kind_def kind.rep_eq
  by auto

lemma [simp]: "stamp (irgraph g) = (\<lambda>nid. (case (map_of g) nid of None \<Rightarrow> IllegalStamp | Some n \<Rightarrow> snd n))" 
  using irgraph.rep_eq stamp.transfer node_stamp_def stamp.rep_eq
  by auto

lemma add_node_lookup:
  "gup = add_node nid (k, s) g \<longrightarrow> kind gup nid = k \<and> stamp gup nid = s"
  by (simp add: add_node.rep_eq kind.rep_eq map_upd_def node_kind_def node_stamp_def stamp.rep_eq)

lemma remove_node_lookup:
  "gup = remove_node nid g \<longrightarrow> kind gup nid = NoNode \<and> stamp gup nid = IllegalStamp"
  by (simp add: kind.rep_eq map_rm_def node_kind_def node_stamp_def remove_node.rep_eq stamp.rep_eq)

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

