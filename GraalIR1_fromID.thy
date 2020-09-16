section \<open>GraalVM graph representation\<close>

theory GraalIR1_fromID
  imports 
    Main
    "HOL-Library.Finite_Map"
begin

(* This is a theory of GraalVM IR graphs that uses numbered nodes.

   It is similar to GraalIR1 but moves the identity value (int)
   out of each node and into the domains of various mapping functions.

   The Graal IR 'Node' type is an abstract class with many subclasses.
   We define it as a datatype comprised of the *leaf* classes.
   If we need the intermediate classes (like FixedNode or FloatingNode), 
   we can define those as the union of the appropriate leaves.
*)

(* To identify each Node, we use a simple natural number index.
   Zero is always the start node in a graph.
*)
type_synonym ID = "nat"

datatype (discs_sels) IRNode = 
  CallNode (startNode: ID)
  | ConstantNode (intValue: int)  (* TODO: should be string *)
  | ParameterNode (index: nat)
  | PhiNode  (* TODO: subclasses GuardPhiNode, MemoryPhiNode *)
  | ValuePhiNode
  | ValueProxyNode
  | AddNode
  | SubNode
  | MulNode
  | SwitchNode
  | IfNode  (* TODO: add field: double trueSuccessorProbability; *)
  | ShortCircuitOrNode (xNegated:bool) (yNegated:bool) (* TODO: add field: double shortCircuitProbability; *)
  | LogicNegationNode   (* the logical not operator *)
  | KillingBeginNode
  | BeginNode  (* TODO: all the BeginStateSplitNode subclasses (inc. StartNode) *)
  | StartNode
  | LoopEndNode
  | LoopExitNode
  | MergeNode
  | ReturnNode
  | EndNode
(* Added nodes *)
  | LoopBeginNode
  | LoopExit
  | AbsNode
  | AndNode
  | OrNode
  | XorNode
  | NegateNode
  | IntegerEqualsNode
  | IntegerLessThanNode
  | ConditionalNode
  | NewInstanceNode string (* class name *)
  | LoadFieldNode string (* field name *)
  | StoreFieldNode string (* field name *)
  | LoadStaticFieldNode string string (* class name, field name *)
  | StoreStaticFieldNode string string (* class name, field name *)
  | FrameStateNode (* effectively unused *)
  | FrameState

  | NoNode (* to not cause too much pain when switching to partial *)
  (* and hundreds of other Node subclasses!... *)

(* Next we may want a predicate for each subclass.
   The '(discs_sels)' above automatically generates (is_StartNode _) etc.
   We can combine these to define similar predicates for abstract subclasses:
*)
definition is_BinaryArithNode :: "IRNode \<Rightarrow> bool" where
  "is_BinaryArithNode n = (n = AddNode \<or> n = SubNode \<or> n = MulNode)"


(* These two kinds of functions will model our two kinds of edges. *)
type_synonym SuccessorEdges = "ID \<Rightarrow> ID list"
type_synonym InputEdges = "ID \<Rightarrow> ID list"

(* Here is the main Graal data structure - an entire IR Graph.
   Note that we *name* each component - like a record.
*)
text_raw \<open>\snip{graphdef}{\<close>
datatype Node = N
  (n_kind : IRNode)
  (n_inputs : "ID list")
  (n_successors : "ID list")

type_synonym Graph = "(ID, Node) fmap"
text_raw \<open>}%endsnip\<close>

definition EmptyNode :: "Node" where
  "EmptyNode = N NoNode [] []"

fun graph_nodes :: "Graph \<Rightarrow> ID set" where
  "graph_nodes g = fset (fmdom g)"

fun kind :: "Graph \<Rightarrow> ID \<Rightarrow> IRNode" where
  "kind g nid = n_kind(case fmlookup g nid of Some n \<Rightarrow> n | None \<Rightarrow> EmptyNode)"

fun inp :: "Graph \<Rightarrow> ID \<Rightarrow> ID list" where
  "inp g nid = n_inputs(case fmlookup g nid of Some n \<Rightarrow> n | None \<Rightarrow> EmptyNode)"

fun usages :: "Graph \<Rightarrow> ID \<Rightarrow> ID set" where
  "usages g nid = fset (ffilter (\<lambda> nid' . nid \<in> set(inp g nid')) (fmdom g))"

fun succ :: "Graph \<Rightarrow> ID \<Rightarrow> ID list" where
  "succ g nid = n_successors(case fmlookup g nid of Some n \<Rightarrow> n | None \<Rightarrow> EmptyNode)"

datatype IRGraph =
  Graph
    (g_ids: "ID set")
    (g_nodes: "ID \<Rightarrow> IRNode")
    (g_inputs: "InputEdges")
    (g_successors: "SuccessorEdges")
(*
  NOTES: from org.graalvm.compiler.graph.Graph
    * IRNode is actually a list ordered by registration time, but we abstract over that.
    * We ignore String name;
    * We ignore source positions.
    * We ignore cachedLeftNodes (but these are used for global-value-numbering).
    * TODO: add OptionValues?
  NOTES: from org.graalvm.compiler.graph.StructuredGraph
    * We ignore most of this for now, except start.
*)


(* Invariants for particular kinds of IRNodes. 
   TODO: see Node.verify() for more things we could check.
*)
fun wff_binary_node :: "ID list \<Rightarrow> ID list \<Rightarrow> bool" where
  "wff_binary_node inputs succs = (length inputs = 2 \<and> succs = [])"

fun wff_node :: "IRNode \<Rightarrow> ID list \<Rightarrow> ID list \<Rightarrow> bool" where
  "wff_node (ConstantNode _) inputs succs = (inputs = [] \<and> succs = [])" |
  "wff_node (ParameterNode _) inputs succs = (inputs = [] \<and> succs = [])" |
  "wff_node AddNode inputs succs = wff_binary_node inputs succs" |
  "wff_node SubNode inputs succs = wff_binary_node inputs succs" |
  "wff_node MulNode inputs succs = wff_binary_node inputs succs" |
  "wff_node IfNode inputs succs = (length inputs = 1 \<and> length succs = 2)" |
  "wff_node (ShortCircuitOrNode xneg yneg) inputs succs = (length inputs = 2 \<and> succs = [])" |
  "wff_node LogicNegationNode inputs succs = (length inputs = 1 \<and> succs = [])" | 
  "wff_node n inputs succs = True"


(* Usage function is the reverse of the 'inputs' edges. *)
fun g_usages :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "g_usages (Graph ids nodes inputs successors) n = {i. i \<in> ids \<and> n \<in> set(inputs i)}"

(* Predecessors function is the reverse of the 'successors' edges.
   The result should be empty or a singleton set.
*)
fun g_predecessor :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "g_predecessor (Graph ids nodes inputs successors) n = {i. i \<in> ids \<and> n \<in> set(successors i)}"


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
fun has_good_inputs :: "ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "has_good_inputs n (Graph ids nodes inputs successors) = (set(inputs n) \<subseteq> ids)"

fun has_good_successors :: "ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "has_good_successors n (Graph ids nodes inputs successors) = (set(successors n) \<subseteq> ids)"

fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph (Graph ids nodes inputs successors) = (
    0 \<in> ids \<and>
    nodes 0 = StartNode \<and>
    (\<forall> n. n \<in> ids \<longrightarrow> has_good_inputs n (Graph ids nodes inputs successors)) \<and>
    (\<forall> n. n \<in> ids \<longrightarrow> has_good_successors n (Graph ids nodes inputs successors)) \<and>
    (\<forall> n. n \<notin> ids \<longrightarrow> nodes n = StartNode) \<and>
    (\<forall> n. n \<notin> ids \<longrightarrow> successors n = []) \<and>
    (\<forall> n. n \<notin> ids \<longrightarrow> inputs n = []) \<and>
    (\<forall> n. n \<in> ids \<longrightarrow> wff_node (nodes n) (inputs n) (successors n))
  )
  "


(* Example 1: empty graph (just a start node) *)
lemma wff_empty: "wff_graph (Graph {0} (\<lambda>i.(StartNode)) (\<lambda>i.[]) (\<lambda>i.[]))"
  apply auto
  done


(* Example 2:
  public static int sq(int x) { return x * x; }

             [1 P(0)]
               \ /
  [0 Start]   [4 *]
       |      /
       V     /
      [5 Return]
*)
fun eg2_node :: "ID \<Rightarrow> IRNode" where
  "eg2_node i =
    (if i=5 then ReturnNode
     else if i=1 then ParameterNode 0
     else if i=4 then MulNode
     else StartNode)"

fun eg2_successors :: SuccessorEdges where
  "eg2_successors i = (if i=0 then [5] else [])"

fun eg2_inputs :: InputEdges where
  "eg2_inputs i = (if i=4 then [1,1] else if i=5 then [4] else [])"

definition eg2_sq :: IRGraph where
  "eg2_sq = Graph {0,1,4,5} eg2_node eg2_inputs eg2_successors"


(* Now check some basic properties of this example. *)
lemma wff_eg2_sq: "wff_graph eg2_sq"
  unfolding eg2_sq_def by simp

lemma "g_usages eg2_sq 1 = {4}"
  unfolding eg2_sq_def by simp

lemma "g_predecessor eg2_sq 5 = {0}"
  unfolding eg2_sq_def sorry

(* predecessor is always singleton or empty. *)
lemma "\<forall> n \<in> g_ids eg2_sq. card(g_predecessor eg2_sq n) \<le> 1"
  unfolding eg2_sq_def sorry

end

