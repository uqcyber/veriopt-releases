theory GraalIR1_fromID
imports Main
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
  CallNode
  | ConstantNode (intValue: int)  (* TODO: should be string *)
  | ParameterNode (index: int)
  | PhiNode  (* TODO: subclasses GuardPhiNode, ValuePhiNode, MemoryPhiNode *)
  | AddNode
  | SubNode
  | MulNode
  | SwitchNode
  | KillingBeginNode
  | BeginNode  (* TODO: all the BeginStateSplitNode subclasses (inc. StartNode) *)
  | StartNode
  | LoopEndNode
  | ReturnNode
  | EndNode
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
datatype IRGraph =
  Graph
    (g_ids: "ID set")
    (g_node: "ID \<Rightarrow> IRNode")
    (g_successors: "SuccessorEdges")
    (g_inputs: "InputEdges")
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


(* First well-formedness predicate for IR graphs.
   This function uses field names.
*
fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph g = (
    0 \<in> g_ids g \<and>
    g_node g 0 = StartNode \<and>
    (\<forall> n. n \<in> g_ids g \<longrightarrow> set(g_successors g n) \<subseteq> g_ids g) \<and>
    (\<forall> n. n \<in> g_ids g \<longrightarrow> set(g_inputs g n) \<subseteq> g_ids g)
  )
  "
*)
(* Alternative definition using pattern matching. *)
fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph (Graph ids nodes successors inputs) = (
    0 \<in> ids \<and>
    nodes 0 = StartNode \<and>
    (\<forall> n. n \<in> ids \<longrightarrow> set(successors n) \<subseteq> ids) \<and>
    (\<forall> n. n \<in> ids \<longrightarrow> set(inputs n) \<subseteq> ids)
  )
  "



(* Example 1: empty graph (just a start node) *)
lemma wff_empty: "wff_graph (Graph {0} (\<lambda>i.(StartNode)) (\<lambda>i.[]) (\<lambda>i.[]))"
  apply auto
  done


(* Example 2:
  public static int sq(int x) { return x * x; }

             [1 P(0)]
                |
  [0 Start]   [4 *]
       \      /
      [5 Return]
*)
fun eg2_node :: "ID \<Rightarrow> IRNode" where
  "eg2_node i =
    (if i=0 then StartNode
     else if i=1 then ParameterNode 0
     else if i=4 then MulNode
     else ReturnNode)"

fun eg2_successors :: SuccessorEdges where
  "eg2_successors i = (if i=0 then [5] else [])"

fun eg2_inputs :: InputEdges where
  "eg2_inputs i = (if i=4 then [1,1] else if i=5 then [4] else [])"

definition eg2_sq :: IRGraph where
  "eg2_sq = Graph {0,1,4,5} eg2_node eg2_successors eg2_inputs"

lemma wff_eg2_sq: "wff_graph eg2_sq"
  apply (unfold eg2_sq_def)
  apply (simp)
  done

end

