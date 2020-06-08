theory GraalIR1
imports Main
begin

(* The Graal IR 'Node' type is an abstract class with many subclasses.
   We define it as a datatype comprised of the *leaf* classes.
   If we need the intermediate classes (like FixedNode or FloatingNode), 
   we can define those as the union of the appropriate leaves.
*)

(* we need an infinite set of each kind of node object,
   so we simulate this by using int identifiers?
   Yuck.  This seems too low-level.
*)
type_synonym ID = "int"

datatype (discs_sels) IRNode = 
  CallNode ID
  | ConstantNode ID (intValue: int)  (* TODO: should be string *)
  | ParameterNode ID (index: int)
  | PhiNode ID  (* TODO: subclasses GuardPhiNode, ValuePhiNode, MemoryPhiNode *)
  | AddNode ID
  | SubNode ID
  | MulNode ID
  | SwitchNode ID
  | KillingBeginNode ID
  | BeginNode ID  (* TODO: all the BeginStateSplitNode subclasses (inc. StartNode) *)
  | StartNode ID
  | LoopEndNode ID
  | ReturnNode ID
  | EndNode ID
  (* and hundreds of other Node subclasses!... *)

(* Next we may want a predicate for each subclass.
   The '(discs_sels)' above automatically generates (is_StartNode _) etc.
   We can combine these to define similar predicates for abstract subclasses:
*)
definition is_BinaryArithNode :: "IRNode \<Rightarrow> bool" where
  "is_BinaryArithNode n = (is_AddNode n \<or> is_SubNode n)"


(* These two kinds of functions will model our two kinds of edges. *)
type_synonym SuccessorEdges = "IRNode \<Rightarrow> IRNode list"
type_synonym InputEdges = "IRNode \<Rightarrow> IRNode list"

(* Here is the main Graal data structure - an entire IR Graph.
   Note that we *name* each component - like a record.
*)
datatype IRGraph =
  Graph
    (gnodes: "IRNode set")
    (gstart: "IRNode")
    (gsuccessors: "SuccessorEdges")
    (ginputs: "InputEdges")
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
*)
fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph g = (
    is_StartNode (gstart g) \<and>
    (\<forall> n. n \<in> gnodes g \<longrightarrow> set(gsuccessors g n) \<subseteq> gnodes g) \<and>
    (\<forall> n. n \<in> gnodes g \<longrightarrow> set(ginputs g n) \<subseteq> gnodes g)
  )
  "
(* Alternative definition using pattern matching. 
fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph (Graph nodes start successors inputs) = (
    is_StartNode start \<and>
    (\<forall> n. n \<in> nodes \<longrightarrow> set(successors n) \<subseteq> nodes) \<and>
    (\<forall> n. n \<in> nodes \<longrightarrow> set(inputs n) \<subseteq> nodes)
  )
  "
*)


(* Example 1: empty graph (just a start node) *)
lemma wff_empty: "wff_graph (Graph {} (StartNode 0) (\<lambda>n.[]) (\<lambda>n.[]) )"
  apply(simp)
  done


(* Example 2:
  public static int sq(int x) { return x * x; }

             [1 P(0)]
                |
  [0 Start]   [4 *]
       \      /
      [5 Return]
*)
fun eg2_successors :: SuccessorEdges where
  "eg2_successors (StartNode _) = [ReturnNode 5]" |
  "eg2_successors other = []"

fun eg2_inputs :: InputEdges where
  "eg2_inputs (StartNode _)       = []" |
  "eg2_inputs (ParameterNode _ _) = []" |
  "eg2_inputs (MulNode _)         = [ParameterNode 1 0, ParameterNode 1 0]" |
  "eg2_inputs (ReturnNode _)      = [MulNode 4]" |
  "eg2_inputs _ = []"

definition eg2_sq :: IRGraph where
  "eg2_sq = Graph {StartNode 0, ParameterNode 1 0, MulNode 4, ReturnNode 5}
                  (StartNode 0) eg2_successors eg2_inputs"

lemma wff_eg2_sq: "wff_graph eg2_sq"
  apply (unfold eg2_sq_def)
  apply (simp)
  done

end

