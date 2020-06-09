theory GraalIR3_exprs
imports Main
begin

(* This is a theory of GraalVM IR graphs that uses numbered nodes,
   but represents expressions by trees (copied from Brae's thesis).

   The Graal IR 'Node' type is an abstract class with many subclasses.
   We define it as a datatype comprised of the *leaf* classes.
   If we need the intermediate classes (like FixedNode or FloatingNode), 
   we can define those as the union of the appropriate leaves.
*)

datatype Value =
  UndefinedValue |
  IntegerValue int | 
  BooleanValue bool |
  StringValue string

datatype UnaryOp =
  AbsOp |
  MinusOp |
  NotOp

datatype BinaryOp =
  AddOp |
  SubOp |
  MulOp |
  DivOp |   (* Note: this is within a FixedBinaryNode *)
  EqualOp |
  LessOp |
  AndOp |
  OrOp |
  XorOp

datatype ExprNode =
  ConstNode Value |
  ParameterNode (index: int) |  (* added *)
  BinaryNode BinaryOp ExprNode ExprNode |
  UnaryNode UnaryOp ExprNode |
  LookupNode String.string |
  ConditionalNode ExprNode ExprNode ExprNode
(* TODO:
  | CallNode
  | PhiNode   TODO: subclasses GuardPhiNode, ValuePhiNode, MemoryPhiNode 
*)

(* TODO: change this from continuation semantics to an IRNode graph? *)
datatype ControlNode =
  EndNode |
  IfNode ExprNode ControlNode ControlNode |
  WhileNode ExprNode ControlNode ControlNode |
  AssignNode String.string ExprNode ControlNode |
  WriteNode ExprNode ControlNode


(* To identify each Node, we use a simple natural number index.
   Zero is always the start node in a graph.
*)
type_synonym ID = "nat"

datatype (discs_sels) IRNode =
  FloatingNode (result: ExprNode)
  | SwitchNode
  | KillingBeginNode
  | BeginNode  (* TODO: all the BeginStateSplitNode subclasses (inc. StartNode) *)
  | StartNode
  | LoopEndNode
  | ReturnNode (result: ExprNode)
  | EndNode
  (* and about 100 other non-floating Node subclasses!... *)


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

             {1 P(0)}
                \/
  [0 Start]   {4 *}
       \       /
      [5 Return]
*)
fun eg2_node :: "ID \<Rightarrow> IRNode" where
  "eg2_node i =
    (if i=0 then StartNode
     else ReturnNode (BinaryNode MulOp (ParameterNode 0) (ParameterNode 0)))"

fun eg2_successors :: SuccessorEdges where
  "eg2_successors i = (if i=0 then [5] else [])"

fun eg2_inputs :: InputEdges where
  "eg2_inputs i = []"

definition eg2_sq :: IRGraph where
  "eg2_sq = Graph {0,5} eg2_node eg2_successors eg2_inputs"

lemma wff_eg2_sq: "wff_graph eg2_sq"
  apply (unfold eg2_sq_def)
  apply (simp)
  done

end

