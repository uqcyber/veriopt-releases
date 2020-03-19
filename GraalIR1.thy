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

datatype IRNode = 
    CallNode ID
  | PhiNode ID  (* TODO: subclasses GuardPhiNode, ValuePhiNode, MemoryPhiNode *)
  | AddNode ID
  | SwitchNode ID
  | KillingBeginNode ID
  | BeginNode ID  (* TODO: all the BeginStateSplitNode subclasses *)
  | StartNode ID
  | LoopEndNode ID
  | EndNode ID
  (* and hundreds of other Node subclasses!... *)

(* Next we need a predicate for each subclass.
   Like this?
*)
definition is_StartNode :: "IRNode \<Rightarrow> bool" where
  "is_StartNode node = (\<exists> id. node = (StartNode id))"
definition is_CallNode :: "IRNode \<Rightarrow> bool" where
  "is_CallNode node = (\<exists> id. node = (CallNode id))"
(* ... *)

(* These two kinds of functions will model our two kinds of edges. *)
type_synonym SuccessorEdges = "IRNode \<Rightarrow> IRNode list"
type_synonym InputEdges = "IRNode \<Rightarrow> IRNode list"

(* Here is the main Graal data structure - an entire IR Graph.
   TODO: is there a way of *naming* each component?  Records?
*)
datatype IRGraph =
  Graph
    "IRNode set" (* nodes *)
    "IRNode"  (* StartNode start *)
    "SuccessorEdges"
    "InputEdges"
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
*)
fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph (Graph nodes start successors inputs) = (
    is_StartNode start \<and>
    (\<forall> n. set(successors n) \<subseteq> nodes) \<and>
    (\<forall> n. set(inputs n) \<subseteq> nodes)
  )
  "

lemma wff_empty: "wff_graph (Graph {} (StartNode 0) (\<lambda>n.[]) (\<lambda>n.[]) )"
  apply(simp add: is_StartNode_def)
  done

end
