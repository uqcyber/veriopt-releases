section \<open>GraalVM graph representation\<close>

theory IRNodes
  imports 
    Main
    "HOL-Word.More_Word"
begin

(* This is a theory of GraalVM IR graphs that uses numbered nodes,
   but where each kind of node defines (and names) its own
   input and successor edges.

   This implies many of the invariants that were needed before.
*)

(* To identify each Node, we use a simple natural number index.
   Zero is always the start node in a graph.
   For human readability, within nodes we write 
   INPUT (or special case thereof) instead of ID for input edges, and
   SUCC instead of ID for control-flow successor edges.
   Optional edges are handled as "INPUT option" etc. 
*)
type_synonym int32 = "32 word"
type_synonym ID = "nat"
type_synonym INPUT = "ID"   (* InputType.Value is the default *)
type_synonym INPUT_ASSOC = "ID" (* InputType.Association *)
type_synonym INPUT_STATE = "ID" (* InputType.State *)
type_synonym INPUT_GUARD = "ID" (* InputType.Guard *)
type_synonym INPUT_COND = "ID"  (* InputType.Condition *)
type_synonym INPUT_EXT = "ID"  (* InputType.Extension *)
type_synonym SUCC = "ID"

(* These IR nodes are roughly based on the leaf Graal Java classes.
   Field names are generally the same, but prefixed with "ir_"
   (because selector names have global scope in Isabelle, and 
    never being able to use 'x' or 'y' again would be unacceptable).
*)
datatype (discs_sels) IRNode =
  (* FloatingNode subclasses (with no successors)
     ----------------------------------------- *)
  ConstantNode (ir_intValue: int32)  (* TODO: value should be a Java Constant object *)
  | ParameterNode (ir_index:nat)
  | PhiNode (ir_merge:INPUT_ASSOC) (ir_values:"INPUT list") (* not used? *)
  | ValuePhiNode (ir_merge:INPUT_ASSOC) (ir_inputs:"INPUT list")
  | ValueProxyNode (ir_loopExit:INPUT_ASSOC) (ir_value:INPUT)
  (* UnaryArithmeticNode subclasses *)
  | AbsNode (ir_value:INPUT)
  | NegateNode (ir_value:INPUT)
  (* BinaryArithmeticNode subclasses *)
  | AddNode (ir_x:INPUT) (ir_y:INPUT)
  | SubNode (ir_x:INPUT) (ir_y:INPUT)
  | MulNode (ir_x:INPUT) (ir_y:INPUT)
  | AndNode (ir_x:INPUT) (ir_y:INPUT)
  | OrNode  (ir_x:INPUT) (ir_y:INPUT)
  | XorNode (ir_x:INPUT) (ir_y:INPUT)
  (* CompareNode subclasses *)
  | IntegerEqualsNode (ir_x:INPUT) (ir_y:INPUT)
  | IntegerLessThanNode (ir_x:INPUT) (ir_y:INPUT)
  (* others *)
  | ConditionalNode (ir_condition:INPUT_COND) (ir_trueValue:INPUT) (ir_falseValue:INPUT)
(* Ian thinks xNegated and yNegated are a hack to be avoided *)
  | ShortCircuitOrNode (ir_x:INPUT_COND) (ir_y:INPUT_COND) (* TODO: add? (ir_xNegated:bool) (ir_yNegated:bool)  double shortCircuitProbability; *)
  | LogicNegationNode (ir_value:INPUT_COND)
  (* Control-flow (fixed) nodes
     ------------------ *)
  | SwitchNode (ir_value:INPUT) (ir_successors:"SUCC list")
  | IfNode (ir_condition:INPUT_COND) (ir_trueSuccessor:SUCC) (ir_falseSuccessor:SUCC) (* TODO: add field: double trueSuccessorProbability; *)
  | KillingBeginNode (ir_next:SUCC)
  | BeginNode (ir_next:SUCC)
  | StartNode (ir_stateAfter:"INPUT_STATE option") (ir_next:SUCC)
  | EndNode
  | LoopBeginNode (ir_stateAfter:"INPUT_STATE option") (ir_overflowGuard:"INPUT_GUARD option") (ir_ends:"INPUT_ASSOC list") (ir_next:SUCC)
  | LoopEndNode (ir_loopBegin:INPUT_ASSOC)
  | LoopExitNode (ir_loopBegin:INPUT_ASSOC) (ir_stateAfter:"INPUT_STATE option") (ir_next:SUCC)
  | MergeNode (ir_stateAfter:"INPUT_STATE option") (ir_ends:"INPUT_ASSOC list") (ir_next:SUCC)
  | ReturnNode (ir_result:"INPUT option") (ir_memoryMap:"INPUT_EXT option")
  | CallNode (ir_startNode:INPUT) (ir_children:"SUCC list")
  | NewInstanceNode (ir_className:string) (ir_stateBefore:INPUT_STATE) (ir_next:SUCC)
  | LoadFieldNode (ir_field:string) (ir_object:INPUT) (ir_next:SUCC)
  | StoreFieldNode (ir_field:string) (ir_object:INPUT) (ir_value:INPUT) (ir_stateAfter:"INPUT_STATE option") (ir_next:SUCC)
    (* these next two are special cases of Load/Store where isStatic() is true. *)
  | LoadStaticFieldNode (ir_field:string) (ir_clazz:string) (ir_next:SUCC)
  | StoreStaticFieldNode (ir_field:string) (ir_clazz:string) (ir_value:INPUT) (ir_next:SUCC)
  | FrameState (ir_outerFrameState:"INPUT_STATE option") (* TODO: add values, monitorIds, virtualObjectMappings? *)
  | RefNode (ir_ref:ID) (* Proxy for another node *)
  (* Dummy node to not cause too much pain when switching to partial *)
  | NoNode 
  (* and hundreds of other Node subclasses!... *)

(* Next we may want a predicate for some abstract subclasses?
   The '(discs_sels)' above automatically generates (is_StartNode _) etc.
*)
fun is_BinaryArithNode :: "IRNode \<Rightarrow> bool" where
  "is_BinaryArithNode (AddNode _ _) = True" |
  "is_BinaryArithNode (SubNode _ _) = True" |
  "is_BinaryArithNode (MulNode _ _) = True" |
  "is_BinaryArithNode (AndNode _ _) = True" |
  "is_BinaryArithNode (OrNode _ _) = True" |
  "is_BinaryArithNode (XorNode _ _) = True" |
  "is_BinaryArithNode _ = False"

fun is_PhiNode :: "IRNode \<Rightarrow> bool" where
  "is_PhiNode (PhiNode _ _) = True" |
  "is_PhiNode (ValuePhiNode _ _) = True" |
  "is_PhiNode _ = False"

fun is_merge_node :: "IRNode \<Rightarrow> bool" where
  "is_merge_node (MergeNode _ _ _) = True" |
  "is_merge_node (LoopBeginNode _ _ _ _) = True" |
  "is_merge_node _ = False"

fun is_sequential_node :: "IRNode \<Rightarrow> bool" where
  "is_sequential_node (StartNode _ _) = True" |
  "is_sequential_node (BeginNode _) = True" |
  "is_sequential_node (LoopBeginNode _ _ _ _) = True" |
  "is_sequential_node (LoopExitNode _ _ _) = True" |
  "is_sequential_node n = is_merge_node n"

fun is_end_node :: "IRNode \<Rightarrow> bool" where
  "is_end_node (EndNode) = True" |
  "is_end_node (LoopEndNode _) = True" |
  "is_end_node _ = False"


(* Surely this must exist already?  I cannot find it in option or list theory. *)
fun opt_to_list :: "'a option \<Rightarrow> 'a list" where
  "opt_to_list None = []" |
  "opt_to_list (Some v) = [v]"

(* We also define a generic 'inputs_of' for all kinds of nodes. *)
fun inputs_of :: "IRNode \<Rightarrow> ID list" where
  "inputs_of (ConstantNode _) = []" |
  "inputs_of (ParameterNode _) = []" |
  "inputs_of (PhiNode merge vals) = merge # vals" |
  "inputs_of (ValuePhiNode merge inputs) = merge # inputs" |
  "inputs_of (ValueProxyNode loopExit val) = [loopExit, val]" |
  "inputs_of (AbsNode val) = [val]" |
  "inputs_of (NegateNode val) = [val]" |
  "inputs_of (AddNode x y) = [x, y]" |
  "inputs_of (SubNode x y) = [x, y]" |
  "inputs_of (MulNode x y) = [x, y]" |
  "inputs_of (AndNode x y) = [x, y]" |
  "inputs_of (OrNode  x y) = [x, y]" |
  "inputs_of (XorNode x y) = [x, y]" |
  "inputs_of (IntegerEqualsNode x y) = [x, y]" |
  "inputs_of (IntegerLessThanNode x y) = [x, y]" |
  "inputs_of (ConditionalNode condition trueVal falseVal) = [condition, trueVal, falseVal]" |
  "inputs_of (ShortCircuitOrNode x y) = [x, y]" |
  "inputs_of (LogicNegationNode val) = [val]" |
  "inputs_of (SwitchNode val _) = [val]" |
  "inputs_of (IfNode condition _ _) = [condition]" |
  "inputs_of (KillingBeginNode _) = []" |
  "inputs_of (BeginNode _) = []" |
  "inputs_of (StartNode after _) = opt_to_list after" |
  "inputs_of (EndNode) = []" |
  "inputs_of (LoopBeginNode after over ends _) = opt_to_list after @ opt_to_list over @ ends" |
  "inputs_of (LoopEndNode loopBegin) = [loopBegin]" |
  "inputs_of (LoopExitNode loopBegin after _) = [loopBegin] @ opt_to_list after" |
  "inputs_of (MergeNode after ends _) = opt_to_list after @ ends" |
  "inputs_of (ReturnNode result mem) = opt_to_list result @ opt_to_list mem" |
  "inputs_of (CallNode startNode _) = [startNode]" |
  "inputs_of (NewInstanceNode _ before _) = [before]" |
  "inputs_of (LoadFieldNode _ object _) = [object]" |
  "inputs_of (StoreFieldNode _ object val after _) = [object, val] @ opt_to_list after" |
  "inputs_of (LoadStaticFieldNode _ _ _) = []" |
  "inputs_of (StoreStaticFieldNode _ _ val _) = [val]" |
  "inputs_of (FrameState ofs) =  opt_to_list ofs" |
  "inputs_of (RefNode x) = [x]" |
  "inputs_of NoNode = []"


value "inputs_of (FrameState (Some 3))"
value "inputs_of (FrameState None)"

fun successors_of :: "IRNode \<Rightarrow> ID list" where
  "successors_of (IfNode _ t f) = [t, f]" |
  "successors_of (KillingBeginNode nxt) = [nxt]" |
  "successors_of (BeginNode nxt) = [nxt]" |
  "successors_of (StartNode _ nxt) = [nxt]" |
  "successors_of (EndNode) = []" |
  "successors_of (LoopBeginNode _ _ _ nxt) = [nxt]" |
  "successors_of (LoopEndNode _) = []" |
  "successors_of (LoopExitNode _ _ nxt) = [nxt]" |
  "successors_of (MergeNode _ _ nxt) = [nxt]" |
  "successors_of (ReturnNode _ _) = []" |
  "successors_of (CallNode _ children) = children" |
  "successors_of (NewInstanceNode _ _ nxt) = [nxt]" |
  "successors_of (LoadFieldNode _ _ nxt) = [nxt]" |
  "successors_of (StoreFieldNode _ _ _ _ nxt) = [nxt]" |
  "successors_of (LoadStaticFieldNode _ _ nxt) = [nxt]" |
  "successors_of (StoreStaticFieldNode _ _ _ nxt) = [nxt]" |
  "successors_of _ = []"
end

