section \<open>GraalVM graph representation\<close>

theory IRNodes
  imports 
    Main
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
type_synonym int32 = "int" (* while working changed from "32 word" *)
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
    (* NB. CallNode here includes CallTargetNode. *)
  | CallNode (ir_startNode:INPUT) (ir_arguments:"INPUT list") (ir_succ:"SUCC list")
  | NewInstanceNode (ir_className:string) (ir_stateBefore:INPUT_STATE) (ir_next:SUCC)
  | LoadFieldNode (ir_field:string) (ir_object:INPUT) (ir_next:SUCC)
  | StoreFieldNode (ir_field:string) (ir_object:INPUT) (ir_value:INPUT) (ir_stateAfter:"INPUT_STATE option") (ir_next:SUCC)
    (* these next two are special cases of Load/Store where isStatic() is true. *)
  | LoadStaticFieldNode (ir_field:string) (ir_clazz:string) (ir_next:SUCC)
  | StoreStaticFieldNode (ir_field:string) (ir_clazz:string) (ir_value:INPUT) (ir_next:SUCC)
  | FrameState (ir_outerFrameState:"INPUT_STATE option") (ir_values:"INPUT list") (* TODO: add monitorIds, virtualObjectMappings? *)
  | RefNode (ir_ref:ID) (* Proxy for another node *)
  (* Dummy node to not cause too much pain when switching to partial *)
  | NoNode 
  (* and hundreds of other Node subclasses!... *)
*)

(* nodeout: isabelle-datatypes *)
datatype (discs_sels) IRNode =
  AbsNode (ir_value: "INPUT") 
  | AbstractBeginNode (ir_next: "SUCC") 
  | AbstractEndNode 
  | AbstractLocalNode 
  | AbstractMergeNode (ir_ends: "INPUT_ASSOC list") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | AbstractNewArrayNode (ir_length: "INPUT") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | AbstractNewObjectNode (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | AccessFieldNode (ir_object_opt: "INPUT option") (ir_next: "SUCC") 
  | AddNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | AndNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | BeginNode (ir_next: "SUCC") 
  | BeginStateSplitNode (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | BinaryArithmeticNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | BinaryNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | ConditionalNode (ir_condition: "INPUT_COND") (ir_trueValue: "INPUT") (ir_falseValue: "INPUT") 
  | ConstantNode (ir_intValue: int32) 
  | ControlSplitNode 
  | DeoptimizingFixedWithNextNode (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | DynamicNewArrayNode (ir_elementType: "INPUT") (ir_length: "INPUT") (ir_voidClass_opt: "INPUT option") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | EndNode 
  | FixedNode 
  | FixedWithNextNode (ir_next: "SUCC") 
  | FloatingNode 
  | FrameState (ir_monitorIds: "INPUT_ASSOC list") (ir_outerFrameState_opt: "INPUT_STATE option") (ir_values_opt: "INPUT list option") (ir_virtualObjectMappings_opt: "INPUT_STATE list option") 
  | IfNode (ir_condition: "INPUT_COND") (ir_trueSuccessor: "SUCC") (ir_falseSuccessor: "SUCC") 
  | IntegerEqualsNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | IntegerLessThanNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | InvokeNode (ir_callTarget: "INPUT_EXT") (ir_classInit_opt: "INPUT option") (ir_stateDuring_opt: "INPUT_STATE option") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | KillingBeginNode (ir_next: "SUCC") 
  | LoadFieldNode (ir_field: string) (ir_object_opt: "INPUT option") (ir_next: "SUCC") 
  | LogicNegationNode (ir_value: "INPUT_COND") 
  | LoopBeginNode (ir_ends: "INPUT_ASSOC list") (ir_overflowGuard_opt: "INPUT_GUARD option") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | LoopEndNode (ir_loopBegin: "INPUT_ASSOC") 
  | LoopExitNode (ir_loopBegin: "INPUT_ASSOC") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | MergeNode (ir_ends: "INPUT_ASSOC list") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | MethodCallTargetNode (ir_targetMethod: string) (ir_arguments: "INPUT list") 
  | MulNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | NegateNode (ir_value: "INPUT") 
  | NewArrayNode (ir_length: "INPUT") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | NewInstanceNode (ir_instanceClass: string) (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | NotNode (ir_value: "INPUT") 
  | OrNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | ParameterNode (ir_index: nat) 
  | PhiNode (ir_merge: "INPUT_ASSOC") 
  | ProxyNode (ir_loopExit: "INPUT_ASSOC") 
  | ReturnNode (ir_result_opt: "INPUT option") (ir_memoryMap_opt: "INPUT_EXT option") 
  | ShortCircuitOrNode (ir_x: "INPUT_COND") (ir_y: "INPUT_COND") 
  | SignedDivNode (ir_x: "INPUT") (ir_y: "INPUT") (ir_zeroCheck_opt: "INPUT_GUARD option") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | StartNode (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | StoreFieldNode (ir_field: string) (ir_value: "INPUT") (ir_stateAfter_opt: "INPUT_STATE option") (ir_object_opt: "INPUT option") (ir_next: "SUCC") 
  | SubNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | SwitchNode (ir_value: "INPUT") (ir_successors: "SUCC list") 
  | UnaryArithmeticNode (ir_value: "INPUT") 
  | UnaryNode (ir_value: "INPUT") 
  | ValueNode 
  | ValuePhiNode (ir_values: "INPUT list") (ir_merge: "INPUT_ASSOC") 
  | ValueProxyNode (ir_value: "INPUT") (ir_loopExit: "INPUT_ASSOC") 
  | XorNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | NoNode
(* nodeout *)

  (* Manually added *)
  | CallNode (ir_startNode:INPUT) (ir_arguments:"INPUT list") (ir_succ:"SUCC list")
  | RefNode (ir_ref:ID)

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

fun is_UnaryArithNode :: "IRNode \<Rightarrow> bool" where
  "is_UnaryArithNode (AbsNode _) = True" |
  "is_UnaryArithNode (NegateNode _) = True" |
  "is_UnaryArithNode _ = False"

fun is_CompareNode :: "IRNode \<Rightarrow> bool" where
  "is_CompareNode (IntegerEqualsNode x y) = True" |
  "is_CompareNode (IntegerLessThanNode x y) = True" |
  "is_CompareNode _ = False"

fun is_PhiNode :: "IRNode \<Rightarrow> bool" where
  "is_PhiNode (PhiNode _) = True" |
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
(*  "is_sequential_node (RefNode _) = True" | *)
  "is_sequential_node n = is_merge_node n"

fun is_end_node :: "IRNode \<Rightarrow> bool" where
  "is_end_node (EndNode) = True" |
  "is_end_node (LoopEndNode _) = True" |
  "is_end_node _ = False"


(* Surely this must exist already?  I cannot find it in option or list theory. *)
fun opt_to_list :: "'a option \<Rightarrow> 'a list" where
  "opt_to_list None = []" |
  "opt_to_list (Some v) = [v]"

fun opt_list_to_list :: "'a list option \<Rightarrow> 'a list" where
  "opt_list_to_list None = []" |
  "opt_list_to_list (Some x) = x"

(* We also define a generic 'inputs_of' for all kinds of nodes. *)
(* nodeout: isabelle-inputs *)
fun inputs_of :: "IRNode \<Rightarrow> ID list" where
  "inputs_of (AbsNode value) = [value]" |
  "inputs_of (AbstractBeginNode next) = []" |
  "inputs_of (AbstractEndNode) = []" |
  "inputs_of (AbstractLocalNode) = []" |
  "inputs_of (AbstractMergeNode ends stateAfter next) = ends @ (opt_to_list stateAfter)" |
  "inputs_of (AbstractNewArrayNode length0 stateBefore next) = [length0] @ (opt_to_list stateBefore)" |
  "inputs_of (AbstractNewObjectNode stateBefore next) = (opt_to_list stateBefore)" |
  "inputs_of (AccessFieldNode object next) = (opt_to_list object)" |
  "inputs_of (AddNode x y) = [x, y]" |
  "inputs_of (AndNode x y) = [x, y]" |
  "inputs_of (BeginNode next) = []" |
  "inputs_of (BeginStateSplitNode stateAfter next) = (opt_to_list stateAfter)" |
  "inputs_of (BinaryArithmeticNode x y) = [x, y]" |
  "inputs_of (BinaryNode x y) = [x, y]" |
  "inputs_of (ConditionalNode condition trueValue falseValue) = [condition, trueValue, falseValue]" |
  "inputs_of (ConstantNode intValue) = []" |
  "inputs_of (ControlSplitNode) = []" |
  "inputs_of (DeoptimizingFixedWithNextNode stateBefore next) = (opt_to_list stateBefore)" |
  "inputs_of (DynamicNewArrayNode elementType length0 voidClass stateBefore next) = [elementType, length0] @ (opt_to_list voidClass) @ (opt_to_list stateBefore)" |
  "inputs_of (EndNode) = []" |
  "inputs_of (FixedNode) = []" |
  "inputs_of (FixedWithNextNode next) = []" |
  "inputs_of (FloatingNode) = []" |
  "inputs_of (FrameState monitorIds outerFrameState values virtualObjectMappings) = monitorIds @ (opt_to_list outerFrameState) @ (opt_list_to_list values) @ (opt_list_to_list virtualObjectMappings)" |
  "inputs_of (IfNode condition trueSuccessor falseSuccessor) = [condition]" |
  "inputs_of (IntegerEqualsNode x y) = [x, y]" |
  "inputs_of (IntegerLessThanNode x y) = [x, y]" |
  "inputs_of (InvokeNode callTarget classInit stateDuring stateAfter next) = [callTarget] @ (opt_to_list classInit) @ (opt_to_list stateDuring) @ (opt_to_list stateAfter)" |
  "inputs_of (KillingBeginNode next) = []" |
  "inputs_of (LoadFieldNode field object next) = (opt_to_list object)" |
  "inputs_of (LogicNegationNode value) = [value]" |
  "inputs_of (LoopBeginNode ends overflowGuard stateAfter next) = ends @ (opt_to_list overflowGuard) @ (opt_to_list stateAfter)" |
  "inputs_of (LoopEndNode loopBegin) = [loopBegin]" |
  "inputs_of (LoopExitNode loopBegin stateAfter next) = [loopBegin] @ (opt_to_list stateAfter)" |
  "inputs_of (MergeNode ends stateAfter next) = ends @ (opt_to_list stateAfter)" |
  "inputs_of (MethodCallTargetNode targetMethod arguments) = arguments" |
  "inputs_of (MulNode x y) = [x, y]" |
  "inputs_of (NegateNode value) = [value]" |
  "inputs_of (NewArrayNode length0 stateBefore next) = [length0] @ (opt_to_list stateBefore)" |
  "inputs_of (NewInstanceNode instanceClass stateBefore next) = (opt_to_list stateBefore)" |
  "inputs_of (NotNode value) = [value]" |
  "inputs_of (OrNode x y) = [x, y]" |
  "inputs_of (ParameterNode index) = []" |
  "inputs_of (PhiNode merge) = [merge]" |
  "inputs_of (ProxyNode loopExit) = [loopExit]" |
  "inputs_of (ReturnNode result memoryMap) = (opt_to_list result) @ (opt_to_list memoryMap)" |
  "inputs_of (ShortCircuitOrNode x y) = [x, y]" |
  "inputs_of (SignedDivNode x y zeroCheck stateBefore next) = [x, y] @ (opt_to_list zeroCheck) @ (opt_to_list stateBefore)" |
  "inputs_of (StartNode stateAfter next) = (opt_to_list stateAfter)" |
  "inputs_of (StoreFieldNode field value stateAfter object next) = [value] @ (opt_to_list stateAfter) @ (opt_to_list object)" |
  "inputs_of (SubNode x y) = [x, y]" |
  "inputs_of (SwitchNode value successors) = [value]" |
  "inputs_of (UnaryArithmeticNode value) = [value]" |
  "inputs_of (UnaryNode value) = [value]" |
  "inputs_of (ValueNode) = []" |
  "inputs_of (ValuePhiNode values merge) = [merge] @ values" |
  "inputs_of (ValueProxyNode value loopExit) = [value, loopExit]" |
  "inputs_of (XorNode x y) = [x, y]" |
  "inputs_of (NoNode) = []"|
(* nodeout *)

  "inputs_of (RefNode ref) = [ref]" |
  "inputs_of (CallNode startNode arguments succ) = [startNode] @ arguments" 

value "inputs_of (FrameState [4] (Some 3) (Some [5, 7]) None)"
value "inputs_of (FrameState [4] None (Some [7]) (Some [3]))"

(* nodeout: isabelle-succs *)
fun successors_of :: "IRNode \<Rightarrow> ID list" where
  "successors_of (AbsNode value) = []" |
  "successors_of (AbstractBeginNode next) = [next]" |
  "successors_of (AbstractEndNode) = []" |
  "successors_of (AbstractLocalNode) = []" |
  "successors_of (AbstractMergeNode ends stateAfter next) = [next]" |
  "successors_of (AbstractNewArrayNode length0 stateBefore next) = [next]" |
  "successors_of (AbstractNewObjectNode stateBefore next) = [next]" |
  "successors_of (AccessFieldNode object next) = [next]" |
  "successors_of (AddNode x y) = []" |
  "successors_of (AndNode x y) = []" |
  "successors_of (BeginNode next) = [next]" |
  "successors_of (BeginStateSplitNode stateAfter next) = [next]" |
  "successors_of (BinaryArithmeticNode x y) = []" |
  "successors_of (BinaryNode x y) = []" |
  "successors_of (ConditionalNode condition trueValue falseValue) = []" |
  "successors_of (ConstantNode intValue) = []" |
  "successors_of (ControlSplitNode) = []" |
  "successors_of (DeoptimizingFixedWithNextNode stateBefore next) = [next]" |
  "successors_of (DynamicNewArrayNode elementType length0 voidClass stateBefore next) = [next]" |
  "successors_of (EndNode) = []" |
  "successors_of (FixedNode) = []" |
  "successors_of (FixedWithNextNode next) = [next]" |
  "successors_of (FloatingNode) = []" |
  "successors_of (FrameState monitorIds outerFrameState values virtualObjectMappings) = []" |
  "successors_of (IfNode condition trueSuccessor falseSuccessor) = [trueSuccessor, falseSuccessor]" |
  "successors_of (IntegerEqualsNode x y) = []" |
  "successors_of (IntegerLessThanNode x y) = []" |
  "successors_of (InvokeNode callTarget classInit stateDuring stateAfter next) = [next]" |
  "successors_of (KillingBeginNode next) = [next]" |
  "successors_of (LoadFieldNode field object next) = [next]" |
  "successors_of (LogicNegationNode value) = []" |
  "successors_of (LoopBeginNode ends overflowGuard stateAfter next) = [next]" |
  "successors_of (LoopEndNode loopBegin) = []" |
  "successors_of (LoopExitNode loopBegin stateAfter next) = [next]" |
  "successors_of (MergeNode ends stateAfter next) = [next]" |
  "successors_of (MethodCallTargetNode targetMethod arguments) = []" |
  "successors_of (MulNode x y) = []" |
  "successors_of (NegateNode value) = []" |
  "successors_of (NewArrayNode length0 stateBefore next) = [next]" |
  "successors_of (NewInstanceNode instanceClass stateBefore next) = [next]" |
  "successors_of (NotNode value) = []" |
  "successors_of (OrNode x y) = []" |
  "successors_of (ParameterNode index) = []" |
  "successors_of (PhiNode merge) = []" |
  "successors_of (ProxyNode loopExit) = []" |
  "successors_of (ReturnNode result memoryMap) = []" |
  "successors_of (ShortCircuitOrNode x y) = []" |
  "successors_of (SignedDivNode x y zeroCheck stateBefore next) = [next]" |
  "successors_of (StartNode stateAfter next) = [next]" |
  "successors_of (StoreFieldNode field value stateAfter object next) = [next]" |
  "successors_of (SubNode x y) = []" |
  "successors_of (SwitchNode value successors) = successors" |
  "successors_of (UnaryArithmeticNode value) = []" |
  "successors_of (UnaryNode value) = []" |
  "successors_of (ValueNode) = []" |
  "successors_of (ValuePhiNode values merge) = []" |
  "successors_of (ValueProxyNode value loopExit) = []" |
  "successors_of (XorNode x y) = []" |
  "successors_of (NoNode) = []"|
(* nodeout *)

  "successors_of (RefNode ref) = []" |
  "successors_of (CallNode startNode arguments succ) = succ"

end

