theory FullIRNodes
  imports 
    Main
    "HOL-Word.More_Word"
begin

type_synonym int32 = "32 word"
type_synonym ID = "nat"
type_synonym INPUT = "ID"
type_synonym INPUT_ASSOC = "ID"
type_synonym INPUT_STATE = "ID"
type_synonym INPUT_GUARD = "ID"
type_synonym INPUT_COND = "ID"
type_synonym INPUT_EXT = "ID"
type_synonym INPUT_MEM = "ID"
type_synonym INPUT_ANCHOR = "ID"
type_synonym SUCC = "ID"

datatype (discs_sels) IRNode =
  NegateNode (ir_value: "INPUT") 
  | EndNode 
  | AbstractMergeNode (ir_ends: "INPUT_ASSOC list") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | BeginStateSplitNode (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | OrNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | ValueNode 
  | NewInstanceNode (ir_instanceClass: string) (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | ConditionalNode (ir_condition: "INPUT_COND") (ir_trueValue: "INPUT") (ir_falseValue: "INPUT") 
  | StartNode (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | IfNode (ir_condition: "INPUT_COND") (ir_trueSuccessor: "SUCC") (ir_falseSuccessor: "SUCC") 
  | FloatingNode 
  | SubNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | BeginNode (ir_next: "SUCC") 
  | UnaryNode (ir_value: "INPUT") 
  | NotNode (ir_value: "INPUT") 
  | ProxyNode (ir_loopExit: "INPUT_ASSOC") 
  | FrameState (ir_monitorIds: "INPUT_ASSOC list") (ir_outerFrameState_opt: "INPUT_STATE option") (ir_values_opt: "INPUT option list") (ir_virtualObjectMappings_opt: "INPUT_STATE option list") 
  | FixedWithNextNode (ir_next: "SUCC") 
  | StoreFieldNode (ir_field: string) (ir_value: "INPUT") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | UnaryArithmeticNode (ir_value: "INPUT") 
  | AbstractNewObjectNode (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | BinaryNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | LoopBeginNode (ir_ends: "INPUT_ASSOC list") (ir_overflowGuard_opt: "INPUT_GUARD option") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | ConstantNode (ir_intValue: int32) 
  | MulNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | AbstractEndNode 
  | NewArrayNode (ir_length: "INPUT") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | ControlSplitNode 
  | BinaryArithmeticNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | LoopEndNode (ir_loopBegin: "INPUT_ASSOC") 
  | DeoptimizingFixedWithNextNode (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | LoopExitNode (ir_loopBegin: "INPUT_ASSOC") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | AbstractBeginNode (ir_next: "SUCC") 
  | AndNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | ValuePhiNode (ir_values: "INPUT list") (ir_merge: "INPUT_ASSOC") 
  | AddNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | AbstractNewArrayNode (ir_length: "INPUT") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | XorNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | DynamicNewArrayNode (ir_length: "INPUT") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | PhiNode (ir_merge: "INPUT_ASSOC") 
  | AccessFieldNode (ir_next: "SUCC") 
  | LoadFieldNode (ir_field: string) (ir_next: "SUCC") 
  | AbsNode (ir_value: "INPUT") 
  | MergeNode (ir_ends: "INPUT_ASSOC list") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | FixedNode 
  | NoNode


fun is_VirtualState :: "IRNode \<Rightarrow> bool" where
  "is_VirtualState (FrameState _ _ _ _) = True" |
  "is_VirtualState _ = False"

fun is_ProxyNode :: "IRNode \<Rightarrow> bool" where
  "is_ProxyNode (ProxyNode _) = True" |
  "is_ProxyNode _ = False"

fun is_AccessFieldNode :: "IRNode \<Rightarrow> bool" where
  "is_AccessFieldNode (StoreFieldNode _ _ _ _) = True" |
  "is_AccessFieldNode (AccessFieldNode _) = True" |
  "is_AccessFieldNode (LoadFieldNode _ _) = True" |
  "is_AccessFieldNode _ = False"

fun is_BinaryArithmeticNode :: "IRNode \<Rightarrow> bool" where
  "is_BinaryArithmeticNode (OrNode _ _) = True" |
  "is_BinaryArithmeticNode (SubNode _ _) = True" |
  "is_BinaryArithmeticNode (MulNode _ _) = True" |
  "is_BinaryArithmeticNode (BinaryArithmeticNode _ _) = True" |
  "is_BinaryArithmeticNode (AndNode _ _) = True" |
  "is_BinaryArithmeticNode (AddNode _ _) = True" |
  "is_BinaryArithmeticNode (XorNode _ _) = True" |
  "is_BinaryArithmeticNode _ = False"

fun is_StoreFieldNode :: "IRNode \<Rightarrow> bool" where
  "is_StoreFieldNode (StoreFieldNode _ _ _ _) = True" |
  "is_StoreFieldNode _ = False"

fun is_AbsNode :: "IRNode \<Rightarrow> bool" where
  "is_AbsNode (AbsNode _) = True" |
  "is_AbsNode _ = False"

fun is_AndNode :: "IRNode \<Rightarrow> bool" where
  "is_AndNode (AndNode _ _) = True" |
  "is_AndNode _ = False"

fun is_ConditionalNode :: "IRNode \<Rightarrow> bool" where
  "is_ConditionalNode (ConditionalNode _ _ _) = True" |
  "is_ConditionalNode _ = False"

fun is_AddNode :: "IRNode \<Rightarrow> bool" where
  "is_AddNode (AddNode _ _) = True" |
  "is_AddNode _ = False"

fun is_ValueNode :: "IRNode \<Rightarrow> bool" where
  "is_ValueNode (NegateNode _) = True" |
  "is_ValueNode (EndNode) = True" |
  "is_ValueNode (AbstractMergeNode _ _ _) = True" |
  "is_ValueNode (BeginStateSplitNode _ _) = True" |
  "is_ValueNode (OrNode _ _) = True" |
  "is_ValueNode (ValueNode) = True" |
  "is_ValueNode (NewInstanceNode _ _ _) = True" |
  "is_ValueNode (ConditionalNode _ _ _) = True" |
  "is_ValueNode (StartNode _ _) = True" |
  "is_ValueNode (IfNode _ _ _) = True" |
  "is_ValueNode (FloatingNode) = True" |
  "is_ValueNode (SubNode _ _) = True" |
  "is_ValueNode (BeginNode _) = True" |
  "is_ValueNode (UnaryNode _) = True" |
  "is_ValueNode (NotNode _) = True" |
  "is_ValueNode (ProxyNode _) = True" |
  "is_ValueNode (FixedWithNextNode _) = True" |
  "is_ValueNode (StoreFieldNode _ _ _ _) = True" |
  "is_ValueNode (UnaryArithmeticNode _) = True" |
  "is_ValueNode (AbstractNewObjectNode _ _) = True" |
  "is_ValueNode (BinaryNode _ _) = True" |
  "is_ValueNode (LoopBeginNode _ _ _ _) = True" |
  "is_ValueNode (ConstantNode _) = True" |
  "is_ValueNode (MulNode _ _) = True" |
  "is_ValueNode (AbstractEndNode) = True" |
  "is_ValueNode (NewArrayNode _ _ _) = True" |
  "is_ValueNode (ControlSplitNode) = True" |
  "is_ValueNode (BinaryArithmeticNode _ _) = True" |
  "is_ValueNode (LoopEndNode _) = True" |
  "is_ValueNode (DeoptimizingFixedWithNextNode _ _) = True" |
  "is_ValueNode (LoopExitNode _ _ _) = True" |
  "is_ValueNode (AbstractBeginNode _) = True" |
  "is_ValueNode (AndNode _ _) = True" |
  "is_ValueNode (ValuePhiNode _ _) = True" |
  "is_ValueNode (AddNode _ _) = True" |
  "is_ValueNode (AbstractNewArrayNode _ _ _) = True" |
  "is_ValueNode (XorNode _ _) = True" |
  "is_ValueNode (DynamicNewArrayNode _ _ _) = True" |
  "is_ValueNode (PhiNode _) = True" |
  "is_ValueNode (AccessFieldNode _) = True" |
  "is_ValueNode (LoadFieldNode _ _) = True" |
  "is_ValueNode (AbsNode _) = True" |
  "is_ValueNode (MergeNode _ _ _) = True" |
  "is_ValueNode (FixedNode) = True" |
  "is_ValueNode _ = False"

fun is_StartNode :: "IRNode \<Rightarrow> bool" where
  "is_StartNode (StartNode _ _) = True" |
  "is_StartNode _ = False"

fun is_NewArrayNode :: "IRNode \<Rightarrow> bool" where
  "is_NewArrayNode (NewArrayNode _ _ _) = True" |
  "is_NewArrayNode _ = False"

fun is_UnaryArithmeticNode :: "IRNode \<Rightarrow> bool" where
  "is_UnaryArithmeticNode (NegateNode _) = True" |
  "is_UnaryArithmeticNode (NotNode _) = True" |
  "is_UnaryArithmeticNode (UnaryArithmeticNode _) = True" |
  "is_UnaryArithmeticNode (AbsNode _) = True" |
  "is_UnaryArithmeticNode _ = False"

fun is_AbstractMergeNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractMergeNode (AbstractMergeNode _ _ _) = True" |
  "is_AbstractMergeNode (LoopBeginNode _ _ _ _) = True" |
  "is_AbstractMergeNode (MergeNode _ _ _) = True" |
  "is_AbstractMergeNode _ = False"

fun is_LoopExitNode :: "IRNode \<Rightarrow> bool" where
  "is_LoopExitNode (LoopExitNode _ _ _) = True" |
  "is_LoopExitNode _ = False"

fun is_MergeNode :: "IRNode \<Rightarrow> bool" where
  "is_MergeNode (MergeNode _ _ _) = True" |
  "is_MergeNode _ = False"

fun is_IfNode :: "IRNode \<Rightarrow> bool" where
  "is_IfNode (IfNode _ _ _) = True" |
  "is_IfNode _ = False"

fun is_LoopBeginNode :: "IRNode \<Rightarrow> bool" where
  "is_LoopBeginNode (LoopBeginNode _ _ _ _) = True" |
  "is_LoopBeginNode _ = False"

fun is_FloatingNode :: "IRNode \<Rightarrow> bool" where
  "is_FloatingNode (NegateNode _) = True" |
  "is_FloatingNode (OrNode _ _) = True" |
  "is_FloatingNode (ConditionalNode _ _ _) = True" |
  "is_FloatingNode (FloatingNode) = True" |
  "is_FloatingNode (SubNode _ _) = True" |
  "is_FloatingNode (UnaryNode _) = True" |
  "is_FloatingNode (NotNode _) = True" |
  "is_FloatingNode (ProxyNode _) = True" |
  "is_FloatingNode (UnaryArithmeticNode _) = True" |
  "is_FloatingNode (BinaryNode _ _) = True" |
  "is_FloatingNode (ConstantNode _) = True" |
  "is_FloatingNode (MulNode _ _) = True" |
  "is_FloatingNode (BinaryArithmeticNode _ _) = True" |
  "is_FloatingNode (AndNode _ _) = True" |
  "is_FloatingNode (ValuePhiNode _ _) = True" |
  "is_FloatingNode (AddNode _ _) = True" |
  "is_FloatingNode (XorNode _ _) = True" |
  "is_FloatingNode (PhiNode _) = True" |
  "is_FloatingNode (AbsNode _) = True" |
  "is_FloatingNode _ = False"

fun is_AbstractNewArrayNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractNewArrayNode (NewArrayNode _ _ _) = True" |
  "is_AbstractNewArrayNode (AbstractNewArrayNode _ _ _) = True" |
  "is_AbstractNewArrayNode (DynamicNewArrayNode _ _ _) = True" |
  "is_AbstractNewArrayNode _ = False"

fun is_MulNode :: "IRNode \<Rightarrow> bool" where
  "is_MulNode (MulNode _ _) = True" |
  "is_MulNode _ = False"

fun is_LoopEndNode :: "IRNode \<Rightarrow> bool" where
  "is_LoopEndNode (LoopEndNode _) = True" |
  "is_LoopEndNode _ = False"

fun is_FixedNode :: "IRNode \<Rightarrow> bool" where
  "is_FixedNode (EndNode) = True" |
  "is_FixedNode (AbstractMergeNode _ _ _) = True" |
  "is_FixedNode (BeginStateSplitNode _ _) = True" |
  "is_FixedNode (NewInstanceNode _ _ _) = True" |
  "is_FixedNode (StartNode _ _) = True" |
  "is_FixedNode (IfNode _ _ _) = True" |
  "is_FixedNode (BeginNode _) = True" |
  "is_FixedNode (FixedWithNextNode _) = True" |
  "is_FixedNode (StoreFieldNode _ _ _ _) = True" |
  "is_FixedNode (AbstractNewObjectNode _ _) = True" |
  "is_FixedNode (LoopBeginNode _ _ _ _) = True" |
  "is_FixedNode (AbstractEndNode) = True" |
  "is_FixedNode (NewArrayNode _ _ _) = True" |
  "is_FixedNode (ControlSplitNode) = True" |
  "is_FixedNode (LoopEndNode _) = True" |
  "is_FixedNode (DeoptimizingFixedWithNextNode _ _) = True" |
  "is_FixedNode (LoopExitNode _ _ _) = True" |
  "is_FixedNode (AbstractBeginNode _) = True" |
  "is_FixedNode (AbstractNewArrayNode _ _ _) = True" |
  "is_FixedNode (DynamicNewArrayNode _ _ _) = True" |
  "is_FixedNode (AccessFieldNode _) = True" |
  "is_FixedNode (LoadFieldNode _ _) = True" |
  "is_FixedNode (MergeNode _ _ _) = True" |
  "is_FixedNode (FixedNode) = True" |
  "is_FixedNode _ = False"

fun is_FixedWithNextNode :: "IRNode \<Rightarrow> bool" where
  "is_FixedWithNextNode (AbstractMergeNode _ _ _) = True" |
  "is_FixedWithNextNode (BeginStateSplitNode _ _) = True" |
  "is_FixedWithNextNode (NewInstanceNode _ _ _) = True" |
  "is_FixedWithNextNode (StartNode _ _) = True" |
  "is_FixedWithNextNode (BeginNode _) = True" |
  "is_FixedWithNextNode (FixedWithNextNode _) = True" |
  "is_FixedWithNextNode (StoreFieldNode _ _ _ _) = True" |
  "is_FixedWithNextNode (AbstractNewObjectNode _ _) = True" |
  "is_FixedWithNextNode (LoopBeginNode _ _ _ _) = True" |
  "is_FixedWithNextNode (NewArrayNode _ _ _) = True" |
  "is_FixedWithNextNode (DeoptimizingFixedWithNextNode _ _) = True" |
  "is_FixedWithNextNode (LoopExitNode _ _ _) = True" |
  "is_FixedWithNextNode (AbstractBeginNode _) = True" |
  "is_FixedWithNextNode (AbstractNewArrayNode _ _ _) = True" |
  "is_FixedWithNextNode (DynamicNewArrayNode _ _ _) = True" |
  "is_FixedWithNextNode (AccessFieldNode _) = True" |
  "is_FixedWithNextNode (LoadFieldNode _ _) = True" |
  "is_FixedWithNextNode (MergeNode _ _ _) = True" |
  "is_FixedWithNextNode _ = False"

fun is_LoadFieldNode :: "IRNode \<Rightarrow> bool" where
  "is_LoadFieldNode (LoadFieldNode _ _) = True" |
  "is_LoadFieldNode _ = False"

fun is_ConstantNode :: "IRNode \<Rightarrow> bool" where
  "is_ConstantNode (ConstantNode _) = True" |
  "is_ConstantNode _ = False"

fun is_BinaryNode :: "IRNode \<Rightarrow> bool" where
  "is_BinaryNode (OrNode _ _) = True" |
  "is_BinaryNode (SubNode _ _) = True" |
  "is_BinaryNode (BinaryNode _ _) = True" |
  "is_BinaryNode (MulNode _ _) = True" |
  "is_BinaryNode (BinaryArithmeticNode _ _) = True" |
  "is_BinaryNode (AndNode _ _) = True" |
  "is_BinaryNode (AddNode _ _) = True" |
  "is_BinaryNode (XorNode _ _) = True" |
  "is_BinaryNode _ = False"

fun is_SubNode :: "IRNode \<Rightarrow> bool" where
  "is_SubNode (SubNode _ _) = True" |
  "is_SubNode _ = False"

fun is_NegateNode :: "IRNode \<Rightarrow> bool" where
  "is_NegateNode (NegateNode _) = True" |
  "is_NegateNode _ = False"

fun is_BeginNode :: "IRNode \<Rightarrow> bool" where
  "is_BeginNode (BeginNode _) = True" |
  "is_BeginNode _ = False"

fun is_EndNode :: "IRNode \<Rightarrow> bool" where
  "is_EndNode (EndNode) = True" |
  "is_EndNode _ = False"

fun is_DynamicNewArrayNode :: "IRNode \<Rightarrow> bool" where
  "is_DynamicNewArrayNode (DynamicNewArrayNode _ _ _) = True" |
  "is_DynamicNewArrayNode _ = False"

fun is_OrNode :: "IRNode \<Rightarrow> bool" where
  "is_OrNode (OrNode _ _) = True" |
  "is_OrNode _ = False"

fun is_FrameState :: "IRNode \<Rightarrow> bool" where
  "is_FrameState (FrameState _ _ _ _) = True" |
  "is_FrameState _ = False"

fun is_Node :: "IRNode \<Rightarrow> bool" where
  "is_Node (NegateNode _) = True" |
  "is_Node (EndNode) = True" |
  "is_Node (AbstractMergeNode _ _ _) = True" |
  "is_Node (BeginStateSplitNode _ _) = True" |
  "is_Node (OrNode _ _) = True" |
  "is_Node (ValueNode) = True" |
  "is_Node (NewInstanceNode _ _ _) = True" |
  "is_Node (ConditionalNode _ _ _) = True" |
  "is_Node (StartNode _ _) = True" |
  "is_Node (IfNode _ _ _) = True" |
  "is_Node (FloatingNode) = True" |
  "is_Node (SubNode _ _) = True" |
  "is_Node (BeginNode _) = True" |
  "is_Node (UnaryNode _) = True" |
  "is_Node (NotNode _) = True" |
  "is_Node (ProxyNode _) = True" |
  "is_Node (FrameState _ _ _ _) = True" |
  "is_Node (FixedWithNextNode _) = True" |
  "is_Node (StoreFieldNode _ _ _ _) = True" |
  "is_Node (UnaryArithmeticNode _) = True" |
  "is_Node (AbstractNewObjectNode _ _) = True" |
  "is_Node (BinaryNode _ _) = True" |
  "is_Node (LoopBeginNode _ _ _ _) = True" |
  "is_Node (ConstantNode _) = True" |
  "is_Node (MulNode _ _) = True" |
  "is_Node (AbstractEndNode) = True" |
  "is_Node (NewArrayNode _ _ _) = True" |
  "is_Node (ControlSplitNode) = True" |
  "is_Node (BinaryArithmeticNode _ _) = True" |
  "is_Node (LoopEndNode _) = True" |
  "is_Node (DeoptimizingFixedWithNextNode _ _) = True" |
  "is_Node (LoopExitNode _ _ _) = True" |
  "is_Node (AbstractBeginNode _) = True" |
  "is_Node (AndNode _ _) = True" |
  "is_Node (ValuePhiNode _ _) = True" |
  "is_Node (AddNode _ _) = True" |
  "is_Node (AbstractNewArrayNode _ _ _) = True" |
  "is_Node (XorNode _ _) = True" |
  "is_Node (DynamicNewArrayNode _ _ _) = True" |
  "is_Node (PhiNode _) = True" |
  "is_Node (AccessFieldNode _) = True" |
  "is_Node (LoadFieldNode _ _) = True" |
  "is_Node (AbsNode _) = True" |
  "is_Node (MergeNode _ _ _) = True" |
  "is_Node (FixedNode) = True" |
  "is_Node _ = False"

fun is_XorNode :: "IRNode \<Rightarrow> bool" where
  "is_XorNode (XorNode _ _) = True" |
  "is_XorNode _ = False"

fun is_UnaryNode :: "IRNode \<Rightarrow> bool" where
  "is_UnaryNode (NegateNode _) = True" |
  "is_UnaryNode (UnaryNode _) = True" |
  "is_UnaryNode (NotNode _) = True" |
  "is_UnaryNode (UnaryArithmeticNode _) = True" |
  "is_UnaryNode (AbsNode _) = True" |
  "is_UnaryNode _ = False"

fun is_DeoptimizingFixedWithNextNode :: "IRNode \<Rightarrow> bool" where
  "is_DeoptimizingFixedWithNextNode (NewInstanceNode _ _ _) = True" |
  "is_DeoptimizingFixedWithNextNode (AbstractNewObjectNode _ _) = True" |
  "is_DeoptimizingFixedWithNextNode (NewArrayNode _ _ _) = True" |
  "is_DeoptimizingFixedWithNextNode (DeoptimizingFixedWithNextNode _ _) = True" |
  "is_DeoptimizingFixedWithNextNode (AbstractNewArrayNode _ _ _) = True" |
  "is_DeoptimizingFixedWithNextNode (DynamicNewArrayNode _ _ _) = True" |
  "is_DeoptimizingFixedWithNextNode _ = False"

fun is_BeginStateSplitNode :: "IRNode \<Rightarrow> bool" where
  "is_BeginStateSplitNode (AbstractMergeNode _ _ _) = True" |
  "is_BeginStateSplitNode (BeginStateSplitNode _ _) = True" |
  "is_BeginStateSplitNode (StartNode _ _) = True" |
  "is_BeginStateSplitNode (LoopBeginNode _ _ _ _) = True" |
  "is_BeginStateSplitNode (LoopExitNode _ _ _) = True" |
  "is_BeginStateSplitNode (MergeNode _ _ _) = True" |
  "is_BeginStateSplitNode _ = False"

fun is_ValuePhiNode :: "IRNode \<Rightarrow> bool" where
  "is_ValuePhiNode (ValuePhiNode _ _) = True" |
  "is_ValuePhiNode _ = False"

fun is_AbstractEndNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractEndNode (EndNode) = True" |
  "is_AbstractEndNode (AbstractEndNode) = True" |
  "is_AbstractEndNode (LoopEndNode _) = True" |
  "is_AbstractEndNode _ = False"

fun is_PhiNode :: "IRNode \<Rightarrow> bool" where
  "is_PhiNode (ValuePhiNode _ _) = True" |
  "is_PhiNode (PhiNode _) = True" |
  "is_PhiNode _ = False"

fun is_ControlSplitNode :: "IRNode \<Rightarrow> bool" where
  "is_ControlSplitNode (IfNode _ _ _) = True" |
  "is_ControlSplitNode (ControlSplitNode) = True" |
  "is_ControlSplitNode _ = False"

fun is_NotNode :: "IRNode \<Rightarrow> bool" where
  "is_NotNode (NotNode _) = True" |
  "is_NotNode _ = False"

fun is_AbstractBeginNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractBeginNode (AbstractMergeNode _ _ _) = True" |
  "is_AbstractBeginNode (BeginStateSplitNode _ _) = True" |
  "is_AbstractBeginNode (StartNode _ _) = True" |
  "is_AbstractBeginNode (BeginNode _) = True" |
  "is_AbstractBeginNode (LoopBeginNode _ _ _ _) = True" |
  "is_AbstractBeginNode (LoopExitNode _ _ _) = True" |
  "is_AbstractBeginNode (AbstractBeginNode _) = True" |
  "is_AbstractBeginNode (MergeNode _ _ _) = True" |
  "is_AbstractBeginNode _ = False"

fun is_AbstractNewObjectNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractNewObjectNode (NewInstanceNode _ _ _) = True" |
  "is_AbstractNewObjectNode (AbstractNewObjectNode _ _) = True" |
  "is_AbstractNewObjectNode (NewArrayNode _ _ _) = True" |
  "is_AbstractNewObjectNode (AbstractNewArrayNode _ _ _) = True" |
  "is_AbstractNewObjectNode (DynamicNewArrayNode _ _ _) = True" |
  "is_AbstractNewObjectNode _ = False"

fun is_NewInstanceNode :: "IRNode \<Rightarrow> bool" where
  "is_NewInstanceNode (NewInstanceNode _ _ _) = True" |
  "is_NewInstanceNode _ = False"

type_synonym IRGraph = "ID \<rightharpoonup> IRNode"

fun kind :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRNode" where
  "kind g nid = (case g nid of 
    Some n \<Rightarrow> n |
    None \<Rightarrow> NoNode)"

fun maybe_kind :: "IRGraph \<Rightarrow> ID option \<Rightarrow> IRNode" where
  "maybe_kind g (Some nid) = kind g nid" |
  "maybe_kind g None = NoNode"

fun wff_node_type :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> bool" where
  "wff_node_type g (NegateNode value) = ((is_ValueNode (kind g value)))" |
  "wff_node_type g (AbstractMergeNode ends stateAfter next) = ((\<forall> n \<in> (set ends) . (is_EndNode (kind g n))) \<and> (is_FrameState (maybe_kind g stateAfter)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (BeginStateSplitNode stateAfter next) = ((is_FrameState (maybe_kind g stateAfter)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (OrNode x y) = ((is_ValueNode (kind g x)) \<and> (is_ValueNode (kind g y)))" |
  "wff_node_type g (NewInstanceNode instanceClass stateBefore next) = ((is_FrameState (maybe_kind g stateBefore)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (ConditionalNode condition trueValue falseValue) = ((is_ValueNode (kind g trueValue)) \<and> (is_ValueNode (kind g falseValue)))" |
  "wff_node_type g (StartNode stateAfter next) = ((is_FrameState (maybe_kind g stateAfter)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (IfNode condition trueSuccessor falseSuccessor) = ((is_AbstractBeginNode (kind g trueSuccessor)) \<and> (is_AbstractBeginNode (kind g falseSuccessor)))" |
  "wff_node_type g (SubNode x y) = ((is_ValueNode (kind g x)) \<and> (is_ValueNode (kind g y)))" |
  "wff_node_type g (BeginNode next) = ((is_FixedNode (kind g next)))" |
  "wff_node_type g (UnaryNode value) = ((is_ValueNode (kind g value)))" |
  "wff_node_type g (NotNode value) = ((is_ValueNode (kind g value)))" |
  "wff_node_type g (ProxyNode loopExit) = ((is_LoopExitNode (kind g loopExit)))" |
  "wff_node_type g (FrameState monitorIds outerFrameState values virtualObjectMappings) = ((is_FrameState (maybe_kind g outerFrameState)) \<and> (\<forall> n \<in> (set values) . (is_ValueNode (maybe_kind g n))))" |
  "wff_node_type g (FixedWithNextNode next) = ((is_FixedNode (kind g next)))" |
  "wff_node_type g (StoreFieldNode field value stateAfter next) = ((is_ValueNode (kind g value)) \<and> (is_FrameState (maybe_kind g stateAfter)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (UnaryArithmeticNode value) = ((is_ValueNode (kind g value)))" |
  "wff_node_type g (AbstractNewObjectNode stateBefore next) = ((is_FrameState (maybe_kind g stateBefore)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (BinaryNode x y) = ((is_ValueNode (kind g x)) \<and> (is_ValueNode (kind g y)))" |
  "wff_node_type g (LoopBeginNode ends overflowGuard stateAfter next) = ((\<forall> n \<in> (set ends) . (is_EndNode (kind g n))) \<and> (is_FrameState (maybe_kind g stateAfter)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (MulNode x y) = ((is_ValueNode (kind g x)) \<and> (is_ValueNode (kind g y)))" |
  "wff_node_type g (NewArrayNode length0 stateBefore next) = ((is_ValueNode (kind g length0)) \<and> (is_FrameState (maybe_kind g stateBefore)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (BinaryArithmeticNode x y) = ((is_ValueNode (kind g x)) \<and> (is_ValueNode (kind g y)))" |
  "wff_node_type g (LoopEndNode loopBegin) = ((is_AbstractBeginNode (kind g loopBegin)))" |
  "wff_node_type g (DeoptimizingFixedWithNextNode stateBefore next) = ((is_FrameState (maybe_kind g stateBefore)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (LoopExitNode loopBegin stateAfter next) = ((is_AbstractBeginNode (kind g loopBegin)) \<and> (is_FrameState (maybe_kind g stateAfter)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (AbstractBeginNode next) = ((is_FixedNode (kind g next)))" |
  "wff_node_type g (AndNode x y) = ((is_ValueNode (kind g x)) \<and> (is_ValueNode (kind g y)))" |
  "wff_node_type g (ValuePhiNode values merge) = ((\<forall> n \<in> (set values) . (is_ValueNode (kind g n))) \<and> (is_AbstractMergeNode (kind g merge)))" |
  "wff_node_type g (AddNode x y) = ((is_ValueNode (kind g x)) \<and> (is_ValueNode (kind g y)))" |
  "wff_node_type g (AbstractNewArrayNode length0 stateBefore next) = ((is_ValueNode (kind g length0)) \<and> (is_FrameState (maybe_kind g stateBefore)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (XorNode x y) = ((is_ValueNode (kind g x)) \<and> (is_ValueNode (kind g y)))" |
  "wff_node_type g (DynamicNewArrayNode length0 stateBefore next) = ((is_ValueNode (kind g length0)) \<and> (is_FrameState (maybe_kind g stateBefore)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g (PhiNode merge) = ((is_AbstractMergeNode (kind g merge)))" |
  "wff_node_type g (AccessFieldNode next) = ((is_FixedNode (kind g next)))" |
  "wff_node_type g (LoadFieldNode field next) = ((is_FixedNode (kind g next)))" |
  "wff_node_type g (AbsNode value) = ((is_ValueNode (kind g value)))" |
  "wff_node_type g (MergeNode ends stateAfter next) = ((\<forall> n \<in> (set ends) . (is_EndNode (kind g n))) \<and> (is_FrameState (maybe_kind g stateAfter)) \<and> (is_FixedNode (kind g next)))" |
  "wff_node_type g _ = True"

end
