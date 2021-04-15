subsection \<open>Hierarchy of Nodes\<close>

theory IRNodeHierarchy
imports IRNodes
begin

(* Datatype with no parameters don't generate selectors *)
fun is_EndNode :: "IRNode \<Rightarrow> bool" where
  "is_EndNode EndNode = True" |
  "is_EndNode _ = False"


text \<open>Class inheritance functions to determine if a node is extended from another\<close>
(* nodeout: isabelle-subclass *)
fun isVirtualStateType :: "IRNode \<Rightarrow> bool" where
  "isVirtualStateType n = ((is_FrameState n))"

fun isAbstractEndNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractEndNodeType n = ((is_EndNode n) \<or> (is_LoopEndNode n))"

fun isAbstractMergeNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractMergeNodeType n = ((is_LoopBeginNode n) \<or> (is_MergeNode n))"

fun isBeginStateSplitNodeType :: "IRNode \<Rightarrow> bool" where
  "isBeginStateSplitNodeType n = ((isAbstractMergeNodeType n) \<or> (is_ExceptionObjectNode n) \<or> (is_LoopExitNode n) \<or> (is_StartNode n))"

fun isAbstractBeginNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractBeginNodeType n = ((is_BeginNode n) \<or> (isBeginStateSplitNodeType n) \<or> (is_KillingBeginNode n))"

fun isAbstractMemoryCheckpointType :: "IRNode \<Rightarrow> bool" where
  "isAbstractMemoryCheckpointType n = ((is_BytecodeExceptionNode n) \<or> (is_InvokeNode n))"

fun isAbstractStateSplitType :: "IRNode \<Rightarrow> bool" where
  "isAbstractStateSplitType n = ((isAbstractMemoryCheckpointType n))"

fun isAccessFieldNodeType :: "IRNode \<Rightarrow> bool" where
  "isAccessFieldNodeType n = ((is_LoadFieldNode n) \<or> (is_StoreFieldNode n))"

fun isIntegerDivRemNodeType :: "IRNode \<Rightarrow> bool" where
  "isIntegerDivRemNodeType n = ((is_SignedDivNode n) \<or> (is_SignedRemNode n))"

fun isFixedBinaryNodeType :: "IRNode \<Rightarrow> bool" where
  "isFixedBinaryNodeType n = ((isIntegerDivRemNodeType n))"

fun isAbstractNewArrayNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractNewArrayNodeType n = ((is_DynamicNewArrayNode n) \<or> (is_NewArrayNode n))"

fun isAbstractNewObjectNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractNewObjectNodeType n = ((isAbstractNewArrayNodeType n) \<or> (is_NewInstanceNode n))"

fun isDeoptimizingFixedWithNextNodeType :: "IRNode \<Rightarrow> bool" where
  "isDeoptimizingFixedWithNextNodeType n = ((isAbstractNewObjectNodeType n) \<or> (isFixedBinaryNodeType n))"

fun isFixedWithNextNodeType :: "IRNode \<Rightarrow> bool" where
  "isFixedWithNextNodeType n = ((isAbstractBeginNodeType n) \<or> (isAbstractStateSplitType n) \<or> (isAccessFieldNodeType n) \<or> (isDeoptimizingFixedWithNextNodeType n))"

fun isWithExceptionNodeType :: "IRNode \<Rightarrow> bool" where
  "isWithExceptionNodeType n = ((is_InvokeWithExceptionNode n))"

fun isControlSplitNodeType :: "IRNode \<Rightarrow> bool" where
  "isControlSplitNodeType n = ((is_IfNode n) \<or> (isWithExceptionNodeType n))"

fun isControlSinkNodeType :: "IRNode \<Rightarrow> bool" where
  "isControlSinkNodeType n = ((is_ReturnNode n) \<or> (is_UnwindNode n))"

fun isFixedNodeType :: "IRNode \<Rightarrow> bool" where
  "isFixedNodeType n = ((isAbstractEndNodeType n) \<or> (isControlSinkNodeType n) \<or> (isControlSplitNodeType n) \<or> (isFixedWithNextNodeType n))"

fun isCallTargetNodeType :: "IRNode \<Rightarrow> bool" where
  "isCallTargetNodeType n = ((is_MethodCallTargetNode n))"

fun isBinaryArithmeticNodeType :: "IRNode \<Rightarrow> bool" where
  "isBinaryArithmeticNodeType n = ((is_AddNode n) \<or> (is_AndNode n) \<or> (is_MulNode n) \<or> (is_OrNode n) \<or> (is_SubNode n) \<or> (is_XorNode n))"

fun isBinaryNodeType :: "IRNode \<Rightarrow> bool" where
  "isBinaryNodeType n = ((isBinaryArithmeticNodeType n))"

fun isProxyNodeType :: "IRNode \<Rightarrow> bool" where
  "isProxyNodeType n = ((is_ValueProxyNode n))"

fun isFloatingGuardedNodeType :: "IRNode \<Rightarrow> bool" where
  "isFloatingGuardedNodeType n = ((is_PiNode n))"

fun isAbstractLocalNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractLocalNodeType n = ((is_ParameterNode n))"

fun isUnaryOpLogicNodeType :: "IRNode \<Rightarrow> bool" where
  "isUnaryOpLogicNodeType n = ((is_IsNullNode n))"

fun isIntegerLowerThanNodeType :: "IRNode \<Rightarrow> bool" where
  "isIntegerLowerThanNodeType n = ((is_IntegerLessThanNode n))"

fun isCompareNodeType :: "IRNode \<Rightarrow> bool" where
  "isCompareNodeType n = ((is_IntegerEqualsNode n) \<or> (isIntegerLowerThanNodeType n))"

fun isBinaryOpLogicNodeType :: "IRNode \<Rightarrow> bool" where
  "isBinaryOpLogicNodeType n = ((isCompareNodeType n))"

fun isLogicNodeType :: "IRNode \<Rightarrow> bool" where
  "isLogicNodeType n = ((isBinaryOpLogicNodeType n) \<or> (is_LogicNegationNode n) \<or> (is_ShortCircuitOrNode n) \<or> (isUnaryOpLogicNodeType n))"

fun isUnaryArithmeticNodeType :: "IRNode \<Rightarrow> bool" where
  "isUnaryArithmeticNodeType n = ((is_AbsNode n) \<or> (is_NegateNode n) \<or> (is_NotNode n))"

fun isUnaryNodeType :: "IRNode \<Rightarrow> bool" where
  "isUnaryNodeType n = ((isUnaryArithmeticNodeType n))"

fun isPhiNodeType :: "IRNode \<Rightarrow> bool" where
  "isPhiNodeType n = ((is_ValuePhiNode n))"

fun isFloatingNodeType :: "IRNode \<Rightarrow> bool" where
  "isFloatingNodeType n = ((isAbstractLocalNodeType n) \<or> (isBinaryNodeType n) \<or> (is_ConditionalNode n) \<or> (is_ConstantNode n) \<or> (isFloatingGuardedNodeType n) \<or> (isLogicNodeType n) \<or> (isPhiNodeType n) \<or> (isProxyNodeType n) \<or> (isUnaryNodeType n))"

fun isValueNodeType :: "IRNode \<Rightarrow> bool" where
  "isValueNodeType n = ((isCallTargetNodeType n) \<or> (isFixedNodeType n) \<or> (isFloatingNodeType n))"

fun isNodeType :: "IRNode \<Rightarrow> bool" where
  "isNodeType n = ((isValueNodeType n) \<or> (isVirtualStateType n))"

fun is_MemoryKill :: "IRNode \<Rightarrow> bool" where
  "is_MemoryKill n = ((isAbstractMemoryCheckpointType n))"

fun is_NarrowableArithmeticNode :: "IRNode \<Rightarrow> bool" where
  "is_NarrowableArithmeticNode n = ((is_AbsNode n) \<or> (is_AddNode n) \<or> (is_AndNode n) \<or> (is_MulNode n) \<or> (is_NegateNode n) \<or> (is_NotNode n) \<or> (is_OrNode n) \<or> (is_SubNode n) \<or> (is_XorNode n))"

fun is_AnchoringNode :: "IRNode \<Rightarrow> bool" where
  "is_AnchoringNode n = ((isAbstractBeginNodeType n))"

fun is_DeoptBefore :: "IRNode \<Rightarrow> bool" where
  "is_DeoptBefore n = ((isDeoptimizingFixedWithNextNodeType n))"

fun is_IndirectCanonicalization :: "IRNode \<Rightarrow> bool" where
  "is_IndirectCanonicalization n = ((isLogicNodeType n))"

fun is_IterableNodeType :: "IRNode \<Rightarrow> bool" where
  "is_IterableNodeType n = ((isAbstractBeginNodeType n) \<or> (isAbstractMergeNodeType n) \<or> (is_FrameState n) \<or> (is_IfNode n) \<or> (isIntegerDivRemNodeType n) \<or> (is_InvokeWithExceptionNode n) \<or> (is_LoopBeginNode n) \<or> (is_LoopExitNode n) \<or> (is_MethodCallTargetNode n) \<or> (is_ParameterNode n) \<or> (is_ReturnNode n) \<or> (is_ShortCircuitOrNode n))"

fun is_Invoke :: "IRNode \<Rightarrow> bool" where
  "is_Invoke n = ((is_InvokeNode n) \<or> (is_InvokeWithExceptionNode n))"

fun is_Proxy :: "IRNode \<Rightarrow> bool" where
  "is_Proxy n = ((isProxyNodeType n))"

fun is_ValueProxy :: "IRNode \<Rightarrow> bool" where
  "is_ValueProxy n = ((is_PiNode n) \<or> (is_ValueProxyNode n))"

fun is_ValueNodeInterface :: "IRNode \<Rightarrow> bool" where
  "is_ValueNodeInterface n = ((isValueNodeType n))"

fun is_ArrayLengthProvider :: "IRNode \<Rightarrow> bool" where
  "is_ArrayLengthProvider n = ((isAbstractNewArrayNodeType n) \<or> (is_ConstantNode n))"

fun is_StampInverter :: "IRNode \<Rightarrow> bool" where
  "is_StampInverter n = ((is_NegateNode n) \<or> (is_NotNode n))"

fun is_GuardingNode :: "IRNode \<Rightarrow> bool" where
  "is_GuardingNode n = ((isAbstractBeginNodeType n))"

fun is_SingleMemoryKill :: "IRNode \<Rightarrow> bool" where
  "is_SingleMemoryKill n = ((is_BytecodeExceptionNode n) \<or> (is_ExceptionObjectNode n) \<or> (is_InvokeNode n) \<or> (is_InvokeWithExceptionNode n) \<or> (is_KillingBeginNode n) \<or> (is_StartNode n))"

fun is_LIRLowerable :: "IRNode \<Rightarrow> bool" where
  "is_LIRLowerable n = ((isAbstractBeginNodeType n) \<or> (isAbstractEndNodeType n) \<or> (isAbstractMergeNodeType n) \<or> (isBinaryOpLogicNodeType n) \<or> (isCallTargetNodeType n) \<or> (is_ConditionalNode n) \<or> (is_ConstantNode n) \<or> (is_IfNode n) \<or> (is_InvokeNode n) \<or> (is_InvokeWithExceptionNode n) \<or> (is_IsNullNode n) \<or> (is_LoopBeginNode n) \<or> (is_PiNode n) \<or> (is_ReturnNode n) \<or> (isIntegerDivRemNodeType n) \<or> (isUnaryOpLogicNodeType n) \<or> (is_UnwindNode n))"

fun is_GuardedNode :: "IRNode \<Rightarrow> bool" where
  "is_GuardedNode n = ((isFloatingGuardedNodeType n))"

fun is_ArithmeticLIRLowerable :: "IRNode \<Rightarrow> bool" where
  "is_ArithmeticLIRLowerable n = ((is_AbsNode n) \<or> (isBinaryArithmeticNodeType n) \<or> (is_NotNode n) \<or> (isUnaryArithmeticNodeType n))"

fun is_SwitchFoldable :: "IRNode \<Rightarrow> bool" where
  "is_SwitchFoldable n = ((is_IfNode n))"

fun is_VirtualizableAllocation :: "IRNode \<Rightarrow> bool" where
  "is_VirtualizableAllocation n = ((is_NewArrayNode n) \<or> (is_NewInstanceNode n))"

fun is_Unary :: "IRNode \<Rightarrow> bool" where
  "is_Unary n = ((is_LoadFieldNode n) \<or> (is_LogicNegationNode n) \<or> (isUnaryNodeType n) \<or> (isUnaryOpLogicNodeType n))"

fun is_FixedNodeInterface :: "IRNode \<Rightarrow> bool" where
  "is_FixedNodeInterface n = ((isFixedNodeType n))"

fun is_BinaryCommutative :: "IRNode \<Rightarrow> bool" where
  "is_BinaryCommutative n = ((is_AddNode n) \<or> (is_AndNode n) \<or> (is_IntegerEqualsNode n) \<or> (is_MulNode n) \<or> (is_OrNode n) \<or> (is_XorNode n))"

fun is_Canonicalizable :: "IRNode \<Rightarrow> bool" where
  "is_Canonicalizable n = ((is_BytecodeExceptionNode n) \<or> (is_ConditionalNode n) \<or> (is_DynamicNewArrayNode n) \<or> (isPhiNodeType n) \<or> (is_PiNode n) \<or> (isProxyNodeType n) \<or> (is_StoreFieldNode n) \<or> (is_ValueProxyNode n))"

fun is_UncheckedInterfaceProvider :: "IRNode \<Rightarrow> bool" where
  "is_UncheckedInterfaceProvider n = ((is_InvokeNode n) \<or> (is_InvokeWithExceptionNode n) \<or> (is_LoadFieldNode n) \<or> (is_ParameterNode n))"

fun is_Binary :: "IRNode \<Rightarrow> bool" where
  "is_Binary n = ((isBinaryArithmeticNodeType n) \<or> (isBinaryNodeType n) \<or> (isBinaryOpLogicNodeType n) \<or> (isCompareNodeType n) \<or> (isFixedBinaryNodeType n) \<or> (is_ShortCircuitOrNode n))"

fun is_ArithmeticOperation :: "IRNode \<Rightarrow> bool" where
  "is_ArithmeticOperation n = ((isBinaryArithmeticNodeType n) \<or> (isUnaryArithmeticNodeType n))"

fun is_ValueNumberable :: "IRNode \<Rightarrow> bool" where
  "is_ValueNumberable n = ((isFloatingNodeType n) \<or> (isProxyNodeType n))"

fun is_Lowerable :: "IRNode \<Rightarrow> bool" where
  "is_Lowerable n = ((isAbstractNewObjectNodeType n) \<or> (isAccessFieldNodeType n) \<or> (is_BytecodeExceptionNode n) \<or> (is_ExceptionObjectNode n) \<or> (isIntegerDivRemNodeType n) \<or> (is_UnwindNode n))"

fun is_Virtualizable :: "IRNode \<Rightarrow> bool" where
  "is_Virtualizable n = ((is_IsNullNode n) \<or> (is_LoadFieldNode n) \<or> (is_PiNode n) \<or> (is_StoreFieldNode n) \<or> (is_ValueProxyNode n))"

fun is_Simplifiable :: "IRNode \<Rightarrow> bool" where
  "is_Simplifiable n = ((isAbstractMergeNodeType n) \<or> (is_BeginNode n) \<or> (is_IfNode n) \<or> (is_LoopExitNode n) \<or> (is_MethodCallTargetNode n) \<or> (is_NewArrayNode n))"

fun is_StateSplit :: "IRNode \<Rightarrow> bool" where
  "is_StateSplit n = ((isAbstractStateSplitType n) \<or> (isBeginStateSplitNodeType n) \<or> (is_StoreFieldNode n))"
(* nodeout *)

fun is_sequential_node :: "IRNode \<Rightarrow> bool" where
  "is_sequential_node (StartNode _ _) = True" |
  "is_sequential_node (BeginNode _) = True" |
  "is_sequential_node (KillingBeginNode _) = True" |
  "is_sequential_node (LoopBeginNode _ _ _ _) = True" |
  "is_sequential_node (LoopExitNode _ _ _) = True" |
  "is_sequential_node (MergeNode _ _ _) = True" |
  "is_sequential_node _ = False"

(* nodeout: isabelle-compare-type *)
fun is_same_ir_node_type :: "IRNode \<Rightarrow> IRNode \<Rightarrow> bool" where
"is_same_ir_node_type n1 n2 = (
  ((is_AbsNode n1) \<and> (is_AbsNode n2)) \<or>
  ((is_AddNode n1) \<and> (is_AddNode n2)) \<or>
  ((is_AndNode n1) \<and> (is_AndNode n2)) \<or>
  ((is_BeginNode n1) \<and> (is_BeginNode n2)) \<or>
  ((is_BytecodeExceptionNode n1) \<and> (is_BytecodeExceptionNode n2)) \<or>
  ((is_ConditionalNode n1) \<and> (is_ConditionalNode n2)) \<or>
  ((is_ConstantNode n1) \<and> (is_ConstantNode n2)) \<or>
  ((is_DynamicNewArrayNode n1) \<and> (is_DynamicNewArrayNode n2)) \<or>
  ((is_EndNode n1) \<and> (is_EndNode n2)) \<or>
  ((is_ExceptionObjectNode n1) \<and> (is_ExceptionObjectNode n2)) \<or>
  ((is_FrameState n1) \<and> (is_FrameState n2)) \<or>
  ((is_IfNode n1) \<and> (is_IfNode n2)) \<or>
  ((is_IntegerEqualsNode n1) \<and> (is_IntegerEqualsNode n2)) \<or>
  ((is_IntegerLessThanNode n1) \<and> (is_IntegerLessThanNode n2)) \<or>
  ((is_InvokeNode n1) \<and> (is_InvokeNode n2)) \<or>
  ((is_InvokeWithExceptionNode n1) \<and> (is_InvokeWithExceptionNode n2)) \<or>
  ((is_IsNullNode n1) \<and> (is_IsNullNode n2)) \<or>
  ((is_KillingBeginNode n1) \<and> (is_KillingBeginNode n2)) \<or>
  ((is_LoadFieldNode n1) \<and> (is_LoadFieldNode n2)) \<or>
  ((is_LogicNegationNode n1) \<and> (is_LogicNegationNode n2)) \<or>
  ((is_LoopBeginNode n1) \<and> (is_LoopBeginNode n2)) \<or>
  ((is_LoopEndNode n1) \<and> (is_LoopEndNode n2)) \<or>
  ((is_LoopExitNode n1) \<and> (is_LoopExitNode n2)) \<or>
  ((is_MergeNode n1) \<and> (is_MergeNode n2)) \<or>
  ((is_MethodCallTargetNode n1) \<and> (is_MethodCallTargetNode n2)) \<or>
  ((is_MulNode n1) \<and> (is_MulNode n2)) \<or>
  ((is_NegateNode n1) \<and> (is_NegateNode n2)) \<or>
  ((is_NewArrayNode n1) \<and> (is_NewArrayNode n2)) \<or>
  ((is_NewInstanceNode n1) \<and> (is_NewInstanceNode n2)) \<or>
  ((is_NotNode n1) \<and> (is_NotNode n2)) \<or>
  ((is_OrNode n1) \<and> (is_OrNode n2)) \<or>
  ((is_ParameterNode n1) \<and> (is_ParameterNode n2)) \<or>
  ((is_PiNode n1) \<and> (is_PiNode n2)) \<or>
  ((is_ReturnNode n1) \<and> (is_ReturnNode n2)) \<or>
  ((is_ShortCircuitOrNode n1) \<and> (is_ShortCircuitOrNode n2)) \<or>
  ((is_SignedDivNode n1) \<and> (is_SignedDivNode n2)) \<or>
  ((is_StartNode n1) \<and> (is_StartNode n2)) \<or>
  ((is_StoreFieldNode n1) \<and> (is_StoreFieldNode n2)) \<or>
  ((is_SubNode n1) \<and> (is_SubNode n2)) \<or>
  ((is_UnwindNode n1) \<and> (is_UnwindNode n2)) \<or>
  ((is_ValuePhiNode n1) \<and> (is_ValuePhiNode n2)) \<or>
  ((is_ValueProxyNode n1) \<and> (is_ValueProxyNode n2)) \<or>
  ((is_XorNode n1) \<and> (is_XorNode n2)))"

end
