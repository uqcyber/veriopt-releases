section \<open>Node Hierarchy\<close>

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
  "isIntegerDivRemNodeType n = ((is_SignedDivNode n))"

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
(* nodeout *)

fun is_sequential_node :: "IRNode \<Rightarrow> bool" where
  "is_sequential_node (StartNode _ _) = True" |
  "is_sequential_node (BeginNode _) = True" |
  "is_sequential_node (KillingBeginNode _) = True" |
  "is_sequential_node (LoopBeginNode _ _ _ _) = True" |
  "is_sequential_node (LoopExitNode _ _ _) = True" |
  "is_sequential_node (SignedDivNode _ _ _ _ _) = True" |
  "is_sequential_node n = isAbstractMergeNodeType n"

end