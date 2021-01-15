section \<open>Node Hierarchy\<close>

theory IRNodeHierarchy
imports IRNodes
begin

(* Datatype with no parameters don't generate selectors *)
fun is_AbstractEndNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractEndNode AbstractEndNode = True" |
  "is_AbstractEndNode _ = False"

fun is_EndNode :: "IRNode \<Rightarrow> bool" where
  "is_EndNode EndNode = True" |
  "is_EndNode _ = False"

fun is_ControlSplitNode :: "IRNode \<Rightarrow> bool" where
  "is_ControlSplitNode ControlSplitNode = True" |
  "is_ControlSplitNode _ = False"

fun is_FixedNode :: "IRNode \<Rightarrow> bool" where
  "is_FixedNode FixedNode = True" |
  "is_FixedNode _ = False"

fun is_AbstractLocalNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractLocalNode AbstractLocalNode = True" |
  "is_AbstractLocalNode _ = False"

fun is_FloatingNode :: "IRNode \<Rightarrow> bool" where
  "is_FloatingNode FloatingNode = True" |
  "is_FloatingNode _ = False"

fun is_ValueNode :: "IRNode \<Rightarrow> bool" where
  "is_ValueNode ValueNode = True" |
  "is_ValueNode _ = False"


text \<open>Class inheritance functions to determine if a node is extended from another\<close>
(* nodeout: isabelle-subclass *)
fun isAbstractEndNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractEndNodeType n = ((is_AbstractEndNode n) \<or> (is_EndNode n) \<or> (is_LoopEndNode n))" 

fun isControlSplitNodeType :: "IRNode \<Rightarrow> bool" where
  "isControlSplitNodeType n = ((is_ControlSplitNode n) \<or> (is_IfNode n) \<or> (is_SwitchNode n))" 

fun isAbstractMergeNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractMergeNodeType n = ((is_AbstractMergeNode n) \<or> (is_LoopBeginNode n) \<or> (is_MergeNode n))" 

fun isBeginStateSplitNodeType :: "IRNode \<Rightarrow> bool" where
  "isBeginStateSplitNodeType n = ((is_BeginStateSplitNode n) \<or> (isAbstractMergeNodeType n) \<or> (is_ExceptionObjectNode n) \<or> (is_LoopExitNode n) \<or> (is_StartNode n))" 

fun isAbstractBeginNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractBeginNodeType n = ((is_AbstractBeginNode n) \<or> (is_BeginNode n) \<or> (isBeginStateSplitNodeType n) \<or> (is_KillingBeginNode n))" 

fun isAccessFieldNodeType :: "IRNode \<Rightarrow> bool" where
  "isAccessFieldNodeType n = ((is_AccessFieldNode n) \<or> (is_LoadFieldNode n) \<or> (is_StoreFieldNode n))" 

fun isAbstractNewArrayNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractNewArrayNodeType n = ((is_AbstractNewArrayNode n) \<or> (is_DynamicNewArrayNode n) \<or> (is_NewArrayNode n))" 

fun isAbstractNewObjectNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractNewObjectNodeType n = ((is_AbstractNewObjectNode n) \<or> (isAbstractNewArrayNodeType n) \<or> (is_NewInstanceNode n))" 

fun isDeoptimizingFixedWithNextNodeType :: "IRNode \<Rightarrow> bool" where
  "isDeoptimizingFixedWithNextNodeType n = ((is_DeoptimizingFixedWithNextNode n) \<or> (isAbstractNewObjectNodeType n))" 

fun isFixedWithNextNodeType :: "IRNode \<Rightarrow> bool" where
  "isFixedWithNextNodeType n = ((is_FixedWithNextNode n) \<or> (isAbstractBeginNodeType n) \<or> (isAccessFieldNodeType n) \<or> (isDeoptimizingFixedWithNextNodeType n))" 

fun isFixedNodeType :: "IRNode \<Rightarrow> bool" where
  "isFixedNodeType n = ((is_FixedNode n) \<or> (isAbstractEndNodeType n) \<or> (isControlSplitNodeType n) \<or> (isFixedWithNextNodeType n))" 

fun isAbstractLocalNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractLocalNodeType n = ((is_AbstractLocalNode n) \<or> (is_ParameterNode n))" 

fun isBinaryArithmeticNodeType :: "IRNode \<Rightarrow> bool" where
  "isBinaryArithmeticNodeType n = ((is_BinaryArithmeticNode n) \<or> (is_AddNode n) \<or> (is_AndNode n) \<or> (is_MulNode n) \<or> (is_OrNode n) \<or> (is_SubNode n) \<or> (is_XorNode n))" 

fun isBinaryNodeType :: "IRNode \<Rightarrow> bool" where
  "isBinaryNodeType n = ((is_BinaryNode n) \<or> (isBinaryArithmeticNodeType n))" 

fun isPhiNodeType :: "IRNode \<Rightarrow> bool" where
  "isPhiNodeType n = ((is_PhiNode n) \<or> (is_ValuePhiNode n))" 

fun isProxyNodeType :: "IRNode \<Rightarrow> bool" where
  "isProxyNodeType n = ((is_ProxyNode n) \<or> (is_ValueProxyNode n))" 

fun isUnaryArithmeticNodeType :: "IRNode \<Rightarrow> bool" where
  "isUnaryArithmeticNodeType n = ((is_UnaryArithmeticNode n) \<or> (is_AbsNode n) \<or> (is_NegateNode n) \<or> (is_NotNode n))" 

fun isUnaryNodeType :: "IRNode \<Rightarrow> bool" where
  "isUnaryNodeType n = ((is_UnaryNode n) \<or> (isUnaryArithmeticNodeType n))" 

fun isFloatingNodeType :: "IRNode \<Rightarrow> bool" where
  "isFloatingNodeType n = ((is_FloatingNode n) \<or> (isAbstractLocalNodeType n) \<or> (isBinaryNodeType n) \<or> (is_ConditionalNode n) \<or> (is_ConstantNode n) \<or> (isPhiNodeType n) \<or> (isProxyNodeType n) \<or> (isUnaryNodeType n))" 

fun isValueNodeType :: "IRNode \<Rightarrow> bool" where
  "isValueNodeType n = ((is_ValueNode n) \<or> (isFixedNodeType n) \<or> (isFloatingNodeType n))"  
(* nodeout *)

fun is_sequential_node :: "IRNode \<Rightarrow> bool" where
  "is_sequential_node (StartNode _ _) = True" |
  "is_sequential_node (BeginNode _) = True" |
  "is_sequential_node (KillingBeginNode _) = True" |
  "is_sequential_node (NewInstanceNode _ _ _) = True" |
  "is_sequential_node (LoopBeginNode _ _ _ _) = True" |
  "is_sequential_node (LoopExitNode _ _ _) = True" |
  "is_sequential_node (SignedDivNode _ _ _ _ _) = True" |
  "is_sequential_node n = isAbstractMergeNodeType n"

end