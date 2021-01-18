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
fun isAbstractEndNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractEndNodeType n = ((is_EndNode n) \<or> (is_LoopEndNode n))" 

fun isControlSplitNodeType :: "IRNode \<Rightarrow> bool" where
  "isControlSplitNodeType n = ((is_IfNode n))" 

fun isAbstractMergeNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractMergeNodeType n = ((is_LoopBeginNode n) \<or> (is_MergeNode n))" 

fun isBeginStateSplitNodeType :: "IRNode \<Rightarrow> bool" where
  "isBeginStateSplitNodeType n = ((isAbstractMergeNodeType n) \<or> (is_ExceptionObjectNode n) \<or> (is_LoopExitNode n) \<or> (is_StartNode n))" 

fun isAbstractBeginNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractBeginNodeType n = ((is_BeginNode n) \<or> (isBeginStateSplitNodeType n) \<or> (is_KillingBeginNode n))" 

fun isAccessFieldNodeType :: "IRNode \<Rightarrow> bool" where
  "isAccessFieldNodeType n = ((is_LoadFieldNode n) \<or> (is_StoreFieldNode n))" 

fun isAbstractNewArrayNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractNewArrayNodeType n = ((is_DynamicNewArrayNode n) \<or> (is_NewArrayNode n))" 

fun isAbstractNewObjectNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractNewObjectNodeType n = ((isAbstractNewArrayNodeType n) \<or> (is_NewInstanceNode n))" 

fun isDeoptimizingFixedWithNextNodeType :: "IRNode \<Rightarrow> bool" where
  "isDeoptimizingFixedWithNextNodeType n = ((isAbstractNewObjectNodeType n))" 

fun isFixedWithNextNodeType :: "IRNode \<Rightarrow> bool" where
  "isFixedWithNextNodeType n = ((isAbstractBeginNodeType n) \<or> (isAccessFieldNodeType n) \<or> (isDeoptimizingFixedWithNextNodeType n))" 

fun isFixedNodeType :: "IRNode \<Rightarrow> bool" where
  "isFixedNodeType n = ((isAbstractEndNodeType n) \<or> (isControlSplitNodeType n) \<or> (isFixedWithNextNodeType n))" 

fun isAbstractLocalNodeType :: "IRNode \<Rightarrow> bool" where
  "isAbstractLocalNodeType n = ((is_ParameterNode n))" 

fun isBinaryArithmeticNodeType :: "IRNode \<Rightarrow> bool" where
  "isBinaryArithmeticNodeType n = ((is_AddNode n) \<or> (is_AndNode n) \<or> (is_MulNode n) \<or> (is_OrNode n) \<or> (is_SubNode n) \<or> (is_XorNode n))" 

fun isBinaryNodeType :: "IRNode \<Rightarrow> bool" where
  "isBinaryNodeType n = ((isBinaryArithmeticNodeType n))" 

fun isPhiNodeType :: "IRNode \<Rightarrow> bool" where
  "isPhiNodeType n = ((is_ValuePhiNode n))" 

fun isProxyNodeType :: "IRNode \<Rightarrow> bool" where
  "isProxyNodeType n = ((is_ValueProxyNode n))" 

fun isUnaryArithmeticNodeType :: "IRNode \<Rightarrow> bool" where
  "isUnaryArithmeticNodeType n = ((is_AbsNode n) \<or> (is_NegateNode n) \<or> (is_NotNode n))" 

fun isUnaryNodeType :: "IRNode \<Rightarrow> bool" where
  "isUnaryNodeType n = ((isUnaryArithmeticNodeType n))" 

fun isFloatingNodeType :: "IRNode \<Rightarrow> bool" where
  "isFloatingNodeType n = ((isAbstractLocalNodeType n) \<or> (isBinaryNodeType n) \<or> (is_ConditionalNode n) \<or> (is_ConstantNode n) \<or> (isPhiNodeType n) \<or> (isProxyNodeType n) \<or> (isUnaryNodeType n))" 

fun isValueNodeType :: "IRNode \<Rightarrow> bool" where
  "isValueNodeType n = ((isFixedNodeType n) \<or> (isFloatingNodeType n))" 
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