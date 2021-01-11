section \<open>Inductive evaluation semantics of floating nodes\<close>

theory IREval
  imports
    IRGraph
    "HOL-Library.LaTeXsugar"
begin

(* To be replaced with More_Word definitions when switched back to 32 word *)
fun int32_not :: "int32 \<Rightarrow> int32" ("NOT") where
  "int32_not x = (if (x = 0) then 1 else 0)"
fun int32_and :: "int32 \<Rightarrow> int32 \<Rightarrow> int32" (infixr "AND" 5) where
  "int32_and x y = (if ((x \<noteq> 0) \<and> (y \<noteq> 0)) then 1 else 0)"
fun int32_or :: "int32 \<Rightarrow> int32 \<Rightarrow> int32" (infixr "OR" 5) where
  "int32_or x y = (if ((x \<noteq> 0) \<or> (y \<noteq> 0)) then 1 else 0)"
fun int32_xor :: "int32 \<Rightarrow> int32 \<Rightarrow> int32" (infixr "XOR" 5) where
  "int32_xor x y = ((x OR y) AND (NOT (x AND y)))"

type_synonym objref = "nat option"

datatype Value =
  UndefVal |
  IntVal int32 |
  ObjRef objref

datatype ExecutionState =
  Normal |
  Exception

datatype MapState =
  MapState
    (m_values: "ID \<Rightarrow> Value")
    (m_params: "Value list")
    (m_state: "ExecutionState")

definition new_map_state :: "MapState" where
  "new_map_state = MapState (\<lambda>x. UndefVal) [] Normal"

fun m_val :: "MapState \<Rightarrow> ID \<Rightarrow> Value" where
  "m_val m nid = (m_values m) nid"

fun m_set :: "ID \<Rightarrow> Value \<Rightarrow> MapState \<Rightarrow> MapState" where
  "m_set nid v (MapState m p s) = MapState (m(nid := v)) p s"

fun m_param :: "IRGraph \<Rightarrow> MapState \<Rightarrow> ID \<Rightarrow> Value" where
  "m_param g m nid = (case (kind g nid) of
    (ParameterNode i) \<Rightarrow> (m_params m)!i |
    _ \<Rightarrow> UndefVal)"

fun set_params :: "MapState \<Rightarrow> Value list \<Rightarrow> MapState" where
  "set_params (MapState m _ s) vs = MapState m vs s"

fun set_state :: "MapState \<Rightarrow> ExecutionState \<Rightarrow> MapState" where
  "set_state (MapState m p _) s = MapState m p s"

fun new_map :: "Value list \<Rightarrow> MapState" where
  "new_map ps = set_params new_map_state ps"


fun val_to_bool :: "int32 \<Rightarrow> bool" where
  "val_to_bool val = (if val = 0 then False else True)" 

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal 1)" |
  "bool_to_val False = (IntVal 0)"


(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index v (x # xs) = (if (x=v) then 0 else find_index v xs + 1)"

fun phi_list :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "phi_list g nid = 
    (filter (\<lambda>x.(is_PhiNode (kind g x)))
      (sorted_list_of_set (usages g nid)))"

fun input_index :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index g n n' = find_index n' (inp g n)"

fun phi_inputs :: "IRGraph \<Rightarrow> nat \<Rightarrow> ID list \<Rightarrow> ID list" where
  "phi_inputs g i nodes = (map (\<lambda>n. (inp g n)!(i + 1)) nodes)"

fun set_phis :: "ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_phis [] [] m = m" |
  "set_phis (nid # xs) (v # vs) m = (set_phis xs vs (m_set nid v m))" |
  "set_phis [] (v # vs) m = m" |
  "set_phis (x # xs) [] m = m"

fun first :: "'a list \<Rightarrow> 'a option" where
  "first [] = None" |
  "first xs = Some (hd xs)"

fun any_usage :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID option" where
  "any_usage g nid = first (sorted_list_of_set (usages g nid))"


inductive
  eval :: "IRGraph \<Rightarrow> MapState \<Rightarrow> ID \<Rightarrow> IRNode \<Rightarrow> Value \<Rightarrow> bool" (" _ _ \<turnstile> _ _ \<mapsto> _" 55)
  for g where

  ConstantNode:
  "\<lbrakk>val = (IntVal c)\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (ConstantNode c) \<mapsto> val" |

  ParameterNode:
  "\<lbrakk>val = (m_params m)!i\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (ParameterNode i) \<mapsto> val" |

  PhiNode:
  "\<lbrakk>val = m_val m nid\<rbrakk>
    \<Longrightarrow> g m \<turnstile> _ (PhiNode nid uu) \<mapsto> val" |

  ValuePhiNode:
  "\<lbrakk>val = m_val m nid\<rbrakk>
    \<Longrightarrow> g m \<turnstile> _ (ValuePhiNode nid _ _) \<mapsto> val" |

  ValueProxyNode:
  "\<lbrakk>g m \<turnstile> c (kind g c) \<mapsto> val\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (ValueProxyNode c _) \<mapsto> val" |

(* Unary arithmetic operators *)

  AbsNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (AbsNode x) \<mapsto> IntVal(if v<0 then -v else v)" |

  NegateNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (NegateNode x) \<mapsto> IntVal(-v)" |

(* Binary arithmetic operators *)

  AddNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<mapsto> IntVal(v2)\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (AddNode x y) \<mapsto> IntVal(v1+v2)" |

  SubNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<mapsto> IntVal(v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (SubNode x y) \<mapsto> IntVal(v1-v2)" |

  MulNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<mapsto> IntVal(v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (MulNode x y) \<mapsto> IntVal(v1*v2)" |

  SignedDivNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<mapsto> IntVal(v2)\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (SignedDivNode x y zeroCheck frameState next) \<mapsto> IntVal(v1 div v2)" |

(* Binary logical bitwise operators *)

  AndNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<mapsto> IntVal(v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (AndNode x y) \<mapsto> IntVal(v1 AND v2)" |

  OrNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<mapsto> IntVal(v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (OrNode x y) \<mapsto> IntVal(v1 OR v2)" |

  XorNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<mapsto> IntVal(v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (XorNode x y) \<mapsto> IntVal(v1 XOR v2)" |

(* Comparison operators *)
(* NOTE: if we use IntVal(bool_to_int(v1=v2)), then code generation does not work! *)
  IntegerEqualsNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<mapsto> IntVal(v2);
    val = bool_to_val(v1 = v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (IntegerEqualsNode x y) \<mapsto> val" |

  IntegerLessThanNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<mapsto> IntVal(v2);
    val = bool_to_val(v1 < v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (IntegerLessThanNode x y) \<mapsto> val" |

(* Other nodes *)
(* Note that both branches are evaluated but only one is used.
   This is not an issue as evaluation is total (but may return UnDef) *)

  ConditionalNode:
  "\<lbrakk>g m \<turnstile> condition (kind g condition) \<mapsto> IntVal(cond);
    g m \<turnstile> trueExp (kind g trueExp) \<mapsto> IntVal(trueVal);
    g m \<turnstile> falseExp (kind g falseExp) \<mapsto> IntVal(falseVal);
    val = IntVal(if cond \<noteq> 0 then trueVal else falseVal)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (ConditionalNode condition trueExp falseExp) \<mapsto> val" |

(* Note that v2 may evaluate to UnDef but is not used if v1 is true *)

  ShortCircuitOrNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<mapsto> IntVal(v2);
    val = IntVal(if v1 \<noteq> 0 then v1 else v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (ShortCircuitOrNode x y) \<mapsto> val" |

  LogicNegationNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    val = IntVal(NOT v1)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (LogicNegationNode x) \<mapsto> val" |

(* Access the value returned by the most recent call *)
  InvokeNodeEval:
  "\<lbrakk>val = m_val m nid\<rbrakk>
    \<Longrightarrow> g m \<turnstile> _ (InvokeNode nid callTarget classInit stateDuring stateAfter next) \<mapsto> val" |

  InvokeWithExceptionNodeEval:
  "\<lbrakk>val = m_val m nid\<rbrakk>
    \<Longrightarrow> g m \<turnstile> _ (InvokeWithExceptionNode nid callTarget classInit stateDuring stateAfter next exceptionEdge) \<mapsto> val" |

  NewInstanceNode:
  "g m \<turnstile> nid (NewInstanceNode class stateBefore next) \<mapsto> (ObjRef (Some 0))" |

  RefNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> val\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (RefNode x) \<mapsto> val" 

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as evalE) eval .

text \<open>Representative induction rules for eval\<close>
text_raw \<open>\Snip{ExpressionSemantics}%\<close>
text \<open>@{thm[mode=Rule] eval.ConstantNode [no_vars]} \textsc{ConstantNode}\<close>
text \<open>@{thm[mode=Rule] eval.ParameterNode [no_vars]} \textsc{ParameterNode}\<close>
text \<open>@{thm[mode=Rule] eval.ValuePhiNode [no_vars]} \textsc{ValuePhiNode}\<close>
text \<open>@{thm[mode=Rule] eval.NegateNode [no_vars]} \textsc{NegateNode}\<close>
text \<open>@{thm[mode=Rule] eval.AddNode [no_vars]} \textsc{AddNode}\<close>
text \<open>@{thm[mode=Rule] eval.ShortCircuitOrNode [no_vars]} \textsc{ShortCircuitOrNode}\<close>
text \<open>@{thm[mode=Rule] eval.InvokeNodeEval [no_vars]} \textsc{InvokeNodeEval}\<close>
text \<open>@{thm[mode=Rule] eval.RefNode [no_vars]} \textsc{RefNode}\<close>
text_raw \<open>\EndSnip\<close>


inductive
  eval_all :: "IRGraph \<Rightarrow> MapState \<Rightarrow> ID list \<Rightarrow> Value list \<Rightarrow> bool"
  ("_ _ _\<longmapsto>_" 55)
  for g where
  "g m [] \<longmapsto> []" |
  "\<lbrakk>g m \<turnstile> nid (kind g nid) \<mapsto> v;
    g m xs \<longmapsto> vs\<rbrakk>
   \<Longrightarrow> g m (nid # xs) \<longmapsto> (v # vs)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as eval_allE) eval_all .


(* Test the eval predicates. *)
inductive eval_graph :: "IRGraph \<Rightarrow> ID \<Rightarrow> Value list \<Rightarrow> Value \<Rightarrow> bool"
  where
  "\<lbrakk>state = new_map ps;
    g state \<turnstile> nid (kind g nid) \<mapsto> val\<rbrakk>
    \<Longrightarrow> eval_graph g nid ps val"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) "eval_graph" .

(* 5*5 \<Rightarrow> 25 *)
values "{v. eval_graph eg2_sq 4 [IntVal 5] v}"

fun has_control_flow :: "IRNode \<Rightarrow> bool" where
  "has_control_flow EndNode = True" |
  "has_control_flow AbstractEndNode = True" |
  "has_control_flow (LoopEndNode n) = True" |
  "has_control_flow n = (length (successors_of n) > 0)"

definition control_nodes :: "IRNode set" where
  "control_nodes = {n . has_control_flow n}"

fun is_floating_node :: "IRNode \<Rightarrow> bool" where
  "is_floating_node n = (\<not>(has_control_flow n))"

definition floating_nodes :: "IRNode set" where
  "floating_nodes = {n . is_floating_node n}"

lemma "is_floating_node n \<longleftrightarrow> \<not>(has_control_flow n)"
  by simp

lemma "n \<in> control_nodes \<longleftrightarrow> n \<notin> floating_nodes"
  by (simp add: control_nodes_def floating_nodes_def)

(* nodeout: isabelle-inductive-cases *)
inductive_cases AbsNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (AbsNode value) \<mapsto> val"

inductive_cases AbstractBeginNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (AbstractBeginNode next) \<mapsto> val"

inductive_cases AbstractEndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (AbstractEndNode) \<mapsto> val"

inductive_cases AbstractLocalNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (AbstractLocalNode) \<mapsto> val"

inductive_cases AbstractMergeNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (AbstractMergeNode ends stateAfter next) \<mapsto> val"

inductive_cases AbstractNewArrayNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (AbstractNewArrayNode length0 stateBefore next) \<mapsto> val"

inductive_cases AbstractNewObjectNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (AbstractNewObjectNode stateBefore next) \<mapsto> val"

inductive_cases AccessFieldNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (AccessFieldNode object next) \<mapsto> val"

inductive_cases AddNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (AddNode x y) \<mapsto> val"

inductive_cases AndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (AndNode x y) \<mapsto> val"

inductive_cases BeginNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (BeginNode next) \<mapsto> val"

inductive_cases BeginStateSplitNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (BeginStateSplitNode stateAfter next) \<mapsto> val"

inductive_cases BinaryArithmeticNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (BinaryArithmeticNode x y) \<mapsto> val"

inductive_cases BinaryNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (BinaryNode x y) \<mapsto> val"

inductive_cases BytecodeExceptionNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (BytecodeExceptionNode arguments stateAfter next) \<mapsto> val"

inductive_cases ConditionalNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (ConditionalNode condition trueValue falseValue) \<mapsto> val"

inductive_cases ConstantNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (ConstantNode intValue) \<mapsto> val"

inductive_cases ControlSplitNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (ControlSplitNode) \<mapsto> val"

inductive_cases DeoptimizingFixedWithNextNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (DeoptimizingFixedWithNextNode stateBefore next) \<mapsto> val"

inductive_cases DynamicNewArrayNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (DynamicNewArrayNode elementType length0 voidClass stateBefore next) \<mapsto> val"

inductive_cases EndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (EndNode) \<mapsto> val"

inductive_cases ExceptionObjectNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (ExceptionObjectNode stateAfter next) \<mapsto> val"

inductive_cases FixedNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (FixedNode) \<mapsto> val"

inductive_cases FixedWithNextNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (FixedWithNextNode next) \<mapsto> val"

inductive_cases FloatingNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (FloatingNode) \<mapsto> val"

inductive_cases FrameStateE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (FrameState monitorIds outerFrameState values virtualObjectMappings) \<mapsto> val"

inductive_cases IfNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (IfNode condition trueSuccessor falseSuccessor) \<mapsto> val"

inductive_cases IntegerEqualsNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (IntegerEqualsNode x y) \<mapsto> val"

inductive_cases IntegerLessThanNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (IntegerLessThanNode x y) \<mapsto> val"

inductive_cases InvokeNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (InvokeNode nid0 callTarget classInit stateDuring stateAfter next) \<mapsto> val"

inductive_cases InvokeWithExceptionNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (InvokeWithExceptionNode nid0 callTarget classInit stateDuring stateAfter next exceptionEdge) \<mapsto> val"

inductive_cases KillingBeginNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (KillingBeginNode next) \<mapsto> val"

inductive_cases LoadFieldNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (LoadFieldNode field object next) \<mapsto> val"

inductive_cases LogicNegationNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (LogicNegationNode value) \<mapsto> val"

inductive_cases LoopBeginNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (LoopBeginNode ends overflowGuard stateAfter next) \<mapsto> val"

inductive_cases LoopEndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (LoopEndNode loopBegin) \<mapsto> val"

inductive_cases LoopExitNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (LoopExitNode loopBegin stateAfter next) \<mapsto> val"

inductive_cases MergeNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (MergeNode ends stateAfter next) \<mapsto> val"

inductive_cases MethodCallTargetNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (MethodCallTargetNode targetMethod arguments) \<mapsto> val"

inductive_cases MulNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (MulNode x y) \<mapsto> val"

inductive_cases NegateNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (NegateNode value) \<mapsto> val"

inductive_cases NewArrayNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (NewArrayNode length0 stateBefore next) \<mapsto> val"

inductive_cases NewInstanceNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (NewInstanceNode instanceClass stateBefore next) \<mapsto> val"

inductive_cases NotNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (NotNode value) \<mapsto> val"

inductive_cases OrNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (OrNode x y) \<mapsto> val"

inductive_cases ParameterNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (ParameterNode index) \<mapsto> val"

inductive_cases PhiNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (PhiNode nid0 merge) \<mapsto> val"

inductive_cases ProxyNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (ProxyNode loopExit) \<mapsto> val"

inductive_cases ReturnNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (ReturnNode result memoryMap) \<mapsto> val"

inductive_cases ShortCircuitOrNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (ShortCircuitOrNode x y) \<mapsto> val"

inductive_cases SignedDivNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (SignedDivNode x y zeroCheck stateBefore next) \<mapsto> val"

inductive_cases StartNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (StartNode stateAfter next) \<mapsto> val"

inductive_cases StoreFieldNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (StoreFieldNode field value stateAfter object next) \<mapsto> val"

inductive_cases SubNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (SubNode x y) \<mapsto> val"

inductive_cases SwitchNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (SwitchNode value successors) \<mapsto> val"

inductive_cases UnaryArithmeticNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (UnaryArithmeticNode value) \<mapsto> val"

inductive_cases UnaryNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (UnaryNode value) \<mapsto> val"

inductive_cases UnwindNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (UnwindNode exception) \<mapsto> val"

inductive_cases ValueNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (ValueNode) \<mapsto> val"

inductive_cases ValuePhiNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (ValuePhiNode nid0 values merge) \<mapsto> val"

inductive_cases ValueProxyNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (ValueProxyNode value loopExit) \<mapsto> val"

inductive_cases XorNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (XorNode x y) \<mapsto> val"
(* nodeout *)


inductive_cases RefNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (RefNode ref) \<mapsto> val"

inductive_cases SubstrateMethodCallTargetNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (SubstrateMethodCallTargetNode targetMethod args) \<mapsto> val"

inductive_cases NoNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> nid (NoNode) \<mapsto> val"


lemmas EvalE = 
ValueNodeE
FixedNodeE
AbstractEndNodeE
EndNodeE
LoopEndNodeE
FixedWithNextNodeE
AccessFieldNodeE
LoadFieldNodeE
StoreFieldNodeE
DeoptimizingFixedWithNextNodeE
AbstractNewObjectNodeE
NewInstanceNodeE
AbstractNewArrayNodeE
NewArrayNodeE
DynamicNewArrayNodeE
AbstractBeginNodeE
BeginNodeE
KillingBeginNodeE
BeginStateSplitNodeE
LoopExitNodeE
AbstractMergeNodeE
MergeNodeE
LoopBeginNodeE
StartNodeE
ReturnNodeE
ControlSplitNodeE
IfNodeE
SwitchNodeE
FloatingNodeE
AbstractLocalNodeE
ParameterNodeE
ProxyNodeE
ValueProxyNodeE
PhiNodeE
ValuePhiNodeE
ConstantNodeE
ConditionalNodeE
UnaryNodeE
UnaryArithmeticNodeE
NotNodeE
NegateNodeE
LogicNegationNodeE
AbsNodeE
BinaryNodeE
BinaryArithmeticNodeE
AddNodeE
XorNodeE
AndNodeE
SubNodeE
MulNodeE
OrNodeE
ShortCircuitOrNodeE
IntegerEqualsNodeE
IntegerLessThanNodeE
FrameStateE
MethodCallTargetNodeE
InvokeNodeE
SignedDivNodeE
SubstrateMethodCallTargetNodeE
ExceptionObjectNodeE
InvokeWithExceptionNodeE
BytecodeExceptionNodeE
UnwindNodeE
RefNodeE
NoNodeE


(* Try proving 'inverted rules' for eval. *)
lemma "evalAddNode" : "g m \<turnstile> nid (AddNode x y) \<mapsto> val \<Longrightarrow>
  (\<exists> v1. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v1) \<and>
    (\<exists> v2. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v2) \<and>
       val = IntVal(v1 + v2)))"
  using AddNodeE by auto

lemma not_floating: "(\<exists>y ys. (successors_of n) = y # ys) \<longrightarrow> \<not>(is_floating_node n)"
  unfolding is_floating_node.simps
  by (induct "n"; simp add: neq_Nil_conv)

(*
This lemma should be provable once we define an eval
rule for all floating nodes but might be stunted by some
undefined behaviour at the moment
*)
lemma evalFloating:
  assumes "\<forall>i . List.member (inputs_of (kind g nid)) i \<longrightarrow> (\<exists>v. (g m \<turnstile> i (kind g i) \<mapsto> IntVal v))"
  assumes "is_floating_node (kind g nid)"
  shows "g m \<turnstile> nid (kind g nid) \<mapsto> val"
proof (induction "kind g nid")
  case (AbsNode x)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_AbsNode AbsNode
    by (metis member_rec(1))
  then have "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  then show ?case using eval.AbsNode AbsNode sorry
next
case (AbstractBeginNode x)
  then show ?case 
    using assms(2) not_floating successors_of_AbstractBeginNode by metis
next
  case AbstractEndNode
  then show ?case using assms(2)
    unfolding is_floating_node.simps
    using has_control_flow.simps(2) by simp
next
  case AbstractLocalNode
  then show ?case sorry
next
  case (AbstractMergeNode x1a x2a x3)
  then show ?case 
    using assms(2) not_floating successors_of_AbstractMergeNode by metis
next
  case (AbstractNewArrayNode x1a x2a x3)
  then show ?case
    using assms(2) not_floating successors_of_AbstractNewArrayNode by metis
next
  case (AbstractNewObjectNode x1a x2a)
  then show ?case
    using assms(2) not_floating successors_of_AbstractNewObjectNode by metis
next
  case (AccessFieldNode x1a x2a)
  then show ?case
    using assms(2) not_floating successors_of_AccessFieldNode by metis
next
  case (AddNode x y)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_AddNode AddNode
    by (metis member_rec(1))
  then have x: "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  have "List.member (inputs_of (kind g nid)) y"
    using inputs_of_AddNode AddNode
    by (metis member_rec(1))
  then have y: "\<exists>v. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using x y eval.AddNode AddNode sorry
next
  case (AndNode x y)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_AndNode AndNode
    by (metis member_rec(1))
  then have x: "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  have "List.member (inputs_of (kind g nid)) y"
    using inputs_of_AndNode AndNode
    by (metis member_rec(1))
  then have y: "\<exists>v. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using x y eval.AndNode AndNode sorry
next
  case (BeginNode x)
  then show ?case
    using assms(2) not_floating successors_of_BeginNode by metis
next
  case (BeginStateSplitNode x1a x2a)
  then show ?case
    using assms(2) not_floating successors_of_BeginStateSplitNode by metis
next
  case (BinaryArithmeticNode x1a x2a)
  then show ?case sorry
next
  case (BinaryNode x1a x2a)
  then show ?case sorry
next
  case (BytecodeExceptionNode x1a x2a x3)
  then show ?case
    using assms(2) not_floating successors_of_BytecodeExceptionNode by metis
next
  case (ConditionalNode cond t f)
  have "List.member (inputs_of (kind g nid)) cond"
    using inputs_of_ConditionalNode ConditionalNode
    by (metis member_rec(1))
  then have cond: "\<exists>v. (g m \<turnstile> cond (kind g cond) \<mapsto> IntVal v)"
    using assms(1) by auto
  have "List.member (inputs_of (kind g nid)) t"
    using inputs_of_ConditionalNode ConditionalNode
    by (metis member_rec(1))
  then have t: "\<exists>v. (g m \<turnstile> t (kind g t) \<mapsto> IntVal v)"
    using assms(1) by auto
  have "List.member (inputs_of (kind g nid)) f"
    using inputs_of_ConditionalNode ConditionalNode
    by (metis member_rec(1))
  then have f: "\<exists>v. (g m \<turnstile> f (kind g f) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using cond t f eval.ConditionalNode ConditionalNode sorry
next
  case (ConstantNode x)
  then show ?case using eval.ConstantNode sorry
next
  case ControlSplitNode
  then show ?case sorry
next
  case (DeoptimizingFixedWithNextNode x1a x2a)
  then show ?case
    using assms(2) not_floating successors_of_DeoptimizingFixedWithNextNode by metis
next
  case (DynamicNewArrayNode x1a x2a x3 x4 x5)
  then show ?case
    using assms(2) not_floating successors_of_DynamicNewArrayNode by metis
next
  case EndNode
  then show ?case using assms(2)
    unfolding is_floating_node.simps
    using has_control_flow.simps(2) by simp
next
  case (ExceptionObjectNode x1a x2a)
  then show ?case
    using assms(2) not_floating successors_of_ExceptionObjectNode by metis
next
  case FixedNode
  then show ?case sorry
next
  case (FixedWithNextNode x)
  then show ?case
    using assms(2) not_floating successors_of_FixedWithNextNode by metis
next
  case FloatingNode
  then show ?case sorry
next
  case (FrameState x1a x2a x3 x4)
  then show ?case sorry
next
  case (IfNode x1a x2a x3)
  then show ?case
    using assms(2) not_floating successors_of_IfNode by metis
next
  case (IntegerEqualsNode x y)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_IntegerEqualsNode IntegerEqualsNode
    by (metis member_rec(1))
  then have x: "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  have "List.member (inputs_of (kind g nid)) y"
    using inputs_of_IntegerEqualsNode IntegerEqualsNode
    by (metis member_rec(1))
  then have y: "\<exists>v. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using x y eval.IntegerEqualsNode IntegerEqualsNode sorry
next
  case (IntegerLessThanNode x y)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_IntegerLessThanNode IntegerLessThanNode
    by (metis member_rec(1))
  then have x: "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  have "List.member (inputs_of (kind g nid)) y"
    using inputs_of_IntegerLessThanNode IntegerLessThanNode
    by (metis member_rec(1))
  then have y: "\<exists>v. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using x y eval.IntegerLessThanNode IntegerLessThanNode sorry
next
  case (InvokeNode x1a x2a x3 x4 x5 x6)
  then show ?case
    using assms(2) not_floating successors_of_InvokeNode by metis
next
  case (InvokeWithExceptionNode x1a x2a x3 x4 x5 x6 x7)
  then show ?case
    using assms(2) not_floating successors_of_InvokeWithExceptionNode by metis
next
  case (KillingBeginNode x)
  then show ?case
    using assms(2) not_floating successors_of_KillingBeginNode by metis
next
  case (LoadFieldNode x1a x2a x3)
  then show ?case
    using assms(2) not_floating successors_of_LoadFieldNode by metis
next
  case (LogicNegationNode x)
  then show ?case sorry
next
  case (LoopBeginNode x1a x2a x3 x4)
  then show ?case
    using assms(2) not_floating successors_of_LoopBeginNode by metis
next
  case (LoopEndNode x)
  then show ?case using assms(2)
    unfolding is_floating_node.simps
    using has_control_flow.simps(3) by metis
next
  case (LoopExitNode x1a x2a x3)
  then show ?case
    using assms(2) not_floating successors_of_LoopExitNode by metis
next
  case (MergeNode x1a x2a x3)
  then show ?case
    using assms(2) not_floating successors_of_MergeNode by metis
next
  case (MethodCallTargetNode x y)
  show ?thesis sorry
next
  case (MulNode x y)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_MulNode MulNode
    by (metis member_rec(1))
  then have x: "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  have "List.member (inputs_of (kind g nid)) y"
    using inputs_of_MulNode MulNode
    by (metis member_rec(1))
  then have y: "\<exists>v. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using x y eval.MulNode MulNode sorry
next
  case (NegateNode x)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_NegateNode NegateNode
    by (metis member_rec(1))
  then have x: "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using x eval.NegateNode NegateNode sorry
next
  case (NewArrayNode x1a x2a x3)
  then show ?case
    using assms(2) not_floating successors_of_NewArrayNode by metis
next
  case (NewInstanceNode x1a x2a x3)
  then show ?case
    using assms(2) not_floating successors_of_NewInstanceNode by metis
next
  case (NotNode x)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_NotNode NotNode
    by (metis member_rec(1))
  then have x: "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using x (*eval.NotNode*) NotNode sorry (* no rule *)
next
  case (OrNode x y)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_OrNode OrNode
    by (metis member_rec(1))
  then have x: "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  have "List.member (inputs_of (kind g nid)) y"
    using inputs_of_OrNode OrNode
    by (metis member_rec(1))
  then have y: "\<exists>v. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using x y eval.OrNode OrNode sorry
next
  case (ParameterNode x)
  then show ?case using eval.ParameterNode sorry
next
  case (PhiNode x1a x2a)
  then show ?case using eval.PhiNode sorry
next
  case (ProxyNode x)
  then show ?case (*using eval.ProxyNode*) sorry (* no rule *)
next
  case (ReturnNode x1a x2a)
  then show ?case sorry
next
  case (ShortCircuitOrNode x y)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_ShortCircuitOrNode ShortCircuitOrNode
    by (metis member_rec(1))
  then have x: "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  have "List.member (inputs_of (kind g nid)) y"
    using inputs_of_ShortCircuitOrNode ShortCircuitOrNode
    by (metis member_rec(1))
  then have y: "\<exists>v. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using x y eval.ShortCircuitOrNode ShortCircuitOrNode sorry
next
  case (SignedDivNode x1a x2a x3 x4 x5)
  then show ?case
    using assms(2) not_floating successors_of_SignedDivNode by metis
next
  case (StartNode x1a x2a)
  then show ?case
    using assms(2) not_floating successors_of_StartNode by metis
next
  case (StoreFieldNode x1a x2a x3 x4 x5)
  then show ?case
    using assms(2) not_floating successors_of_StoreFieldNode by metis
next
  case (SubNode x y)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_SubNode SubNode
    by (metis member_rec(1))
  then have x: "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  have "List.member (inputs_of (kind g nid)) y"
    using inputs_of_SubNode SubNode
    by (metis member_rec(1))
  then have y: "\<exists>v. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using x y eval.SubNode SubNode sorry
next
  case (SwitchNode x1a x2a)
  then show ?case sorry
next
  case (UnaryArithmeticNode x)
  then show ?case sorry
next
  case (UnaryNode x)
  then show ?case sorry
next
  case (UnwindNode x)
  then show ?case sorry
next
  case ValueNode
  then show ?case sorry
next
  case (ValuePhiNode x1a x2a x3)
  then show ?case sorry
next
  case (ValueProxyNode c x2a)
  have "List.member (inputs_of (kind g nid)) c"
    using inputs_of_ValueProxyNode ValueProxyNode
    by (metis member_rec(1))
  then have c: "\<exists>v. (g m \<turnstile> c (kind g c) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using c eval.ValueProxyNode ValueProxyNode sorry
next
  case (XorNode x y)
  have "List.member (inputs_of (kind g nid)) x"
    using inputs_of_XorNode XorNode
    by (metis member_rec(1))
  then have x: "\<exists>v. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v)"
    using assms(1) by auto
  have "List.member (inputs_of (kind g nid)) y"
    using inputs_of_XorNode XorNode
    by (metis member_rec(1))
  then have y: "\<exists>v. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v)"
    using assms(1) by auto
  show ?case
    using x y eval.XorNode XorNode sorry
next
  case (SubstrateMethodCallTargetNode x1a x2a)
  then show ?case sorry
next
  case (RefNode x)
  then show ?case sorry
next
  case (NoNode)
  then show ?case sorry
qed


text \<open>A top-level goal: eval is deterministic.\<close>
theorem "evalDet":
   "(g m \<turnstile> nid node \<mapsto> val1) \<Longrightarrow>
   (\<forall> val2. ((g m \<turnstile> nid node \<mapsto> val2) \<longrightarrow> val1 = val2))"
  apply (induction rule: "eval.induct")
  by (rule allI; rule impI; elim EvalE; auto)+

end

