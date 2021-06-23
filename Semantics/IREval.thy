section \<open>Data-flow Semantics\<close>

theory IREval
  imports
    Graph.IRGraph
begin

text \<open>
We define the semantics of data-flow nodes as big-step operational semantics.

Data-flow nodes are evaluated in the context of the @{typ IRGraph} and a method state
(currently called MapState in the theories for historical reasons).

The method state consists of the values for each method parameter, references to
method parameters use an index of the parameter wihtin the parameter list, as such
we store a list of parameter values which are looked up at parameter references.

The method state also stores a mapping of node ids to values. The contents of this
mapping is calculates during the traversal of the control flow graph.

As a concrete example, as the @{term SignedDivNode} can have side-effects
(during division by zero), it is treated part of the control-flow as the data-flow 
is specified to be side-effect free.
As a result, the control-flow semantics for @{term SignedDivNode} calculates the value of a node
and maps the node identifier to the value within the method state.
The data-flow semantics then just reads the value stored in the method state for the node.
\<close>

type_synonym MapState = "ID \<Rightarrow> Value"
type_synonym Params = "Value list"

definition new_map_state :: "MapState" where
  "new_map_state = (\<lambda>x. UndefVal)"

fun val_to_bool :: "Value \<Rightarrow> bool" where
  "val_to_bool (IntVal bits val) = (if val = 0 then False else True)" |
  "val_to_bool v = False"

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal 1 1)" |
  "bool_to_val False = (IntVal 1 0)"


(* TODO: move the following phi helpers to step semantics? *)
(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index v (x # xs) = (if (x=v) then 0 else find_index v xs + 1)"

fun phi_list :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "phi_list g nid = 
    (filter (\<lambda>x.(is_PhiNode (kind g x)))
      (sorted_list_of_set (usages g nid)))"

fun input_index :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index g n n' = find_index n' (inputs_of (kind g n))"

fun phi_inputs :: "IRGraph \<Rightarrow> nat \<Rightarrow> ID list \<Rightarrow> ID list" where
  "phi_inputs g i nodes = (map (\<lambda>n. (inputs_of (kind g n))!(i + 1)) nodes)"

fun set_phis :: "ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_phis [] [] m = m" |
  "set_phis (nid # xs) (v # vs) m = (set_phis xs vs (m(nid := v)))" |
  "set_phis [] (v # vs) m = m" |
  "set_phis (x # xs) [] m = m"

inductive
  eval :: "IRGraph \<Rightarrow> MapState \<Rightarrow> Params \<Rightarrow> IRNode \<Rightarrow> Value \<Rightarrow> bool" ("[_, _, _] \<turnstile> _ \<mapsto> _" 55)
  for g m p where

  ConstantNode:
  "[g, m, p] \<turnstile> (ConstantNode c) \<mapsto> c" |

  ParameterNode:
  "[g, m, p] \<turnstile> (ParameterNode i) \<mapsto> p!i" |

  ValuePhiNode:
  "[g, m, p] \<turnstile> (ValuePhiNode nid _ _) \<mapsto> m nid" |

  ValueProxyNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g c) \<mapsto> val\<rbrakk>
    \<Longrightarrow> [g, m, p] \<turnstile> (ValueProxyNode c _) \<mapsto> val" |

  \<comment> \<open>Unary arithmetic operators\<close>

  AbsNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> IntVal b v\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (AbsNode x) \<mapsto> if v < 0 then (intval_sub (IntVal b 0) (IntVal b v)) else (IntVal b v)" |

  NegateNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> v\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (NegateNode x) \<mapsto> (IntVal (v_bits v) 0) - v" |

  NotNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> v;
    nv = intval_not v\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (NotNode x) \<mapsto> nv" |
    
  \<comment> \<open>Binary arithmetic operators\<close>

  AddNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> v1;
    [g, m, p] \<turnstile> (kind g y) \<mapsto> v2\<rbrakk>
    \<Longrightarrow> [g, m, p] \<turnstile> (AddNode x y) \<mapsto> v1 + v2" |

  SubNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> v1;
    [g, m, p] \<turnstile> (kind g y) \<mapsto> v2\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (SubNode x y) \<mapsto> v1 - v2" |

  MulNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> v1;
    [g, m, p] \<turnstile> (kind g y) \<mapsto> v2\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (MulNode x y) \<mapsto> v1 * v2" |

  SignedDivNode:
  "[g, m, p] \<turnstile> (SignedDivNode nid _ _ _ _ _) \<mapsto> m nid" |

  SignedRemNode:
  "[g, m, p] \<turnstile> (SignedRemNode nid _ _ _ _ _) \<mapsto> m nid" |

  \<comment> \<open>Binary logical bitwise operators\<close>

  AndNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> v1;
    [g, m, p] \<turnstile> (kind g y) \<mapsto> v2\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (AndNode x y) \<mapsto> intval_and  v1 v2" |

  OrNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> v1;
    [g, m, p] \<turnstile> (kind g y) \<mapsto> v2\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (OrNode x y) \<mapsto> intval_or v1 v2" |

  XorNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> v1;
    [g, m, p] \<turnstile> (kind g y) \<mapsto> v2\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (XorNode x y) \<mapsto> intval_xor v1 v2" |

  \<comment> \<open>Comparison operators\<close>
(* NOTE: if we use IntVal(bool_to_int(v1=v2)), then code generation does not work! *)
  IntegerEqualsNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    [g, m, p] \<turnstile> (kind g y) \<mapsto> IntVal b v2;
    val = bool_to_val(v1 = v2)\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (IntegerEqualsNode x y) \<mapsto> val" |

  IntegerLessThanNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    [g, m, p] \<turnstile> (kind g y) \<mapsto> IntVal b v2;
    val = bool_to_val(v1 < v2)\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (IntegerLessThanNode x y) \<mapsto> val" |

  IsNullNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g obj) \<mapsto> ObjRef ref;
    val = bool_to_val(ref = None)\<rbrakk>
    \<Longrightarrow> [g, m, p] \<turnstile> (IsNullNode obj) \<mapsto> val" |

  \<comment> \<open>Other nodes\<close>
(* Note that both branches are evaluated but only one is used.
   This is not an issue as evaluation is total (but may return UnDef) *)

  ConditionalNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g condition) \<mapsto> IntVal 1 cond;
    [g, m, p] \<turnstile> (kind g trueExp) \<mapsto> IntVal b trueVal;
    [g, m, p] \<turnstile> (kind g falseExp) \<mapsto> IntVal b falseVal;
    val = IntVal b (if cond \<noteq> 0 then trueVal else falseVal)\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (ConditionalNode condition trueExp falseExp) \<mapsto> val" |

(* Note that v2 may evaluate to UnDef but is not used if v1 is true *)

  ShortCircuitOrNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    [g, m, p] \<turnstile> (kind g y) \<mapsto> IntVal b v2;
    val = IntVal b (if v1 \<noteq> 0 then v1 else v2)\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (ShortCircuitOrNode x y) \<mapsto> val" |

  LogicNegationNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> IntVal 1 v1;
    neg_v1 = (\<not>(val_to_bool (IntVal 1 v1)));
    val = bool_to_val neg_v1\<rbrakk> 
    \<Longrightarrow> [g, m, p] \<turnstile> (LogicNegationNode x) \<mapsto> val" |

(* Access the value returned by the most recent call *)
  InvokeNodeEval:
  "[g, m, p] \<turnstile> (InvokeNode nid _ _ _ _ _) \<mapsto> m nid" |

  InvokeWithExceptionNodeEval:
  "[g, m, p] \<turnstile> (InvokeWithExceptionNode nid _ _ _ _ _ _) \<mapsto> m nid" |

  NewInstanceNode:
  "[g, m, p] \<turnstile> (NewInstanceNode nid _ _ _) \<mapsto> m nid" |

  LoadFieldNode:
  "[g, m, p] \<turnstile> (LoadFieldNode nid _ _ _) \<mapsto> m nid" |

  (*TODO: Unclear how we should handle PiNode yet*)
  PiNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g object) \<mapsto> val\<rbrakk>
    \<Longrightarrow> [g, m, p] \<turnstile> (PiNode object guard) \<mapsto> val" |

  RefNode:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g x) \<mapsto> val\<rbrakk>
    \<Longrightarrow> [g, m, p] \<turnstile> (RefNode x) \<mapsto> val" 

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as evalE) eval .

text \<open>
The step semantics for phi nodes requires all the input nodes of the
phi node to be evaluated to a value at the same time.

We introduce the @{text eval_all} relation to handle the evaluation
of a list of node identifiers in parallel. As the evaluation semantics
are side-effect free this is trivial.
\<close>
inductive
  eval_all :: "IRGraph \<Rightarrow> MapState \<Rightarrow> Params \<Rightarrow> ID list \<Rightarrow> Value list \<Rightarrow> bool"
  ("[_, _, _] \<turnstile> _ \<longmapsto> _" 55)
  for g m p where
  Base:
  "[g, m, p] \<turnstile> [] \<longmapsto> []" |

  Transitive:
  "\<lbrakk>[g, m, p] \<turnstile> (kind g nid) \<mapsto> v;
    [g, m, p] \<turnstile> xs \<longmapsto> vs\<rbrakk>
   \<Longrightarrow> [g, m, p] \<turnstile> (nid # xs) \<longmapsto> (v # vs)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as eval_allE) eval_all .

(* Test the eval predicates. *)
inductive eval_graph :: "IRGraph \<Rightarrow> ID \<Rightarrow> Value list \<Rightarrow> Value \<Rightarrow> bool"
  where
  "\<lbrakk>[g, new_map_state, ps] \<turnstile> (kind g nid) \<mapsto> val\<rbrakk>
    \<Longrightarrow> eval_graph g nid ps val"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) "eval_graph" .

(* 5*5 \<Rightarrow> 25 *)
values "{v. eval_graph eg2_sq 4 [IntVal 32 5] v}"

fun has_control_flow :: "IRNode \<Rightarrow> bool" where
  "has_control_flow n = (is_AbstractEndNode n
    \<or> (length (successors_of n) > 0))"

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
  "[g, m, p] \<turnstile> (AbsNode value) \<mapsto> val"

inductive_cases AddNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (AddNode x y) \<mapsto> val"

inductive_cases AndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (AndNode x y) \<mapsto> val"

inductive_cases BeginNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (BeginNode next) \<mapsto> val"

inductive_cases BytecodeExceptionNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (BytecodeExceptionNode arguments stateAfter next) \<mapsto> val"

inductive_cases ConditionalNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (ConditionalNode condition trueValue falseValue) \<mapsto> val"

inductive_cases ConstantNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (ConstantNode const) \<mapsto> val"

inductive_cases DynamicNewArrayNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (DynamicNewArrayNode elementType length0 voidClass stateBefore next) \<mapsto> val"

inductive_cases EndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (EndNode) \<mapsto> val"

inductive_cases ExceptionObjectNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (ExceptionObjectNode stateAfter next) \<mapsto> val"

inductive_cases FrameStateE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (FrameState monitorIds outerFrameState values virtualObjectMappings) \<mapsto> val"

inductive_cases IfNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (IfNode condition trueSuccessor falseSuccessor) \<mapsto> val"

inductive_cases IntegerEqualsNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (IntegerEqualsNode x y) \<mapsto> val"

inductive_cases IntegerLessThanNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (IntegerLessThanNode x y) \<mapsto> val"

inductive_cases InvokeNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (InvokeNode nid0 callTarget classInit stateDuring stateAfter next) \<mapsto> val"

inductive_cases InvokeWithExceptionNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (InvokeWithExceptionNode nid0 callTarget classInit stateDuring stateAfter next exceptionEdge) \<mapsto> val"

inductive_cases IsNullNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (IsNullNode value) \<mapsto> val"

inductive_cases KillingBeginNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (KillingBeginNode next) \<mapsto> val"

inductive_cases LoadFieldNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (LoadFieldNode nid0 field object next) \<mapsto> val"

inductive_cases LogicNegationNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (LogicNegationNode value) \<mapsto> val"

inductive_cases LoopBeginNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (LoopBeginNode ends overflowGuard stateAfter next) \<mapsto> val"

inductive_cases LoopEndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (LoopEndNode loopBegin) \<mapsto> val"

inductive_cases LoopExitNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (LoopExitNode loopBegin stateAfter next) \<mapsto> val"

inductive_cases MergeNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (MergeNode ends stateAfter next) \<mapsto> val"

inductive_cases MethodCallTargetNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (MethodCallTargetNode targetMethod arguments) \<mapsto> val"

inductive_cases MulNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (MulNode x y) \<mapsto> val"

inductive_cases NegateNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (NegateNode value) \<mapsto> val"

inductive_cases NewArrayNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (NewArrayNode length0 stateBefore next) \<mapsto> val"

inductive_cases NewInstanceNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (NewInstanceNode nid0 instanceClass stateBefore next) \<mapsto> val"

inductive_cases NotNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (NotNode value) \<mapsto> val"

inductive_cases OrNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (OrNode x y) \<mapsto> val"

inductive_cases ParameterNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (ParameterNode index) \<mapsto> val"

inductive_cases PiNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (PiNode object guard) \<mapsto> val"

inductive_cases ReturnNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (ReturnNode result memoryMap) \<mapsto> val"

inductive_cases ShortCircuitOrNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (ShortCircuitOrNode x y) \<mapsto> val"

inductive_cases SignedDivNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (SignedDivNode nid0 x y zeroCheck stateBefore next) \<mapsto> val"

inductive_cases SignedRemNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (SignedRemNode nid0 x y zeroCheck stateBefore next) \<mapsto> val"

inductive_cases StartNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (StartNode stateAfter next) \<mapsto> val"

inductive_cases StoreFieldNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (StoreFieldNode nid0 field value stateAfter object next) \<mapsto> val"

inductive_cases SubNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (SubNode x y) \<mapsto> val"

inductive_cases UnwindNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (UnwindNode exception) \<mapsto> val"

inductive_cases ValuePhiNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (ValuePhiNode nid0 values merge) \<mapsto> val"

inductive_cases ValueProxyNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (ValueProxyNode value loopExit) \<mapsto> val"

inductive_cases XorNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (XorNode x y) \<mapsto> val"

inductive_cases NoNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (NoNode) \<mapsto> val"
(* nodeout *)


inductive_cases RefNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[g, m, p] \<turnstile> (RefNode ref) \<mapsto> val"


lemmas EvalE\<^marker>\<open>tag invisible\<close> = 
EndNodeE
LoopEndNodeE
LoadFieldNodeE
StoreFieldNodeE
NewInstanceNodeE
NewArrayNodeE
DynamicNewArrayNodeE
BeginNodeE
KillingBeginNodeE
LoopExitNodeE
MergeNodeE
LoopBeginNodeE
StartNodeE
ReturnNodeE
IfNodeE
ParameterNodeE
ValueProxyNodeE
ValuePhiNodeE
ConstantNodeE
ConditionalNodeE
NotNodeE
NegateNodeE
LogicNegationNodeE
AbsNodeE
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
SignedRemNodeE
ExceptionObjectNodeE
InvokeWithExceptionNodeE
BytecodeExceptionNodeE
UnwindNodeE
RefNodeE
IsNullNodeE
PiNodeE
NoNodeE


text \<open>
Here we show that using the elimination rules for eval we can
prove 'inverted rule' properties
\<close>
lemma "evalAddNode" : "[g, m, p] \<turnstile> (AddNode x y) \<mapsto> val \<Longrightarrow>
  (\<exists> v1. ([g, m, p] \<turnstile> (kind g x) \<mapsto> v1) \<and>
    (\<exists> v2. ([g, m, p] \<turnstile> (kind g y) \<mapsto> v2) \<and>
       val = intval_add v1 v2))"
  using AddNodeE plus_Value_def by metis

lemma not_floating: "(\<exists>y ys. (successors_of n) = y # ys) \<longrightarrow> \<not>(is_floating_node n)"
  unfolding is_floating_node.simps
  by (induct "n"; simp add: neq_Nil_conv)


text \<open>
We show that within the context of a graph and method state, the same
node will always evaluate to the same value and the semantics is therefore deterministic.
\<close>
theorem evalDet:
   "([g, m, p] \<turnstile> node \<mapsto> val1) \<Longrightarrow>
   (\<forall> val2. (([g, m, p] \<turnstile> node \<mapsto> val2) \<longrightarrow> val1 = val2))"
  apply (induction rule: "eval.induct")
  by (rule allI; rule impI; elim EvalE; auto)+

theorem evalAllDet:
   "([g, m, p] \<turnstile> nodes \<longmapsto> vals1) \<Longrightarrow>
   (\<forall> vals2. (([g, m, p] \<turnstile> nodes \<longmapsto> vals2) \<longrightarrow> vals1 = vals2))"
  apply (induction rule: "eval_all.induct")
  using eval_all.cases apply blast
  by (metis evalDet eval_all.cases list.discI list.inject)

end

