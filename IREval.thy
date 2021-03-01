section \<open>Inductive evaluation semantics of floating nodes\<close>

theory IREval
  imports
    IRNodeHierarchy
    IRGraph
begin

datatype MapState =
  MapState
    (m_values: "ID \<Rightarrow> Value")
    (m_params: "Value list")

definition new_map_state :: "MapState" where
  "new_map_state = MapState (\<lambda>x. UndefVal) []"

fun m_val :: "MapState \<Rightarrow> ID \<Rightarrow> Value" where
  "m_val m nid = (m_values m) nid"

fun m_set :: "ID \<Rightarrow> Value \<Rightarrow> MapState \<Rightarrow> MapState" where
  "m_set nid v (MapState m p) = MapState (m(nid := v)) p"

fun m_param :: "IRGraph \<Rightarrow> MapState \<Rightarrow> ID \<Rightarrow> Value" where
  "m_param g m nid = (case (kind g nid) of
    (ParameterNode i) \<Rightarrow> (m_params m)!i |
    _ \<Rightarrow> UndefVal)"

fun set_params :: "MapState \<Rightarrow> Value list \<Rightarrow> MapState" where
  "set_params (MapState m _) vs = MapState m vs"

fun new_map :: "Value list \<Rightarrow> MapState" where
  "new_map ps = set_params new_map_state ps"


fun val_to_bool :: "Value \<Rightarrow> bool" where
  "val_to_bool (IntVal bits val) = (if val = 0 then False else True)" |
  "val_to_bool v = False"

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal 1 1)" |
  "bool_to_val False = (IntVal 1 0)"


(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index v (x # xs) = (if (x=v) then 0 else find_index v xs + 1)"

fun phi_list :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "phi_list g nid = 
    (filter (\<lambda>x.(isPhiNodeType (kind g x)))
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

fun any_usage :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID" where
  "any_usage g nid = hd (sorted_list_of_set (usages g nid))"

inductive
  eval :: "IRGraph \<Rightarrow> MapState \<Rightarrow> IRNode \<Rightarrow> Value \<Rightarrow> bool" ("_ _ \<turnstile> _ \<mapsto> _" 55)
  for g where

  ConstantNode:
  "g m \<turnstile> (ConstantNode c) \<mapsto> c" |

  ParameterNode:
  "g m \<turnstile> (ParameterNode i) \<mapsto> (m_params m)!i" |

  ValuePhiNode:
  "g m \<turnstile> (ValuePhiNode nid _ _) \<mapsto> m_val m nid" |

  ValueProxyNode:
  "\<lbrakk>g m \<turnstile> (kind g c) \<mapsto> val\<rbrakk>
    \<Longrightarrow> g m \<turnstile> (ValueProxyNode c _) \<mapsto> val" |

(* Unary arithmetic operators *)

  AbsNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (AbsNode x) \<mapsto> IntVal b (if v<0 then -v else v)" |

  NegateNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (NegateNode x) \<mapsto> IntVal b (-v)" |

(* Binary arithmetic operators *)

  AddNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    g m \<turnstile> (kind g y) \<mapsto> IntVal b v2\<rbrakk>
    \<Longrightarrow> g m \<turnstile> (AddNode x y) \<mapsto> IntVal b (v1+v2)" |

  SubNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    g m \<turnstile> (kind g y) \<mapsto> IntVal b v2\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (SubNode x y) \<mapsto> IntVal b (v1-v2)" |

  MulNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    g m \<turnstile> (kind g y) \<mapsto> IntVal b v2\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (MulNode x y) \<mapsto> IntVal b (v1*v2)" |

(* TODO: this should be control-flow *)
  SignedDivNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    g m \<turnstile> (kind g y) \<mapsto> IntVal b v2\<rbrakk>
    \<Longrightarrow> g m \<turnstile> (SignedDivNode x y zeroCheck frameState next) \<mapsto> IntVal b (v1 div v2)" |

(* Binary logical bitwise operators *)

  AndNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    g m \<turnstile> (kind g y) \<mapsto> IntVal b v2\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (AndNode x y) \<mapsto> IntVal b (v1 AND v2)" |

  OrNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    g m \<turnstile> (kind g y) \<mapsto> IntVal b v2\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (OrNode x y) \<mapsto> IntVal b (v1 OR v2)" |

  XorNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    g m \<turnstile> (kind g y) \<mapsto> IntVal b v2\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (XorNode x y) \<mapsto> IntVal b (v1 XOR v2)" |

(* Comparison operators *)
(* NOTE: if we use IntVal(bool_to_int(v1=v2)), then code generation does not work! *)
  IntegerEqualsNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    g m \<turnstile> (kind g y) \<mapsto> IntVal b v2;
    val = bool_to_val(v1 = v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (IntegerEqualsNode x y) \<mapsto> val" |

  IntegerLessThanNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    g m \<turnstile> (kind g y) \<mapsto> IntVal b v2;
    val = bool_to_val(v1 < v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (IntegerLessThanNode x y) \<mapsto> val" |

  IsNullNode:
  "\<lbrakk>g m \<turnstile> (kind g obj) \<mapsto> ObjRef ref;
    val = bool_to_val(ref = None)\<rbrakk>
    \<Longrightarrow> g m \<turnstile> (IsNullNode obj) \<mapsto> val" |

(* Other nodes *)
(* Note that both branches are evaluated but only one is used.
   This is not an issue as evaluation is total (but may return UnDef) *)

  ConditionalNode:
  "\<lbrakk>g m \<turnstile> (kind g condition) \<mapsto> IntVal 1 cond;
    g m \<turnstile> (kind g trueExp) \<mapsto> IntVal b trueVal;
    g m \<turnstile> (kind g falseExp) \<mapsto> IntVal b falseVal;
    val = IntVal b (if cond \<noteq> 0 then trueVal else falseVal)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (ConditionalNode condition trueExp falseExp) \<mapsto> val" |

(* Note that v2 may evaluate to UnDef but is not used if v1 is true *)

  ShortCircuitOrNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    g m \<turnstile> (kind g y) \<mapsto> IntVal b v2;
    val = IntVal b (if v1 \<noteq> 0 then v1 else v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (ShortCircuitOrNode x y) \<mapsto> val" |

  LogicNegationNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> IntVal b v1;
    val = IntVal b (NOT v1)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> (LogicNegationNode x) \<mapsto> val" |

(* Access the value returned by the most recent call *)
  InvokeNodeEval:
  "g m \<turnstile> (InvokeNode nid _ _ _ _ _) \<mapsto> m_val m nid" |

  InvokeWithExceptionNodeEval:
  "g m \<turnstile> (InvokeWithExceptionNode nid _ _ _ _ _ _) \<mapsto> m_val m nid" |

  NewInstanceNode:
  "g m \<turnstile> (NewInstanceNode nid class stateBefore next) \<mapsto> m_val m nid" |

  LoadFieldNode:
  "g m \<turnstile> (LoadFieldNode nid _ _ _) \<mapsto> m_val m nid" |

  (*TODO: Unclear how we should handle PiNode yet*)
  PiNode:
  "\<lbrakk>g m \<turnstile> (kind g object) \<mapsto> val\<rbrakk>
    \<Longrightarrow> g m \<turnstile> (PiNode object guard) \<mapsto> val" |

  RefNode:
  "\<lbrakk>g m \<turnstile> (kind g x) \<mapsto> val\<rbrakk>
    \<Longrightarrow> g m \<turnstile> (RefNode x) \<mapsto> val" 

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as evalE) eval .

text \<open>Representative induction rules for eval\<close>
text_raw \<open>\Snip{ExpressionSemantics}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] eval.ConstantNode [no_vars]}}{eval:const}
\induct{@{thm[mode=Rule] eval.ParameterNode [no_vars]}}{eval:param}
\induct{@{thm[mode=Rule] eval.ValuePhiNode [no_vars]}}{eval:phi}
\induct{@{thm[mode=Rule] eval.NegateNode [no_vars]}}{eval:neg}
\induct{@{thm[mode=Rule] eval.AddNode [no_vars]}}{eval:add}
\induct{@{thm[mode=Rule] eval.InvokeNodeEval [no_vars]}}{eval:invoke}
\induct{@{thm[mode=Rule] eval.LoadFieldNode [no_vars]}}{eval:load}
\induct{@{thm[mode=Rule] eval.RefNode [no_vars]}}{eval:ref}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>


inductive
  eval_all :: "IRGraph \<Rightarrow> MapState \<Rightarrow> ID list \<Rightarrow> Value list \<Rightarrow> bool"
  ("_ _ \<turnstile> _ \<longmapsto> _" 55)
  for g where
  Base:
  "g m \<turnstile> [] \<longmapsto> []" |

  Transitive:
  "\<lbrakk>g m \<turnstile> (kind g nid) \<mapsto> v;
    g m \<turnstile> xs \<longmapsto> vs\<rbrakk>
   \<Longrightarrow> g m \<turnstile> (nid # xs) \<longmapsto> (v # vs)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as eval_allE) eval_all .

text_raw \<open>\Snip{EvalAll}%\<close>
text \<open>
\begin{center}
@{thm[mode=Rule] eval_all.Base [no_vars]}\\[8px]
@{thm[mode=Rule] eval_all.Transitive [no_vars]}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>

(* Test the eval predicates. *)
inductive eval_graph :: "IRGraph \<Rightarrow> ID \<Rightarrow> Value list \<Rightarrow> Value \<Rightarrow> bool"
  where
  "\<lbrakk>state = new_map ps;
    g state \<turnstile> (kind g nid) \<mapsto> val\<rbrakk>
    \<Longrightarrow> eval_graph g nid ps val"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) "eval_graph" .

(* 5*5 \<Rightarrow> 25 *)
values "{v. eval_graph eg2_sq 4 [IntVal 32 5] v}"

fun has_control_flow :: "IRNode \<Rightarrow> bool" where
  "has_control_flow n = (isAbstractEndNodeType n
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
  "g m \<turnstile> (AbsNode value) \<mapsto> val"

inductive_cases AddNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (AddNode x y) \<mapsto> val"

inductive_cases AndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (AndNode x y) \<mapsto> val"

inductive_cases BeginNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (BeginNode next) \<mapsto> val"

inductive_cases BytecodeExceptionNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (BytecodeExceptionNode arguments stateAfter next) \<mapsto> val"

inductive_cases ConditionalNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (ConditionalNode condition trueValue falseValue) \<mapsto> val"

inductive_cases ConstantNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (ConstantNode const) \<mapsto> val"

inductive_cases DynamicNewArrayNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (DynamicNewArrayNode elementType length0 voidClass stateBefore next) \<mapsto> val"

inductive_cases EndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (EndNode) \<mapsto> val"

inductive_cases ExceptionObjectNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (ExceptionObjectNode stateAfter next) \<mapsto> val"

inductive_cases FrameStateE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (FrameState monitorIds outerFrameState values virtualObjectMappings) \<mapsto> val"

inductive_cases IfNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (IfNode condition trueSuccessor falseSuccessor) \<mapsto> val"

inductive_cases IntegerEqualsNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (IntegerEqualsNode x y) \<mapsto> val"

inductive_cases IntegerLessThanNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (IntegerLessThanNode x y) \<mapsto> val"

inductive_cases InvokeNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (InvokeNode nid0 callTarget classInit stateDuring stateAfter next) \<mapsto> val"

inductive_cases InvokeWithExceptionNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (InvokeWithExceptionNode nid0 callTarget classInit stateDuring stateAfter next exceptionEdge) \<mapsto> val"

inductive_cases IsNullNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (IsNullNode value) \<mapsto> val"

inductive_cases KillingBeginNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (KillingBeginNode next) \<mapsto> val"

inductive_cases LoadFieldNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (LoadFieldNode nid0 field object next) \<mapsto> val"

inductive_cases LogicNegationNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (LogicNegationNode value) \<mapsto> val"

inductive_cases LoopBeginNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (LoopBeginNode ends overflowGuard stateAfter next) \<mapsto> val"

inductive_cases LoopEndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (LoopEndNode loopBegin) \<mapsto> val"

inductive_cases LoopExitNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (LoopExitNode loopBegin stateAfter next) \<mapsto> val"

inductive_cases MergeNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (MergeNode ends stateAfter next) \<mapsto> val"

inductive_cases MethodCallTargetNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (MethodCallTargetNode targetMethod arguments) \<mapsto> val"

inductive_cases MulNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (MulNode x y) \<mapsto> val"

inductive_cases NegateNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (NegateNode value) \<mapsto> val"

inductive_cases NewArrayNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (NewArrayNode length0 stateBefore next) \<mapsto> val"

inductive_cases NewInstanceNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (NewInstanceNode nid0 instanceClass stateBefore next) \<mapsto> val"

inductive_cases NotNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (NotNode value) \<mapsto> val"

inductive_cases OrNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (OrNode x y) \<mapsto> val"

inductive_cases ParameterNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (ParameterNode index) \<mapsto> val"

inductive_cases PiNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (PiNode object guard) \<mapsto> val"

inductive_cases ReturnNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (ReturnNode result memoryMap) \<mapsto> val"

inductive_cases ShortCircuitOrNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (ShortCircuitOrNode x y) \<mapsto> val"

inductive_cases SignedDivNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (SignedDivNode x y zeroCheck stateBefore next) \<mapsto> val"

inductive_cases StartNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (StartNode stateAfter next) \<mapsto> val"

inductive_cases StoreFieldNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (StoreFieldNode nid0 field value stateAfter object next) \<mapsto> val"

inductive_cases SubNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (SubNode x y) \<mapsto> val"

inductive_cases UnwindNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (UnwindNode exception) \<mapsto> val"

inductive_cases ValuePhiNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (ValuePhiNode nid0 values merge) \<mapsto> val"

inductive_cases ValueProxyNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (ValueProxyNode value loopExit) \<mapsto> val"

inductive_cases XorNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (XorNode x y) \<mapsto> val"

inductive_cases NoNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (NoNode) \<mapsto> val"
(* nodeout *)


inductive_cases RefNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g m \<turnstile> (RefNode ref) \<mapsto> val"


lemmas EvalE = 
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
ExceptionObjectNodeE
InvokeWithExceptionNodeE
BytecodeExceptionNodeE
UnwindNodeE
RefNodeE
IsNullNodeE
PiNodeE
NoNodeE


(* Try proving 'inverted rules' for eval. *)
lemma "evalAddNode" : "g m \<turnstile> (AddNode x y) \<mapsto> val \<Longrightarrow>
  (\<exists> b v1. (g m \<turnstile> (kind g x) \<mapsto> IntVal b v1) \<and>
    (\<exists> v2. (g m \<turnstile> (kind g y) \<mapsto> IntVal b v2) \<and>
       val = IntVal b (v1 + v2)))"
  using AddNodeE by auto

lemma not_floating: "(\<exists>y ys. (successors_of n) = y # ys) \<longrightarrow> \<not>(is_floating_node n)"
  unfolding is_floating_node.simps
  by (induct "n"; simp add: neq_Nil_conv)


text \<open>A top-level goal: eval is deterministic.\<close>
theorem "evalDet":
   "(g m \<turnstile> node \<mapsto> val1) \<Longrightarrow>
   (\<forall> val2. ((g m \<turnstile> node \<mapsto> val2) \<longrightarrow> val1 = val2))"
  apply (induction rule: "eval.induct")
  by (rule allI; rule impI; elim EvalE; auto)+

theorem "evalAllDet":
   "(g m \<turnstile> nodes \<longmapsto> vals1) \<Longrightarrow>
   (\<forall> vals2. ((g m \<turnstile> nodes \<longmapsto> vals2) \<longrightarrow> vals1 = vals2))"
  apply (induction rule: "eval_all.induct")
  using eval_all.cases apply blast
  by (metis evalDet eval_all.cases list.discI list.inject)

end

