section \<open>Inductive evaluation semantics of floating nodes\<close>

theory IREval
  imports
    IRGraph
    "HOL-Word.More_Word"
begin

type_synonym int32 = "32 word"

datatype Value =
  UndefVal |
  IntVal int32

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


fun val_to_bool :: "int32 \<Rightarrow> bool" where
  "val_to_bool val = (if val = 0 then False else True)" 

fun bool_to_m_val :: "bool \<Rightarrow> Value" where
  "bool_to_m_val True = (IntVal 1)" |
  "bool_to_m_val False = (IntVal 0)"


(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index v (x # xs) = (if (x=v) then 0 else find_index v xs + 1)"

fun phi_list :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "phi_list g nid = 
    (filter (\<lambda>x.(is_PhiNode(kind g x)))
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
  "any_usage g nid = (sorted_list_of_set (usages g nid))!0"

inductive
  eval :: "IRGraph \<Rightarrow> MapState \<Rightarrow> ID \<Rightarrow> IRNode \<Rightarrow> Value \<Rightarrow> bool"
  (" _ _ \<turnstile> _ _ \<mapsto> _" 55)
  for g where

  ConstantNode:
  "\<lbrakk>val = (IntVal c)\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (ConstantNode c) \<mapsto> val" |

  ParameterNode:
  "\<lbrakk>val = (m_params m)!i\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (ParameterNode i) \<mapsto> val" |

  PhiNode:
  "\<lbrakk>val = m_val m nid\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (PhiNode _ _) \<mapsto> val" |

  ValuePhiNode:
  "\<lbrakk>val = m_val m nid\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (ValuePhiNode _ _) \<mapsto> val" |

  ValueProxyNode:
  "\<lbrakk>g m \<turnstile> c (kind g c) \<mapsto> val\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (ValueProxyNode _ c) \<mapsto> val" |

(* Unary arithmetic operators *)

  AbsNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (AbsNode x) \<mapsto> IntVal(if v<0 then -v else v)" |

  NegateNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (NegateNode x) \<mapsto> IntVal(-v)" |

(* Binary arithmetic operators *)
(* If we have separate rules for each node then we do not need binary_expr *)
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
    val = bool_to_m_val(v1 = v2)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (IntegerEqualsNode x y) \<mapsto> val" |

  IntegerLessThanNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<mapsto> IntVal(v2);
    val = bool_to_m_val(v1 < v2)\<rbrakk> 
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
    val = (if v1 \<noteq> 0 then IntVal(v1) else IntVal(v2))\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (ShortCircuitOrNode x y) \<mapsto> val" |

  LogicNegationNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> IntVal(v1);
    val = IntVal(NOT v1)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (LogicNegationNode x) \<mapsto> val" |

(* Access the value returned by the most recent call *)
  CallNodeEval:
  "\<lbrakk>val = m_val m nid\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (CallNode start args children) \<mapsto> val" |

  RefNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> val\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (RefNode x) \<mapsto> val" 

(* Duplication data evaluation with illustrative cases for paper *)
text_raw \<open>\snip{ExpressionSemantics}{\<close>
inductive
  data_eval :: "IRGraph \<Rightarrow> MapState \<Rightarrow> ID \<Rightarrow> IRNode \<Rightarrow> Value \<Rightarrow> bool"
  (" _ _ \<turnstile> _ _ \<longmapsto> _" 55)
  for g where

  ConstantNode:
  "\<lbrakk>val = (IntVal c)\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (ConstantNode c) \<longmapsto> val" |

  ParameterNode:
  "\<lbrakk>val = (m_params m)!i\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (ParameterNode i) \<longmapsto> val" |

  PhiNode:
  "\<lbrakk>val = m_val m nid\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (PhiNode _ _) \<longmapsto> val" |

  NegateNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<longmapsto> IntVal(v)\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (NegateNode x) \<longmapsto> IntVal(-v)" |

  AddNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<longmapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<longmapsto> IntVal(v2)\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (AddNode x y) \<longmapsto> IntVal(v1+v2)" |

  ShortCircuitOrNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<longmapsto> IntVal(v1);
    g m \<turnstile> y (kind g y) \<longmapsto> IntVal(v2);
    val = (if v1 \<noteq> 0 then IntVal(v1) else IntVal(v2))\<rbrakk> 
    \<Longrightarrow> g m \<turnstile> nid (ShortCircuitOrNode x y) \<longmapsto> val" |

  CallNodeEval:
  "\<lbrakk>val = m_val m nid\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (CallNode start args children) \<longmapsto> val" |

  RefNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<longmapsto> val\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (RefNode x) \<longmapsto> val" 
text_raw \<open>}%endsnip\<close>

code_pred [show_modes] eval .


inductive
  eval_all :: "IRGraph \<Rightarrow> ID list \<Rightarrow> MapState \<Rightarrow> Value list \<Rightarrow> bool"
  ("_ _ _\<longmapsto>_" 55)
  for g where
  "g [] m \<longmapsto> []" |
  "\<lbrakk>g m \<turnstile> nid (kind g nid) \<mapsto> v;
    g xs m \<longmapsto> vs\<rbrakk>
   \<Longrightarrow> g (nid # xs) m \<longmapsto> (v # vs)"

code_pred [show_modes] eval_all .


(* Test the eval predicates. *)
inductive eval_graph :: "IRGraph \<Rightarrow> ID \<Rightarrow> Value list \<Rightarrow> Value \<Rightarrow> bool"
  where
  "\<lbrakk>state = new_map ps;
    g state \<turnstile> nid (kind g nid) \<mapsto> val\<rbrakk>
    \<Longrightarrow> eval_graph g nid ps val"

code_pred [show_modes] "eval_graph" .

(* 5*5 \<Rightarrow> 25 *)
values "{v. eval_graph eg2_sq 4 [IntVal 5] v}"


fun is_misc_floating_node :: "IRNode \<Rightarrow> bool" where
  "is_misc_floating_node (ConstantNode c) = True" |
  "is_misc_floating_node (ParameterNode i) = True" |
  "is_misc_floating_node (ValueProxyNode loopExit c) = True" |
  "is_misc_floating_node (ConditionalNode c t f) = True" |
  "is_misc_floating_node (ShortCircuitOrNode x y) = True" |
  "is_misc_floating_node (LogicNegationNode x) = True" |
  "is_misc_floating_node (CallNode start args children) = True" |
  "is_misc_floating_node (RefNode x) = True" |
  "is_misc_floating_node _ = False"

(* All the kinds of nodes that eval can handle. *)
fun is_floating_node :: "IRNode \<Rightarrow> bool" where
  "is_floating_node n = (
    is_BinaryArithNode n \<or>
    is_UnaryArithNode n \<or>
    is_CompareNode n \<or>
    is_PhiNode n \<or>
    is_misc_floating_node n
  )"

inductive_cases ConstantNodeE[elim!]:
  "g m \<turnstile> nid (ConstantNode c) \<mapsto> val"
thm ConstantNodeE

inductive_cases ParameterNodeE[elim!]:
  "g m \<turnstile> nid (ParameterNode i) \<mapsto> val"
thm ParameterNodeE

inductive_cases PhiNodeE[elim!]:
  "g m \<turnstile> nid (PhiNode merge vals) \<mapsto> val"
thm PhiNodeE

inductive_cases ValuePhiNodeE[elim!]:
  "g m \<turnstile> nid (ValuePhiNode merge vals) \<mapsto> val"
thm ValuePhiNodeE

inductive_cases ValueProxyNodeE[elim!]:
  "g m \<turnstile> nid (ValueProxyNode loopExit c) \<mapsto> val"
thm ValueProxyNodeE

inductive_cases AbsNodeE[elim!]:
  "g m \<turnstile> nid (AbsNode x) \<mapsto> val"
thm AbsNodeE

inductive_cases NegateNodeE[elim!]:
  "g m \<turnstile> nid (NegateNode x) \<mapsto> val"
thm NegateNodeE

inductive_cases AddNodeE[elim!]:
  "g m \<turnstile> nid (AddNode x y) \<mapsto> val"
thm AddNodeE

inductive_cases SubNodeE[elim!]:
  "g m \<turnstile> nid (SubNode x y) \<mapsto> val"
thm SubNodeE

inductive_cases MulNodeE[elim!]:
  "g m \<turnstile> nid (MulNode x y) \<mapsto> val"
thm MulNodeE

inductive_cases AndNodeE[elim!]:
  "g m \<turnstile> nid (AndNode x y) \<mapsto> val"
thm AndNodeE

inductive_cases OrNodeE[elim!]:
  "g m \<turnstile> nid (OrNode x y) \<mapsto> val"
thm OrNodeE

inductive_cases XorNodeE[elim!]:
  "g m \<turnstile> nid (XorNode x y) \<mapsto> val"
thm XorNodeE

inductive_cases IntegerEqualsNodeE[elim!]:
  "g m \<turnstile> nid (IntegerEqualsNode x y) \<mapsto> val"
thm MulNodeE

inductive_cases IntegerLessThanNodeE[elim!]:
  "g m \<turnstile> nid (IntegerLessThanNode x y) \<mapsto> val"
thm IntegerLessThanNodeE

inductive_cases ConditionalNodeE[elim!]:
  "g m \<turnstile> nid (ConditionalNode condition trueExp falseExp) \<mapsto> val"
thm ConditionalNodeE

inductive_cases ShortCircuitOrNodeE[elim!]:
  "g m \<turnstile> nid (ShortCircuitOrNode x y) \<mapsto> val"
thm ShortCircuitOrNodeE

inductive_cases LogicNegationNodeE[elim!]:
  "g m \<turnstile> nid (LogicNegationNode x) \<mapsto> val"
thm LogicNegationNodeE

inductive_cases CallNodeE[elim!]:
  "g m \<turnstile> nid (CallNode start args children) \<mapsto> val"
thm CallNodeE

inductive_cases RefNodeE[elim!]:
  "g m \<turnstile> nid (RefNode x) \<mapsto> val"
thm RefNodeE

(* It is also useful to define these inverse rules for the
  *missing* eval cases, so that we can prove they are never true.
  E.g. see lemma notEvalIfNode.
*)
inductive_cases IfNodeE[elim!]:
  "g m \<turnstile> nid (IfNode c t f) \<mapsto> val"

lemma notEvalIfNode: "\<not>(g m \<turnstile> nid (IfNode c t f) \<mapsto> val)"
  by auto

inductive_cases SwitchNodeE[elim!]:
  "g m \<turnstile> nid (SwitchNode v sucs) \<mapsto> val"

inductive_cases KillingBeginNodeE[elim!]:
  "g m \<turnstile> nid (KillingBeginNode nxt) \<mapsto> val"

inductive_cases BeginNodeE[elim!]:
  "g m \<turnstile> nid (BeginNode nxt) \<mapsto> val"

inductive_cases StartNodeE[elim!]:
  "g m \<turnstile> nid (StartNode after nxt) \<mapsto> val"

inductive_cases EndNodeE[elim!]:
  "g m \<turnstile> nid (EndNode) \<mapsto> val"

inductive_cases LoopBeginNodeE[elim!]:
  "g m \<turnstile> nid (LoopBeginNode after ovr ends nxt) \<mapsto> val"

inductive_cases LoopEndNodeE[elim!]:
  "g m \<turnstile> nid (LoopEndNode begin) \<mapsto> val"

inductive_cases LoopExitNodeE[elim!]:
  "g m \<turnstile> nid (LoopExitNode begin after nxt) \<mapsto> val"

inductive_cases MergeNodeE[elim!]:
  "g m \<turnstile> nid (MergeNode after ends nxt) \<mapsto> val"

inductive_cases ReturnNodeE[elim!]:
  "g m \<turnstile> nid (ReturnNode result mem) \<mapsto> val"

inductive_cases NewInstanceNodeE[elim!]:
  "g m \<turnstile> nid (NewInstanceNode clazz before nxt) \<mapsto> val"

inductive_cases LoadFieldNodeE[elim!]:
  "g m \<turnstile> nid (LoadFieldNode field obj nxt) \<mapsto> val"

inductive_cases StoreFieldNodeE[elim!]:
  "g m \<turnstile> nid (StoreFieldNode field obj v after nxt) \<mapsto> val"

inductive_cases LoadStaticFieldNodeE[elim!]:
  "g m \<turnstile> nid (LoadStaticFieldNode field clazz nxt) \<mapsto> val"

inductive_cases StoreStaticFieldNodeE[elim!]:
  "g m \<turnstile> nid (StoreStaticFieldNode field clazz v nxt) \<mapsto> val"

inductive_cases FrameStateE[elim!]:
  "g m \<turnstile> nid (FrameState outer vals) \<mapsto> val"

inductive_cases NoNodeE[elim!]:
  "g m \<turnstile> nid (NoNode) \<mapsto> val"


(* Try proving 'inverted rules' for eval. *)
lemma "evalAddNode" : "g m \<turnstile> nid (AddNode x y) \<mapsto> val \<Longrightarrow>
  (\<exists> v1. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v1) \<and>
    (\<exists> v2. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v2) \<and>
       val = IntVal(v1 + v2)))"
  using AddNodeE by auto

(* Prove that eval only works on floating nodes. *)
lemma "evalFloating":
  assumes v:"g m \<turnstile> nid node \<mapsto> val"
  shows "is_floating_node node"
  using v apply (induct node)
                      apply auto
  done


(* eval never sees NoNode *)
lemma good_kind: "g m \<turnstile> x (kind g x) \<mapsto> val \<Longrightarrow> kind g x \<noteq> NoNode"
  using NoNodeE by auto
  
(* eval never sees NoNode?  Alternative form? *)
lemma good_kind2:
  "(g m \<turnstile> nid (case fmlookup g nid of
     None \<Rightarrow> NoNode |
     Some n \<Rightarrow> n)
   \<mapsto> val) \<Longrightarrow>
  kind g nid \<noteq> NoNode"
  using good_kind NoNodeE by simp 

(* We might like to prove the reverse too? But that
   would require lots of graph and MapState invariants.
lemma "floatingEval":
  assumes "is_floating_node node"
  assumes "very well formed graph:  g"
  assumes "mapstate m has all necessary params and values!"
  shows v:"g m \<turnstile> nid node \<mapsto> val"
*)



(* A top-level goal: eval is deterministic. *)
theorem "evalDet":
  shows "(g m \<turnstile> nid node \<mapsto> val1) \<Longrightarrow>
   (\<forall> val2. ((g m \<turnstile> nid node \<mapsto> val2) \<longrightarrow> val1 = val2))"
  apply (induction rule: "eval.induct")
                     apply (rule allI; rule impI; elim ConstantNodeE; auto)
                    apply (rule allI; rule impI; elim ParameterNodeE; auto)
                   apply (rule allI; rule impI; elim PhiNodeE; auto)
                  apply (rule allI; rule impI; elim ValuePhiNodeE; auto)
                 apply (rule allI; rule impI; elim ValueProxyNodeE; auto)
                apply (rule allI; rule impI; elim AbsNodeE; auto)
               apply (rule allI; rule impI; elim NegateNodeE; auto)
              apply (rule allI; rule impI; elim AddNodeE; auto)
             apply (rule allI; rule impI; elim SubNodeE; auto)
            apply (rule allI; rule impI; elim MulNodeE; auto)
           apply (rule allI; rule impI; elim AndNodeE; auto)
          apply (rule allI; rule impI; elim OrNodeE; auto)
         apply (rule allI; rule impI; elim XorNodeE; auto)
        apply (rule allI; rule impI; elim IntegerEqualsNodeE; auto)
       apply (rule allI; rule impI; elim IntegerLessThanNodeE; auto)
      apply (rule allI; rule impI; elim ConditionalNodeE; auto)
     apply (rule allI; rule impI; elim ShortCircuitOrNodeE; auto)
    apply (rule allI; rule impI; elim LogicNegationNodeE; auto)
   apply (rule allI; rule impI; elim CallNodeE; auto)
  apply (rule allI; rule impI; elim RefNodeE; auto)
  done

end

