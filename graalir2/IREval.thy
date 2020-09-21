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
    val = bool_to_m_val(v1 \<le> v2)\<rbrakk> 
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
    \<Longrightarrow> g m \<turnstile> nid (LogicNegationNode x ) \<mapsto> val" |

(* Access the value returned by the most recent call *)
  CallNodeEval:
  "\<lbrakk>val = m_val m nid\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (CallNode start children) \<mapsto> val" |

  RefNode:
  "\<lbrakk>g m \<turnstile> x (kind g x) \<mapsto> val\<rbrakk>
    \<Longrightarrow> g m \<turnstile> nid (RefNode x) \<mapsto> val" 

code_pred [show_modes] eval .


inductive
  eval_all :: "IRGraph \<Rightarrow> ID list \<Rightarrow> MapState \<Rightarrow> Value list \<Rightarrow> bool"
  ("_ _ _\<longmapsto>_" 55)
  for g where
  "g [] m \<longmapsto> []" |
  "\<lbrakk>g m \<turnstile> nid (kind g nid) \<mapsto> v; g xs m \<longmapsto> vs\<rbrakk> \<Longrightarrow> g (nid # xs) m \<longmapsto> (v # vs)"

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


(* Try proving 'inverted rules' for eval.
lemma "evalAddNode" : "g m \<turnstile> nid (AddNode x y) \<mapsto> val \<Longrightarrow>
  (\<exists> v1. (g m \<turnstile> x (kind g x) \<mapsto> IntVal v1) \<and>
    (\<exists> v2. (g m \<turnstile> y (kind g y) \<mapsto> IntVal v2) \<and>
       val = IntVal(v1 + v2)))"
*)

end

