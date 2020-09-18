section \<open>Inductive semantics of nodes\<close>

theory InductiveSemantics
  imports
    "AbsGraph"
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

fun m_param :: "Graph \<Rightarrow> MapState \<Rightarrow> ID \<Rightarrow> Value" where
  "m_param g m nid = (case (kind g nid) of
    (ParameterNode i) \<Rightarrow> (m_params m)!i |
    _ \<Rightarrow> UndefVal)"

fun set_params :: "MapState \<Rightarrow> Value list \<Rightarrow> MapState" where
  "set_params (MapState m p) vs = MapState m vs"


fun val_to_bool :: "int32 \<Rightarrow> bool" where
  "val_to_bool x = (if x = 0 then False else True)" 

fun bool_to_m_val :: "bool \<Rightarrow> Value" where
  "bool_to_m_val True = (IntVal 1)" |
  "bool_to_m_val False = (IntVal 0)"

fun unary_expr :: "IRNode \<Rightarrow> Value \<Rightarrow> Value" where
  "unary_expr AbsNode (IntVal x) = (IntVal (if (x < 0) then -x else x))" |
  "unary_expr NegateNode (IntVal x) = (IntVal (uminus x))" |
  "unary_expr LogicNegationNode (IntVal x) = (bool_to_m_val (\<not>(val_to_bool x)))" |
  "unary_expr _ _ = UndefVal"

fun binary_expr :: "IRNode \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "binary_expr AddNode (IntVal x) (IntVal y) = (IntVal (x + y))" |
  "binary_expr SubNode (IntVal x) (IntVal y) = (IntVal (x - y))" |
  "binary_expr MulNode (IntVal x) (IntVal y) = (IntVal (x * y))" |
  "binary_expr AndNode (IntVal x) (IntVal y) = (IntVal (x AND y))" |
  "binary_expr OrNode (IntVal x) (IntVal y) = (IntVal (x OR y))" |
  "binary_expr XorNode (IntVal x) (IntVal y) = (IntVal (x XOR y))" |
  "binary_expr IntegerLessThanNode (IntVal x) (IntVal y) = (bool_to_m_val (x < y))" |
  "binary_expr IntegerEqualsNode (IntVal x) (IntVal y) = (bool_to_m_val (x = y))" |
  "binary_expr _ _ _ = UndefVal"

definition unary_nodes :: "IRNode set" where
  "unary_nodes = {AbsNode, NegateNode}"

definition binary_nodes :: "IRNode set" where
  "binary_nodes = {AddNode, SubNode, MulNode, AndNode, 
                   OrNode, XorNode, IntegerLessThanNode,
                   IntegerEqualsNode}"

definition phi_nodes :: "IRNode set" where
  "phi_nodes = {PhiNode, ValuePhiNode}"

definition merge_nodes :: "IRNode set" where
  "merge_nodes = {MergeNode, LoopBeginNode}"

definition end_nodes :: "IRNode set" where
  "end_nodes = {EndNode, LoopEndNode}"

definition sequential_nodes :: "IRNode set" where
  "sequential_nodes = {StartNode, BeginNode, 
                       LoopBeginNode, LoopExitNode}
                      \<union> merge_nodes"

lemma "AddNode \<in> binary_nodes"
  unfolding binary_nodes_def by simp

(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index v (x # xs) = (if (x=v) then 0 else find_index v xs + 1)"

fun phi_list :: "Graph \<Rightarrow> ID \<Rightarrow> ID list" where
  "phi_list g nid = 
    (filter (\<lambda>x.((kind g x)\<in>phi_nodes))
      (sorted_list_of_set (usages g nid)))"

fun input_index :: "Graph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index g n n' = find_index n' (inp g n)"

fun phi_inputs :: "Graph \<Rightarrow> nat \<Rightarrow> ID list \<Rightarrow> ID list" where
  "phi_inputs g i nodes = (map (\<lambda>n. (inp g n)!(i + 1)) nodes)"

fun set_phis :: "ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_phis [] [] m = m" |
  "set_phis (nid # xs) (v # vs) m = (set_phis xs vs (m_set nid v m))" |
  "set_phis [] (v # vs) m = m" |
  "set_phis (x # xs) [] m = m"


fun any_usage :: "Graph \<Rightarrow> ID \<Rightarrow> ID" where
  "any_usage g nid = (sorted_list_of_set (usages g nid))!0"


text_raw \<open>\snip{expression_semantics}{\<close>
inductive
  eval :: "Graph \<Rightarrow> (ID \<times> MapState) \<Rightarrow> Value \<Rightarrow> bool"
  (" _ _\<mapsto>_" 55)
  for g where

  CallNodeEval:
  "\<lbrakk>kind g nid = CallNode start;
    val = m_val m nid\<rbrakk>
    \<Longrightarrow> g (nid, m) \<mapsto> val" |

  ParameterNode:
  "\<lbrakk>kind g nid = ParameterNode i;
    val = m_param g m nid\<rbrakk>
    \<Longrightarrow> g (nid, m) \<mapsto> val" |

  PhiNode:
  "\<lbrakk>kind g nid \<in> phi_nodes;
    val = m_val m nid\<rbrakk>
    \<Longrightarrow>  g (nid, m) \<mapsto> val" |

  ConstantNode:
  "\<lbrakk>kind g nid = ConstantNode c;
    val = (IntVal (word_of_int c))\<rbrakk>
    \<Longrightarrow> g (nid, m) \<mapsto> val" |

  ValueProxyNode:
  "\<lbrakk>kind g nid = ValueProxyNode;
    g ((inp g nid)!1, m) \<mapsto> v\<rbrakk>
    \<Longrightarrow> g (nid, m) \<mapsto> v" |

  UnaryNode:
  "\<lbrakk>kind g nid \<in> unary_nodes;
    g ((inp g nid)!0, m) \<mapsto> v;
    val = (unary_expr (kind g nid) v)\<rbrakk>
    \<Longrightarrow> g (nid, m) \<mapsto> val" |

  BinaryNode:
  "\<lbrakk>kind g nid \<in> binary_nodes;
    g ((inp g nid)!0, m) \<mapsto> v1;
    g ((inp g nid)!1, m) \<mapsto> v2;
    val = binary_expr (kind g nid) v1 v2\<rbrakk> 
    \<Longrightarrow> g (nid, m) \<mapsto> val"
text_raw \<open>}%endsnip\<close>

code_pred eval .

inductive
  eval_all :: "Graph \<Rightarrow> ID list \<Rightarrow> MapState \<Rightarrow> Value list \<Rightarrow> bool"
  ("_ _ _\<longmapsto>_" 55)
  for g where
  "g [] m \<longmapsto> []" |
  "\<lbrakk>g (nid, m) \<mapsto> v; g xs m \<longmapsto> vs\<rbrakk> \<Longrightarrow> g (nid # xs) m \<longmapsto> (v # vs)"

code_pred eval_all .


text_raw \<open>\snip{step_semantics}{\<close>
inductive
  step :: "Graph \<Rightarrow> (ID \<times> MapState) \<Rightarrow> (ID \<times> MapState) \<Rightarrow> bool"
  ("_ \<turnstile> _\<rightarrow>_" 55)
  for g where

  SequentialNode:
  "\<lbrakk>node = kind g nid;
    node \<in> sequential_nodes;
    next = (succ g nid)!0\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) \<rightarrow> (next, m)" |

  IfNode:
  "\<lbrakk>kind g nid = IfNode;
    g ((inp g nid)!0, m) \<mapsto> (IntVal cond);
    succ_edge = (if val_to_bool cond then 0 else 1);
    next = (succ g nid)!succ_edge\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m) \<rightarrow> (next, m)" |  

  EndNodes:
  "\<lbrakk>kind g nid \<in> end_nodes;

    merge = any_usage g nid;
    kind g merge \<in> merge_nodes;

    i = input_index g merge nid;

    phis = (phi_list g merge);
    inputs = (phi_inputs g i phis);
    g inputs m \<longmapsto> vs;

    m' = (set_phis phis vs m)\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) \<rightarrow> (merge, m')"
text_raw \<open>}%endsnip\<close>

code_pred step .

text_raw \<open>\snip{top_step_semantics}{\<close>
inductive
  step_top :: "Graph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool"
  ("_\<turnstile>_\<longrightarrow>_" 55) 
  for g where

  "\<lbrakk>g \<turnstile> (nid, m) \<rightarrow> (nid', m')\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) # xs \<longrightarrow> (nid', m') # xs" |

  CallNodeStep:
  "\<lbrakk>kind g nid = CallNode start;
    g (inp g nid) m \<longmapsto> vs;
    m' = MapState (\<lambda>x. UndefVal) vs\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m)#xs \<longrightarrow> (start, m')#(nid,m)#xs" |

  ReturnNode:
  "\<lbrakk>kind g nid = ReturnNode;
    g ((inp g nid)!0, m) \<mapsto> v;
    m' = m_set call_nid v call_m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m)#(call_nid,call_m)#xs \<longrightarrow> ((succ g call_nid)!0,m')#xs"

(* |
  ExitReturnNode:
  "\<lbrakk>kind g nid = ReturnNode;
    g ((inp g nid)!0, m) \<mapsto> v;
    m' = m_set nid v m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m)#[] \<longrightarrow> []"
*)
text_raw \<open>}%endsnip\<close>

code_pred step_top .


fun new_map :: "Value list \<Rightarrow> MapState" where
  "new_map ps = set_params new_map_state ps"

inductive exec :: "Graph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool"
  ("_ \<turnstile> _ \<longrightarrow>* _")
  where
  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    exec g s' s''\<rbrakk> 
    \<Longrightarrow> exec g s s''" 
(* TODO: this seems to be unnecessary? *)
  |
  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    length s' = 0\<rbrakk>
    \<Longrightarrow> exec g s s"
code_pred "exec" .


inductive exec_debug :: "Graph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> nat \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool"
  ("_ \<turnstile> _ \<rightarrow>*_* _")
  where
  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    n > 0;
    exec_debug g s' (n - 1) s''\<rbrakk> 
    \<Longrightarrow> exec_debug g s n s''" |

  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    n = 0\<rbrakk>
    \<Longrightarrow> exec_debug g s n s"
code_pred "exec_debug" .

end