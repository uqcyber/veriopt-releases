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

type_synonym MapState = "ID \<Rightarrow> Value"


fun val_to_bool :: "int32 \<Rightarrow> bool" where
  "val_to_bool x = (if x = 0 then False else True)" 

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal 1)" |
  "bool_to_val False = (IntVal 0)"

fun unary_expr :: "IRNode \<Rightarrow> Value \<Rightarrow> Value" where
  "unary_expr AbsNode (IntVal x) = (IntVal (if (x < 0) then -x else x))" |
  "unary_expr NegateNode (IntVal x) = (IntVal (uminus x))" |
  "unary_expr LogicNegationNode (IntVal x) = (bool_to_val (\<not>(val_to_bool x)))" |
  "unary_expr _ _ = UndefVal"

fun binary_expr :: "IRNode \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "binary_expr AddNode (IntVal x) (IntVal y) = (IntVal (x + y))" |
  "binary_expr SubNode (IntVal x) (IntVal y) = (IntVal (x - y))" |
  "binary_expr MulNode (IntVal x) (IntVal y) = (IntVal (x * y))" |
  "binary_expr AndNode (IntVal x) (IntVal y) = (IntVal (x AND y))" |
  "binary_expr OrNode (IntVal x) (IntVal y) = (IntVal (x OR y))" |
  "binary_expr XorNode (IntVal x) (IntVal y) = (IntVal (x XOR y))" |
  "binary_expr IntegerLessThanNode (IntVal x) (IntVal y) = (bool_to_val (x < y))" |
  "binary_expr IntegerEqualsNode (IntVal x) (IntVal y) = (bool_to_val (x = y))" |
  "binary_expr _ _ _ = UndefVal"

definition unary_nodes :: "IRNode set" where
  "unary_nodes = {AbsNode, NegateNode}"

definition binary_nodes :: "IRNode set" where
  "binary_nodes = {AddNode, SubNode, MulNode, AndNode, 
                   OrNode, XorNode, IntegerLessThanNode,
                   IntegerEqualsNode}"

definition merge_nodes :: "IRNode set" where
  "merge_nodes = {MergeNode, LoopBeginNode}"

definition end_nodes :: "IRNode set" where
  "end_nodes = {EndNode, LoopEndNode}"

(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index val (x # xs) = (if (x=val) then 0 else find_index val xs + 1)"

fun phi_list :: "Graph \<Rightarrow> ID \<Rightarrow> ID list" where
  "phi_list g nid = 
    (filter (\<lambda>x.((kind g x)=PhiNode))
      (sorted_list_of_set (usages g nid)))"

fun input_index :: "Graph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index g n n' = find_index n' (inp g n)"

fun phi_inputs :: "Graph \<Rightarrow> nat \<Rightarrow> ID list \<Rightarrow> ID list" where
  "phi_inputs g i nodes = (map (\<lambda>n. (inp g n)!(i + 1)) nodes)"

fun set_phis :: "ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_phis [] [] m = m" |
  "set_phis (nid # xs) (v # vs) m = (set_phis xs vs (m(nid := v)))" |
  "set_phis [] (v # vs) m = m" |
  "set_phis (x # xs) [] m = m"

fun set_params :: "Graph \<Rightarrow> ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_params g [] vs m = m" |
  "set_params g (nid # xs) vs m = (let m' = (set_params g xs vs m) in 
   (case (kind g nid) of 
    (ParameterNode i) \<Rightarrow> m'(nid := (vs!i)) |
    _ \<Rightarrow> m'))"


fun any_usage :: "Graph \<Rightarrow> ID \<Rightarrow> ID" where
  "any_usage g nid = (sorted_list_of_set (usages g nid))!0"


inductive
  eval :: "Graph \<Rightarrow> (ID \<times> MapState) \<Rightarrow> Value \<Rightarrow> bool" (" _ _\<mapsto>_" 55) and
  eval_all :: "Graph \<Rightarrow> ID list \<Rightarrow> MapState \<Rightarrow> Value list \<Rightarrow> bool" ("_ _ _\<longmapsto>_" 55)
  for g
  where

  CallNodeEval:
  "\<lbrakk>kind g nid = CallNode start\<rbrakk>
    \<Longrightarrow> g (nid, m) \<mapsto> m nid" |

  ParameterNode:
  "\<lbrakk>kind g nid = ParameterNode i\<rbrakk>
    \<Longrightarrow> g (nid, m) \<mapsto> m nid" |

  PhiNode:
  "\<lbrakk>kind g nid = PhiNode\<rbrakk>
    \<Longrightarrow>  g (nid, m) \<mapsto> m nid" |

  ConstantNode:
  "\<lbrakk>kind g nid = ConstantNode c\<rbrakk>
    \<Longrightarrow> g (nid, m) \<mapsto> (IntVal (word_of_int c))" |

  UnaryNode:
  "\<lbrakk>kind g nid \<in> unary_nodes;
    g ((inp g nid)!0, m) \<mapsto> v\<rbrakk> 
    \<Longrightarrow> g (nid, m) \<mapsto> (unary_expr (kind g nid) v)" |

  BinaryNode:
  "\<lbrakk>kind g nid \<in> binary_nodes;
    g ((inp g nid)!0, m) \<mapsto> v1;
    g ((inp g nid)!1, m) \<mapsto> v2\<rbrakk> 
    \<Longrightarrow> g (nid, m) \<mapsto> (binary_expr (kind g nid) v1 v2)" |

  "g [] m \<longmapsto> []" |
  "\<lbrakk>g (nid, m) \<mapsto> v; g xs m \<longmapsto> vs\<rbrakk> \<Longrightarrow> g (nid # xs) m \<longmapsto> (v # vs)"

code_pred eval .
code_pred eval_all .
  

inductive
  step :: "Graph \<Rightarrow> (ID \<times> MapState) \<Rightarrow> (ID \<times> MapState) \<Rightarrow> bool" ("_ \<turnstile> _\<rightarrow>_" 55) and
  step_top :: "Graph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool" ("_\<turnstile>_\<longrightarrow>_" 55) 
  for g
  where

  "\<lbrakk>g \<turnstile> (nid, m) \<rightarrow> (nid', m')\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) # xs \<longrightarrow> (nid', m') # xs" |

  CallNodeStep:
  "\<lbrakk>kind g nid = CallNode start;
    g (inp g nid) m \<longmapsto> vs;
    m' = (set_params g (sorted_list_of_set (graph_nodes g)) vs m)\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m)#xs \<longrightarrow> (start, m')#(nid,m)#xs" |

  ReturnNode:
  "\<lbrakk>kind g nid = ReturnNode;
    g ((inp g nid)!0, m) \<mapsto> v;
    m' = call_m(call_nid := v)\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m)#(call_nid,call_m)#xs \<longrightarrow> ((succ g call_nid)!0,m')#xs" |

  ExitReturnNode:
  "\<lbrakk>kind g nid = ReturnNode;
    g ((inp g nid)!0, m) \<mapsto> v;
    m' = m(nid := v)\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m)#[] \<longrightarrow> []" |

  SequentialNode:
  "\<lbrakk>node = kind g nid;
    node \<in> {StartNode, BeginNode} \<union> merge_nodes\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) \<rightarrow> ((succ g nid)!0, m)" |

  IfNode:
  "\<lbrakk>kind g nid = IfNode;
    g ((inp g nid)!0, m) \<mapsto> (IntVal cond)\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m) \<rightarrow> ((succ g nid)!(if val_to_bool cond then 0 else 1), m)" |  

  (* Solution to the eval_all but the evalution gives up :(
   * \<forall> i. i < length inputs \<longrightarrow> (\<exists> s' . (inputs!i \<mapsto> (s',vs!i))); *)

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


code_pred step .
code_pred step_top .

fun new_map :: "Graph \<Rightarrow> Value list \<Rightarrow> MapState" where
  "new_map g params = set_params g (sorted_list_of_set (graph_nodes g))
      params (\<lambda> x . UndefVal)"

inductive exec :: "Graph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool" ("_ \<turnstile> _ \<longrightarrow>* _")
  where
  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    length s' \<noteq> 0;
    exec g s' s''\<rbrakk> 
    \<Longrightarrow> exec g s s''" |

  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    length s' = 0\<rbrakk>
    \<Longrightarrow> exec g s s"
code_pred "exec" .

inductive exec_debug :: "Graph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> nat \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow>*_* _")
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