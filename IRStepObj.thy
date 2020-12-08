section \<open>Inductive small-step semantics of IR graphs\<close>

theory IRStepObj
  imports
    IREval
begin

type_synonym FieldName = "string"

(* We use the H[f][p] heap representation.  See \cite{heap-reps-2011}. *)
(* TODO: Record volatile fields?  Include class name of field? *)
type_synonym Heap = "FieldName \<Rightarrow> objref \<Rightarrow> Value"

definition new_heap :: "Heap" where
  "new_heap =  (\<lambda>f. \<lambda>p. UndefVal)"

fun h_load_field :: "FieldName \<Rightarrow> objref \<Rightarrow> Heap \<Rightarrow> Value" where
  "h_load_field f obj h = h f obj"

fun h_store_field :: "FieldName \<Rightarrow> objref \<Rightarrow> Value \<Rightarrow> Heap \<Rightarrow> Heap" where
  "h_store_field f obj v h = h(f := ((h f)(obj := v)))"


text_raw \<open>\Snip{StepSemantics}%\<close>
inductive step :: "IRGraph \<Rightarrow> (ID \<times> MapState \<times> Heap) \<Rightarrow> (ID \<times> MapState \<times> Heap) \<Rightarrow> bool"
  ("_ \<turnstile> _\<rightarrow>_" 55)
  for g where

  SequentialNode:
  "\<lbrakk>node = kind g nid;
    is_sequential_node(node);
    next = (succ g nid)!0\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (next, m, h)" |

  IfNode:
  "\<lbrakk>kind g nid = (IfNode cond true false);
    g m \<turnstile> cond (kind g cond) \<mapsto> (IntVal val);
    next = (if val_to_bool val then true else false)\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (next, m, h)" |  

  EndNodes:
  "\<lbrakk>is_end_node(kind g nid);
    merge = any_usage g nid;
    is_merge_node(kind g merge);

    i = input_index g merge nid;
    phis = (phi_list g merge);
    inputs = (phi_inputs g i phis);
    g m inputs \<longmapsto> vs;

    m' = set_phis phis vs m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (merge, m', h)" |

  RefNode:
    "kind g nid = RefNode nid'
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)" |

  LoadFieldNode:
    "\<lbrakk>kind g nid = (LoadFieldNode f nxt);
     obj = 0;
     h_load_field f obj h = v;
     m' = m_set nid v m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h)" |

  StoreFieldNode:
    "\<lbrakk>kind g nid = (StoreFieldNode f rhs _ nxt);
     obj = 0;
     g m \<turnstile> rhs (kind g rhs) \<mapsto> val;
     h' = h_store_field f obj val h;
     m' = m_set nid val m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h')"
text_raw \<open>\EndSnip\<close>

code_pred (modes: i \<Rightarrow> i * i \<Rightarrow> o * o \<Rightarrow> bool) step .


text_raw \<open>\Snip{TopStepSemantics}%\<close>
inductive step_top :: "IRGraph \<Rightarrow> (ID \<times> MapState) list \<times> Heap \<Rightarrow> (ID \<times> MapState) list \<times> Heap \<Rightarrow> bool"
  ("_\<turnstile>_\<longrightarrow>_" 55) 
  for g where

  "\<lbrakk>g \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')\<rbrakk> 
    \<Longrightarrow> g \<turnstile> ((nid,m)#xs, h) \<longrightarrow> ((nid',m')#xs, h')" |

  CallNodeStep:
  "\<lbrakk>kind g nid = (CallNode start args _);
    g m args \<longmapsto> vs;
    m' = set_params m vs\<rbrakk>
    \<Longrightarrow> g \<turnstile> ((nid,m)#xs, h) \<longrightarrow> ((start,m')#(nid,m)#xs, h)" |

  ReturnNode:
  "\<lbrakk>kind g nid = (ReturnNode (Some expr) _);
    g m \<turnstile> expr (kind g expr) \<mapsto> v;
    c_m' = m_set c_nid v c_m;
    c_nid' = (succ g c_nid)!0\<rbrakk> 
    \<Longrightarrow> g \<turnstile> ((nid,m)#(c_nid,c_m)#xs, h) \<longrightarrow> ((c_nid',c_m')#xs, h)" |

  ReturnNodeVoid:
  "\<lbrakk>kind g nid = (ReturnNode None _);
    c_nid' = (succ g c_nid)!0\<rbrakk> 
    \<Longrightarrow> g \<turnstile> ((nid,m)#(c_nid,c_m)#xs, h) \<longrightarrow> ((c_nid',c_m)#xs, h)"


text_raw \<open>\EndSnip\<close>

(*

  ExitReturnNode:
  "\<lbrakk>kind g nid = (ReturnNode (Some expr) _);
    g m \<turnstile> expr (kind g expr) \<mapsto> v;
    m' = hs_setval nid v m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m)#[] \<longrightarrow> []"
*)

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) step_top .

type_synonym ExecLog = "(ID \<times> IRNode) list"


inductive exec :: "IRGraph 
      \<Rightarrow> (ID \<times> MapState) list \<times> Heap
      \<Rightarrow> ExecLog 
      \<Rightarrow> (ID \<times> MapState) list \<times> Heap
      \<Rightarrow> ExecLog 
      \<Rightarrow> bool"
  ("_ \<turnstile> _ | _ \<longrightarrow>* _ | _")
  where
  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    m_val (prod.snd ((prod.fst s')!0)) 0 = UndefVal;
    nid = prod.fst ((prod.fst s)!0);
    l' = (l @ [(nid, (kind g nid))]);
    exec g s' l' s'' l''\<rbrakk> 
    \<Longrightarrow> exec g s l s'' l''" 
(* TODO: refactor this stopping condition to be more abstract *)
  |
  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    m_val (prod.snd ((prod.fst s')!0)) 0 \<noteq> UndefVal;
    nid = prod.fst ((prod.fst s)!0);
    l' = (l @ [(nid, (kind g nid))])\<rbrakk>
    \<Longrightarrow> exec g s l s' l'"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) "exec" .


inductive exec_debug :: "IRGraph
     \<Rightarrow> (ID \<times> MapState) list \<times> Heap
     \<Rightarrow> nat
     \<Rightarrow> (ID \<times> MapState) list \<times> Heap
     \<Rightarrow> bool"
  ("_ \<turnstile> _ \<rightarrow>*_* _")
  where
  "\<lbrakk>n > 0;
    g \<turnstile> s \<longrightarrow> s';
    exec_debug g s' (n - 1) s''\<rbrakk> 
    \<Longrightarrow> exec_debug g s n s''" |

  "\<lbrakk>n = 0\<rbrakk>
    \<Longrightarrow> exec_debug g s n s"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) "exec_debug" .


definition p3:: MapState where
  "p3 = set_params new_map_state [IntVal 3] "

(* Eg. call eg2_sq with [3] \<longrightarrow> 9 *)
values "{m_val (prod.snd (hd (prod.fst res))) 0 
        | res. eg2_sq \<turnstile> ([(0, p3), (0, p3)], new_heap) \<rightarrow>*2* res}"

definition field_sq :: FieldName where
  "field_sq = ''sq''"

definition eg3_store_sq :: RealGraph where
  "eg3_store_sq = irgraph [
    (0, StartNode None 4),
    (1, ParameterNode 0),
    (3, MulNode 1 1),
    (4, StoreFieldNode field_sq 3 None 5),
    (5, ReturnNode (Some 3) None)
   ]"

definition eg3_sq :: IRGraph where
  "eg3_sq = Abs_IRGraph eg3_store_sq"

(* Eg. call eg2_sq with [3] \<longrightarrow> heap with object 0={sq: 9} *)
values "{prod.snd res field_sq 0
        | res. eg3_sq \<turnstile> ([(0, p3), (0, p3)], new_heap) \<rightarrow>*3* res}"
end

