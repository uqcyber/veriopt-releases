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


type_synonym Signature = "string"
type_synonym Program = "Signature \<Rightarrow> IRGraph"


fun p_method :: "Signature \<Rightarrow> Program \<Rightarrow> IRGraph" where
  "p_method m p = p m"


text_raw \<open>\Snip{StepSemantics}%\<close>
inductive step :: "(Program \<times> Signature) \<Rightarrow> (ID \<times> MapState \<times> Heap) \<Rightarrow> (ID \<times> MapState \<times> Heap) \<Rightarrow> bool"
  ("_\<turnstile>_\<rightarrow>_" 55)
  where

  SequentialNode:
  "\<lbrakk>g = p_method s p;
    node = kind g nid;
    is_sequential_node(node);
    next = (succ g nid)!0\<rbrakk> 
    \<Longrightarrow> (p, s) \<turnstile> (nid, m, h) \<rightarrow> (next, m, h)" |

  IfNode:
  "\<lbrakk>g = p_method s p;
    kind g nid = (IfNode cond true false);
    g m \<turnstile> cond (kind g cond) \<mapsto> (IntVal val);
    next = (if val_to_bool val then true else false)\<rbrakk>
    \<Longrightarrow> (p, s) \<turnstile> (nid, m, h) \<rightarrow> (next, m, h)" |  

  EndNodes:
  "\<lbrakk>g = p_method s p;
    is_end_node(kind g nid);
    merge_or_none = any_usage g nid;
    merge = the merge_or_none;
    is_merge_node(kind g merge);

    i = input_index g merge nid;
    phis = (phi_list g merge);
    inputs = (phi_inputs g i phis);
    g m inputs \<longmapsto> vs;

    m' = set_phis phis vs m\<rbrakk> 
    \<Longrightarrow> (p, s) \<turnstile> (nid, m, h) \<rightarrow> (merge, m', h)" |

  RefNode:
    "\<lbrakk>g = p_method s p;
      kind g nid = RefNode nid'\<rbrakk>
    \<Longrightarrow> (p, s) \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)" |

  LoadFieldNode:
    "\<lbrakk>g = p_method s p;
      kind g nid = (LoadFieldNode f obj nxt);
      h_load_field f obj h = v;
      m' = m_set nid v m\<rbrakk> 
    \<Longrightarrow> (p, s) \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h)" |

  StoreFieldNode:
    "\<lbrakk>g = p_method s p;
      kind g nid = (StoreFieldNode f rhs _ obj nxt);
      g m \<turnstile> rhs (kind g rhs) \<mapsto> val;
      h' = h_store_field f obj val h;
      m' = m_set nid val m\<rbrakk> 
    \<Longrightarrow> (p, s) \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h')"
text_raw \<open>\EndSnip\<close>

code_pred (modes: i * i \<Rightarrow> i * i * i \<Rightarrow> o * o * o \<Rightarrow> bool) step .


text_raw \<open>\Snip{TopStepSemantics}%\<close>
inductive step_top :: "Program \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> Heap \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> Heap \<Rightarrow> bool"
  ("_\<turnstile>_\<longrightarrow>_" 55) 
  for p where

  "\<lbrakk>(p, s) \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')\<rbrakk> 
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#xs, h) \<longrightarrow> ((s,nid',m')#xs, h')" |

  CallNodeStep:
  "\<lbrakk>g = p_method s p;
    kind g nid = (CallNode start args _);
    g m args \<longmapsto> vs;
    m' = set_params m vs\<rbrakk>
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#xs, h) \<longrightarrow> ((s,start,m')#(s,nid,m)#xs, h)" |

  InvokeNodeStep:
  "\<lbrakk>g = p_method s p;
    kind g nid = (InvokeNode callTarget classInit stateDuring stateAfter next);
    kind g callTarget = (MethodCallTargetNode targetMethod arguments);
    g m arguments \<longmapsto> vs;
    m' = set_params m vs\<rbrakk>
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#xs, h) \<longrightarrow> ((targetMethod,0,m')#(s,nid,m)#xs, h)" |

  InvokeWithExceptionNode:
  "\<lbrakk>g = p_method s p;
    kind g nid = (InvokeWithExceptionNode callTarget classInit stateDuring stateAfter next exceptionEdge);
    kind g callTarget = (SubstrateMethodCallTargetNode targetMethod arguments);
    g m arguments \<longmapsto> vs;
    m' = set_params m vs\<rbrakk>
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#xs, h) \<longrightarrow> ((targetMethod,0,m')#(s,nid,m)#xs, h)" |

  ReturnNode:
  "\<lbrakk>g = p_method s p;
    kind g nid = (ReturnNode (Some expr) _);
    g m \<turnstile> expr (kind g expr) \<mapsto> v;
    c_m' = m_set c_nid v c_m;
    c_nid' = (succ (p_method c_s p) c_nid)!0\<rbrakk> 
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#(c_s,c_nid,c_m)#xs, h) \<longrightarrow> ((c_s,c_nid',c_m')#xs, h)" |

  ReturnNodeVoid:
  "\<lbrakk>g = p_method s p;
    kind g nid = (ReturnNode None _);
    c_nid' = (succ g c_nid)!0\<rbrakk> 
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#(c_s,c_nid,c_m)#xs, h) \<longrightarrow> ((c_s,c_nid',c_m)#xs, h)"


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

fun has_return :: "MapState \<Rightarrow> bool" where
  "has_return m = ((m_val m 0) \<noteq> UndefVal)"

inductive exec :: "Program 
      \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> Heap
      \<Rightarrow> ExecLog 
      \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> Heap
      \<Rightarrow> ExecLog 
      \<Rightarrow> bool"
  ("_ \<turnstile> _ | _ \<longrightarrow>* _ | _")
  where
  "\<lbrakk>p \<turnstile> (((s,nid,m)#xs),h) \<longrightarrow> (((s',nid',m')#ys),h');
    \<not>(has_return m');

    g = p_method s p;    
    l' = (l @ [(nid, (kind g nid))]);

    exec p (((s',nid',m')#ys),h') l' next_state l''\<rbrakk> 
    \<Longrightarrow> exec p (((s,nid,m)#xs),h) l next_state l''" 
(* TODO: refactor this stopping condition to be more abstract *)
  |
  "\<lbrakk>p \<turnstile> (((s,nid,m)#xs),h) \<longrightarrow> (((s',nid',m')#ys),h');
    has_return m';

    g = p_method s p;
    l' = (l @ [(nid, (kind g nid))])\<rbrakk>
    \<Longrightarrow> exec p (((s,nid,m)#xs),h) l (((s',nid',m')#ys),h') l'"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool as Exec) "exec" .


inductive exec_debug :: "Program
     \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> Heap
     \<Rightarrow> nat
     \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> Heap
     \<Rightarrow> bool"
  ("_\<turnstile>_\<rightarrow>*_* _")
  where
  "\<lbrakk>n > 0;
    p \<turnstile> s \<longrightarrow> s';
    exec_debug p s' (n - 1) s''\<rbrakk> 
    \<Longrightarrow> exec_debug p s n s''" |

  "\<lbrakk>n = 0\<rbrakk>
    \<Longrightarrow> exec_debug p s n s"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) "exec_debug" .


definition p3:: MapState where
  "p3 = set_params new_map_state [IntVal 3] "

(* Eg. call eg2_sq with [3] \<longrightarrow> 9 *)
values "{m_val (prod.snd (prod.snd (hd (prod.fst res)))) 0 
        | res. (\<lambda>x . eg2_sq) \<turnstile> ([('''',0, p3), ('''',0, p3)], new_heap) \<rightarrow>*2* res}"

definition field_sq :: FieldName where
  "field_sq = ''sq''"

definition eg3_store_sq :: RealGraph where
  "eg3_store_sq = irgraph [
    (0, StartNode None 4),
    (1, ParameterNode 0),
    (3, MulNode 1 1),
    (4, StoreFieldNode field_sq 3 None None 5),
    (5, ReturnNode (Some 3) None)
   ]"

definition eg3_sq :: IRGraph where
  "eg3_sq = Abs_IRGraph eg3_store_sq"

(* Eg. call eg2_sq with [3] \<longrightarrow> heap with object None={sq: 9} *)
values "{(prod.snd res) field_sq None
        | res. (\<lambda>x. eg3_sq) \<turnstile> ([('''', 0, p3), ('''', 0, p3)], new_heap) \<rightarrow>*3* res}"

definition eg4_store_sq :: RealGraph where
  "eg4_store_sq = irgraph [
    (0, StartNode None 4),
    (1, ParameterNode 0),
    (3, MulNode 1 1),
    (4, StoreFieldNode field_sq 3 None (Some 24) 5),
    (5, ReturnNode (Some 3) None)
   ]"

definition eg4_sq :: IRGraph where
  "eg4_sq = Abs_IRGraph eg4_store_sq"

(* Eg. call eg2_sq with [3] \<longrightarrow> heap with object 24={sq: 9} *)
values "{(prod.snd res) field_sq (Some 24)
        | res. (\<lambda>x. eg4_sq) \<turnstile> ([('''', 0, p3), ('''', 0, p3)], new_heap) \<rightarrow>*3* res}"
end

