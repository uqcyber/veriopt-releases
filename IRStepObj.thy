section \<open>Inductive small-step semantics of IR graphs\<close>

theory IRStepObj
  imports
    IREval
begin

(* We use the H[f][p] heap representation.  See \cite{heap-reps-2011}. *)
(* TODO: Record volatile fields?  Include class name of field? *)
text_raw \<open>\Snip{heapdef}%\<close>
type_synonym FieldName = "string"
type_synonym Heap = "FieldName \<Rightarrow> objref \<Rightarrow> Value"
type_synonym Free = "nat"
type_synonym DynamicHeap = "Heap \<times> Free"

fun h_load_field :: "FieldName \<Rightarrow> objref \<Rightarrow> DynamicHeap \<Rightarrow> Value" where
  "h_load_field f obj (h, n) = h f obj"

fun h_store_field :: "FieldName \<Rightarrow> objref \<Rightarrow> Value \<Rightarrow> DynamicHeap \<Rightarrow> DynamicHeap" where
  "h_store_field f obj v (h, n) = (h(f := ((h f)(obj := v))), n)"

fun h_new_inst :: "DynamicHeap \<Rightarrow> DynamicHeap \<times> Value" where
  "h_new_inst (h, n) = ((h,n+1), (ObjRef (Some (n+1))))"
text_raw \<open>\EndSnip\<close>

definition new_heap :: "DynamicHeap" where
  "new_heap =  ((\<lambda>f. \<lambda>p. UndefVal), 0)"

text_raw \<open>\Snip{programdef}%\<close>
type_synonym Signature = "string"
type_synonym Program = "Signature \<Rightarrow> IRGraph"
text_raw \<open>\EndSnip\<close>

fun p_method :: "Signature \<Rightarrow> Program \<Rightarrow> IRGraph" where
  "p_method m p = p m"

inductive step :: "IRGraph \<Rightarrow> (ID \<times> MapState \<times> DynamicHeap) \<Rightarrow> (ID \<times> MapState \<times> DynamicHeap) \<Rightarrow> bool"
  ("_\<turnstile>_\<rightarrow>_" 55)
  where

  SequentialNode:
  "\<lbrakk>is_sequential_node (kind g nid);
    next = (succ g nid)!0\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (next, m, h)" |

  IfNode:
  "\<lbrakk>kind g nid = (IfNode cond true false);
    g m \<turnstile> cond (kind g cond) \<mapsto> val;
    next = (if val_to_bool val then true else false)\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (next, m, h)" |  

  EndNodes:
  "\<lbrakk>isAbstractEndNodeType (kind g nid);
    merge = the (any_usage g nid);
    isAbstractMergeNodeType (kind g merge);

    i = input_index g merge nid;
    phis = (phi_list g merge);
    inputs = (phi_inputs g i phis);
    g m inputs \<longmapsto> vs;

    m' = set_phis phis vs m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (merge, m', h)" |

  RefNode:
    "\<lbrakk>kind g nid = (RefNode nid')\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)" |

  NewInstanceNode:
    "\<lbrakk>kind g nid = (NewInstanceNode nid f obj nxt);
      (h', ref) = h_new_inst h;
      m' = m_set nid ref m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h')" |

  LoadFieldNode:
    "\<lbrakk>kind g nid = (LoadFieldNode nid f (Some obj) nxt);
      g m \<turnstile> obj (kind g obj) \<mapsto> ObjRef ref;
      h_load_field f ref h = v;
      m' = m_set nid v m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h)" |

  StaticLoadFieldNode:
    "\<lbrakk>kind g nid = (LoadFieldNode nid f None nxt);
      h_load_field f None h = v;
      m' = m_set nid v m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h)" |

  StoreFieldNode:
    "\<lbrakk>kind g nid = (StoreFieldNode nid f rhs _ (Some obj) nxt);
      g m \<turnstile> rhs (kind g rhs) \<mapsto> val;
      g m \<turnstile> obj (kind g obj) \<mapsto> ObjRef ref;
      h' = h_store_field f ref val h;
      m' = m_set nid val m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h')" |

  StaticStoreFieldNode:
    "\<lbrakk>kind g nid = (StoreFieldNode nid f rhs _ None nxt);
      g m \<turnstile> rhs (kind g rhs) \<mapsto> val;
      h' = h_store_field f None val h;
      m' = m_set nid val m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h')"

text_raw \<open>\Snip{StepSemantics}%\<close>
text \<open>
\begin{center}
@{thm[mode=Rule] step.SequentialNode [no_vars]}\induct{step:seq}\\[8px]
@{thm[mode=Rule] step.IfNode [no_vars]}\induct{step:if}\\[8px]
@{thm[mode=Rule] step.EndNodes [no_vars]}\induct{step:end}\\[8px]
@{thm[mode=Rule] step.RefNode [no_vars]}\induct{step:ref}\\[8px]
@{thm[mode=Rule] step.NewInstanceNode [no_vars]}\induct{step:newinst}\\[8px]
@{thm[mode=Rule] step.LoadFieldNode [no_vars]}\induct{step:load}\\[8px]
@{thm[mode=Rule] step.StoreFieldNode [no_vars]}\induct{step:store}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>

code_pred (modes: i \<Rightarrow> i * i * i \<Rightarrow> o * o * o \<Rightarrow> bool) step .

inductive step_top :: "Program \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> DynamicHeap \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> DynamicHeap \<Rightarrow> bool"
  ("_\<turnstile>_\<longrightarrow>_" 55) 
  for p where

  Lift:
  "\<lbrakk>g = p_method s p;
    g \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')\<rbrakk> 
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#xs, h) \<longrightarrow> ((s,nid',m')#xs, h')" |

  InvokeNodeStep:
  "\<lbrakk>g = p_method s p;
    kind g nid = (InvokeNode _ callTarget _ _ _ next);
    kind g callTarget = (MethodCallTargetNode targetMethod arguments);
    g m arguments \<longmapsto> vs;
    m' = set_params m vs\<rbrakk>
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#xs, h) \<longrightarrow> ((targetMethod,0,m')#(s,nid,m)#xs, h)" |

  InvokeWithExceptionNode:
  "\<lbrakk>g = p_method s p;
    kind g nid = (InvokeWithExceptionNode _ callTarget _ _ _ next _);
    kind g callTarget = (MethodCallTargetNode targetMethod arguments);
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
    c_m' = m_set c_nid (ObjRef (Some (2048))) c_m;
    c_nid' = (succ (p_method c_s p) c_nid)!0\<rbrakk> 
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#(c_s,c_nid,c_m)#xs, h) \<longrightarrow> ((c_s,c_nid',c_m')#xs, h)" |

  UnwindNode:
    "\<lbrakk>g = p_method s p;
      kind g nid = (UnwindNode exception);

      g m \<turnstile> exception (kind g exception) \<mapsto> e;

      c_g = (p_method c_s p);      
      kind c_g c_nid = (InvokeWithExceptionNode _ _ _ _ _ _ exceptionEdge);

      c_nid' = exceptionEdge;
      c_m' = set_state c_m Exception;
      c_m'' = m_set c_nid e c_m'\<rbrakk>
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#(c_s,c_nid,c_m)#xs, h) \<longrightarrow> ((c_s,c_nid',c_m'')#xs, h)"

text_raw \<open>\Snip{TopStepSemantics}%\<close>
text \<open>
\begin{center}
@{thm[mode=Rule] step_top.Lift [no_vars]}\induct{top:lift}\\[8px]
@{thm[mode=Rule] step_top.InvokeNodeStep [no_vars]}\induct{top:invoke}\\[8px]
@{thm[mode=Rule] step_top.InvokeWithExceptionNode [no_vars]}\induct{top:invoke_except}\\[8px]
@{thm[mode=Rule] step_top.ReturnNode [no_vars]}\induct{top:return}\\[8px]
@{thm[mode=Rule] step_top.UnwindNode [no_vars]}\induct{top:unwind}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>


code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) step_top .

type_synonym ExecLog = "(ID \<times> IRNode) list"

fun has_return :: "MapState \<Rightarrow> bool" where
  "has_return m = (((m_val m 0) \<noteq> UndefVal) \<or> ((m_state m) = Exception))"

inductive exec :: "Program 
      \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> DynamicHeap
      \<Rightarrow> ExecLog 
      \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> DynamicHeap
      \<Rightarrow> ExecLog 
      \<Rightarrow> bool"
  ("_ \<turnstile> _ | _ \<longrightarrow>* _ | _")
  where
  "\<lbrakk>p \<turnstile> (((s,nid,m)#xs),h) \<longrightarrow> (((s',nid',m')#ys),h');
    \<not>(has_return m');

    g = p_method s p;
    nk = kind g nid;
    l' = (l @ [(nid, nk)]);

    exec p (((s',nid',m')#ys),h') l' next_state l''\<rbrakk> 
    \<Longrightarrow> exec p (((s,nid,m)#xs),h) l next_state l''" 
(* TODO: refactor this stopping condition to be more abstract *)
  |
  "\<lbrakk>p \<turnstile> (((s,nid,m)#xs),h) \<longrightarrow> (((s',nid',m')#ys),h');
    has_return m';

    g = p_method s p;
    nk = kind g nid;
    l' = (l @ [(nid, nk)])\<rbrakk>
    \<Longrightarrow> exec p (((s,nid,m)#xs),h) l (((s',nid',m')#ys),h') l'"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool as Exec) "exec" .


inductive exec_debug :: "Program
     \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> DynamicHeap
     \<Rightarrow> nat
     \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> DynamicHeap
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
  "p3 = set_params new_map_state [IntVal 32 3] "

(* Eg. call eg2_sq with [3] \<longrightarrow> 9 *)
values "{m_val (prod.snd (prod.snd (hd (prod.fst res)))) 0 
        | res. (\<lambda>x . eg2_sq) \<turnstile> ([('''',0, p3), ('''',0, p3)], new_heap) \<rightarrow>*2* res}"

definition field_sq :: FieldName where
  "field_sq = ''sq''"

definition eg3_sq :: IRGraph where
  "eg3_sq = irgraph [
    (0, StartNode None 4, VoidStamp),
    (1, ParameterNode 0, default_stamp),
    (3, MulNode 1 1, default_stamp),
    (4, StoreFieldNode 4 field_sq 3 None None 5, VoidStamp),
    (5, ReturnNode (Some 3) None, default_stamp)
   ]"

(* Eg. call eg2_sq with [3] \<longrightarrow> heap with object None={sq: 9} *)
values "{h_load_field field_sq None (prod.snd res)
        | res. (\<lambda>x. eg3_sq) \<turnstile> ([('''', 0, p3), ('''', 0, p3)], new_heap) \<rightarrow>*3* res}"

definition eg4_sq :: IRGraph where
  "eg4_sq = irgraph [
    (0, StartNode None 4, VoidStamp),
    (1, ParameterNode 0, default_stamp),
    (3, MulNode 1 1, default_stamp),
    (4, NewInstanceNode 4 ''obj_class'' None 5, ObjectStamp ''obj_class'' True True True),
    (5, StoreFieldNode 5 field_sq 3 None (Some 4) 6, VoidStamp),
    (6, ReturnNode (Some 3) None, default_stamp)
   ]"

(* Eg. call eg2_sq with [3] \<longrightarrow> heap with object 24={sq: 9} *)
values "{h_load_field field_sq (Some 1) (prod.snd res)
        | res. (\<lambda>x. eg4_sq) \<turnstile> ([('''', 0, p3), ('''', 0, p3)], new_heap) \<rightarrow>*3* res}"
end

