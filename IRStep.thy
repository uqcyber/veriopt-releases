section \<open>Inductive small-step semantics of IR graphs\<close>

theory IRStep
  imports
    IREval
begin


text_raw \<open>\Snip{StepSemantics}%\<close>
inductive step :: "IRGraph \<Rightarrow> (ID \<times> MapState) \<Rightarrow> (ID \<times> MapState) \<Rightarrow> bool"
  ("_ \<turnstile> _\<rightarrow>_" 55)
  for g where

  SequentialNode:
  "\<lbrakk>node = kind g nid;
    is_sequential_node(node);
    next = (succ g nid)!0\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) \<rightarrow> (next, m)" |

  IfNode:
  "\<lbrakk>kind g nid = (IfNode cond true false);
    g m \<turnstile> cond (kind g cond) \<mapsto> (IntVal val);
    next = (if val_to_bool val then true else false)\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m) \<rightarrow> (next, m)" |  

  EndNodes:
  "\<lbrakk>is_end_node(kind g nid);
    merge = any_usage g nid;
    is_merge_node(kind g merge);

    i = input_index g merge nid;
    phis = (phi_list g merge);
    inputs = (phi_inputs g i phis);
    g m inputs \<longmapsto> vs;

    m' = (set_phis phis vs m)\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) \<rightarrow> (merge, m')" |

  RefNode:
    "kind g nid = RefNode nid'
    \<Longrightarrow> g \<turnstile> (nid, m) \<rightarrow> (nid', m)"
text_raw \<open>\EndSnip\<close>

code_pred (modes: i \<Rightarrow> i * i \<Rightarrow> o * o \<Rightarrow> bool) step .


text_raw \<open>\Snip{TopStepSemantics}%\<close>
inductive step_top :: "IRGraph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool"
  ("_\<turnstile>_\<longrightarrow>_" 55) 
  for g where

  "\<lbrakk>g \<turnstile> (nid, m) \<rightarrow> (nid', m')\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m) # xs \<longrightarrow> (nid', m') # xs" |

  CallNodeStep:
  "\<lbrakk>kind g nid = (CallNode start args _);
    g m args \<longmapsto> vs;
    m' =  set_params new_map_state vs\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m)#xs \<longrightarrow> (start, m')#(nid,m)#xs" |

  ReturnNode:
  "\<lbrakk>kind g nid = (ReturnNode (Some expr) _);
    g m \<turnstile> expr (kind g expr) \<mapsto> v;
    c_m' = m_set c_nid v c_m;
    c_nid' = (succ g c_nid)!0\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid,m)#(c_nid,c_m)#xs \<longrightarrow> (c_nid',c_m')#xs" |

  ReturnNodeVoid:
  "\<lbrakk>kind g nid = (ReturnNode None _);
    c_nid' = (succ g c_nid)!0\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid,m)#(c_nid,c_m)#xs \<longrightarrow> (c_nid',c_m)#xs"


text_raw \<open>\EndSnip\<close>

(*

  ExitReturnNode:
  "\<lbrakk>kind g nid = (ReturnNode (Some expr) _);
    g m \<turnstile> expr (kind g expr) \<mapsto> v;
    m' = m_set nid v m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m)#[] \<longrightarrow> []"
*)

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) step_top .

type_synonym ExecLog = "(ID \<times> IRNode) list"


inductive exec :: "IRGraph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> ExecLog \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> ExecLog \<Rightarrow> bool"
  ("_ \<turnstile> _ | _ \<longrightarrow>* _ | _")
  where
  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    m_val (prod.snd (s'!0)) 0 = UndefVal;
    nid = prod.fst (s!0);
    l' = (l @ [(nid, (kind g nid))]);
    exec g s' l' s'' l''\<rbrakk> 
    \<Longrightarrow> exec g s l s'' l''" 
(* TODO: refactor this stopping condition to be more abstract *)
  |
  "\<lbrakk>g \<turnstile> s \<longrightarrow> s';
    m_val (prod.snd (s'!0)) 0 \<noteq> UndefVal;
    nid = prod.fst (s!0);
    l' = (l @ [(nid, (kind g nid))])\<rbrakk>
    \<Longrightarrow> exec g s l s' l'"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) "exec" .


inductive exec_debug :: "IRGraph \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> nat \<Rightarrow> (ID \<times> MapState) list \<Rightarrow> bool"
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
  "p3 = new_map [IntVal 3]"

(* Eg. call eg2_sq with [3] \<longrightarrow> 9 *)
values "{m_val (prod.snd (hd res)) 0 | res. eg2_sq \<turnstile> [(0, p3), (0, p3)] \<rightarrow>*2* res}"
end

