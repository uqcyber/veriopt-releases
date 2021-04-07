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
  "h_load_field f r (h, n) = h f r"

fun h_store_field :: "FieldName \<Rightarrow> objref \<Rightarrow> Value \<Rightarrow> DynamicHeap \<Rightarrow> DynamicHeap" where
  "h_store_field f r v (h, n) = (h(f := ((h f)(r := v))), n)"

fun h_new_inst :: "DynamicHeap \<Rightarrow> DynamicHeap \<times> Value" where
  "h_new_inst (h, n) = ((h,n+1), (ObjRef (Some n)))"
text_raw \<open>\EndSnip\<close>

definition new_heap :: "DynamicHeap" where
  "new_heap =  ((\<lambda>f. \<lambda>p. UndefVal), 0)"

text_raw \<open>\Snip{programdef}%\<close>
type_synonym Signature = "string"
type_synonym Program = "Signature \<rightharpoonup> IRGraph"
text_raw \<open>\EndSnip\<close>

inductive step :: "IRGraph \<Rightarrow> (ID \<times> MapState \<times> DynamicHeap) \<Rightarrow> (ID \<times> MapState \<times> DynamicHeap) \<Rightarrow> bool"
  ("_ \<turnstile> _ \<rightarrow> _" 55) for g where

  SequentialNode:
  "\<lbrakk>is_sequential_node (kind g nid);
    next = (succ g nid)!0\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (next, m, h)" |

  IfNode:
  "\<lbrakk>kind g nid = (IfNode cond tb fb);
    g m \<turnstile> (kind g cond) \<mapsto> val;
    next = (if val_to_bool val then tb else fb)\<rbrakk>
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (next, m, h)" |  

  EndNodes:
  "\<lbrakk>isAbstractEndNodeType (kind g nid);
    merge = any_usage g nid;
    isAbstractMergeNodeType (kind g merge);

    i = input_index g merge nid;
    phis = (phi_list g merge);
    inputs = (phi_inputs g i phis);
    g m \<turnstile> inputs \<longmapsto> vs;

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
      g m \<turnstile> (kind g obj) \<mapsto> ObjRef ref;
      h_load_field f ref h = v;
      m' = m_set nid v m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h)" |

  StaticLoadFieldNode:
    "\<lbrakk>kind g nid = (LoadFieldNode nid f None nxt);
      h_load_field f None h = v;
      m' = m_set nid v m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h)" |

  StoreFieldNode:
    "\<lbrakk>kind g nid = (StoreFieldNode nid f newval _ (Some obj) nxt);
      g m \<turnstile> (kind g newval) \<mapsto> val;
      g m \<turnstile> (kind g obj) \<mapsto> ObjRef ref;
      h' = h_store_field f ref val h;
      m' = m_set nid val m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h')" |

  StaticStoreFieldNode:
    "\<lbrakk>kind g nid = (StoreFieldNode nid f newval _ None nxt);
      g m \<turnstile> (kind g newval) \<mapsto> val;
      h' = h_store_field f None val h;
      m' = m_set nid val m\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid, m, h) \<rightarrow> (nxt, m', h')"

text_raw \<open>\Snip{StepSemantics}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] step.SequentialNode [no_vars]}}{step:seq}
\induct{@{thm[mode=Rule] step.IfNode [no_vars]}}{step:if}
\induct{@{thm[mode=Rule] step.EndNodes [no_vars]}}{step:end}
\induct{@{thm[mode=Rule] step.RefNode [no_vars]}}{step:ref}
\induct{@{thm[mode=Rule] step.NewInstanceNode [no_vars]}}{step:newinst}
\induct{@{thm[mode=Rule] step.LoadFieldNode [no_vars]}}{step:load}
\induct{@{thm[mode=Rule] step.StoreFieldNode [no_vars]}}{step:store}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>
(*
inductive_cases StepE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> (nid,m,h) \<rightarrow> next"

inductive_cases StepNoModE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)"
*)

definition step_selectors :: "(IRNode \<Rightarrow> bool) set" where
  "step_selectors = {is_sequential_node, is_IfNode, isAbstractEndNodeType,
    is_RefNode, is_NewInstanceNode, is_LoadFieldNode, is_StoreFieldNode}"

theorem "stepDet":
   "(g \<turnstile> (nid,m,h) \<rightarrow> next) \<Longrightarrow>
   (\<forall> next'. ((g \<turnstile> (nid,m,h) \<rightarrow> next') \<longrightarrow> next = next'))"
proof (induction rule: "step.induct")
  case (SequentialNode nid "next" m h)
  have notif: "\<not>(is_IfNode (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps 
    by (metis is_IfNode_def)
  have notend: "\<not>(isAbstractEndNodeType (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps 
    by (metis isAbstractEndNodeType.simps is_EndNode.elims(2) is_LoopEndNode_def)
  have notref: "\<not>(is_RefNode (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps
    by (metis is_RefNode_def)
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps
    by (metis is_NewInstanceNode_def)
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps
    by (metis is_LoadFieldNode_def)
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    using SequentialNode.hyps(1) is_sequential_node.simps
    by (metis is_StoreFieldNode_def)
  from notif notend notref notnew notload notstore
  show ?case using SequentialNode step.cases
    by (smt (verit) is_IfNode_def is_LoadFieldNode_def is_NewInstanceNode_def is_RefNode_def is_StoreFieldNode_def prod.inject)
next
  case (IfNode nid cond tb fb m val "next" h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps isAbstractMergeNodeType.simps
    by (simp add: IfNode.hyps(1))
  have notend: "\<not>(isAbstractEndNodeType (kind g nid))"
    using isAbstractEndNodeType.simps
    by (simp add: IfNode.hyps(1))
  from notseq notend show ?case using IfNode evalDet
    by (smt (verit) IRNode.distinct(871) IRNode.distinct(891) IRNode.distinct(909) IRNode.distinct(923) IRNode.inject(11) Pair_inject step.cases)
next
  case (EndNodes nid merge i phis inputs m vs m' h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    using EndNodes.hyps(1) isAbstractEndNodeType.simps is_sequential_node.simps 
    by (metis is_EndNode.elims(2) is_LoopEndNode_def)
  have notif: "\<not>(is_IfNode (kind g nid))"
    using EndNodes.hyps(1)
    by (metis IRNode.disc(912) isAbstractEndNodeType.elims(1) is_EndNode.simps(12) is_IfNode_def)
  have notref: "\<not>(is_RefNode (kind g nid))"
    using EndNodes.hyps(1) is_sequential_node.simps
    by (metis IRNode.disc(1899) IRNode.distinct(1473) isAbstractEndNodeType.simps is_EndNode.elims(2) is_LoopEndNode_def is_RefNode_def)
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    using EndNodes.hyps(1) isAbstractEndNodeType.simps
    by (metis IRNode.distinct_disc(1442) is_EndNode.simps(29) is_NewInstanceNode_def)
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    using EndNodes.hyps(1) isAbstractEndNodeType.simps
    by (metis IRNode.disc(774) IRNode.distinct_disc(1284) is_EndNode.elims(2))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    using EndNodes.hyps(1) isAbstractEndNodeType.simps
    by (metis IRNode.distinct_disc(1459) IRNode.distinct_disc(706) is_EndNode.elims(2))
  from notseq notif notref notnew notload notstore
  show ?case using EndNodes evalAllDet
    by (smt (verit) is_IfNode_def is_LoadFieldNode_def is_NewInstanceNode_def is_RefNode_def is_StoreFieldNode_def prod.inject step.cases)
next
  case (RefNode nid nid' m h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps isAbstractMergeNodeType.simps
    by (simp add: RefNode.hyps(1))
  have notend: "\<not>(isAbstractEndNodeType (kind g nid))"
    using isAbstractEndNodeType.simps
    by (simp add: RefNode.hyps(1))
  from notseq notend
  show ?case
    by (smt (z3) IRNode.distinct(1329) IRNode.distinct(1739) IRNode.distinct(1937) IRNode.distinct(923) IRNode.sel(108) RefNode.hyps fst_conv snd_conv step.cases) 
next
  case (NewInstanceNode nid f obj nxt h' ref h m' m)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps isAbstractMergeNodeType.simps
    by (simp add: NewInstanceNode.hyps(1))
  have notend: "\<not>(isAbstractEndNodeType (kind g nid))"
    using isAbstractEndNodeType.simps
    by (simp add: NewInstanceNode.hyps(1))
  from notseq notend
  show ?case using NewInstanceNode step.cases
    by (smt (z3) IRNode.distinct(1297) IRNode.distinct(1725) IRNode.distinct(1739) IRNode.distinct(891) IRNode.inject(28) fst_conv snd_conv)
next
  case (LoadFieldNode nid f obj nxt m ref h v m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps isAbstractMergeNodeType.simps
    by (simp add: LoadFieldNode.hyps(1))
  have notend: "\<not>(isAbstractEndNodeType (kind g nid))"
    using isAbstractEndNodeType.simps
    by (simp add: LoadFieldNode.hyps(1))
  from notseq notend
  show ?case using LoadFieldNode step.cases
    by (smt (z3) IRNode.distinct(1297) IRNode.distinct(1315) IRNode.distinct(1329) IRNode.distinct(871) IRNode.inject(18) LoadFieldNode.hyps(1) LoadFieldNode.hyps(2) LoadFieldNode.hyps(3) LoadFieldNode.hyps(4) Pair_inject Value.inject(3) evalDet option.discI option.inject)
next
  case (StaticLoadFieldNode nid f nxt h v m' m)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps isAbstractMergeNodeType.simps
    by (simp add: StaticLoadFieldNode.hyps(1))
  have notend: "\<not>(isAbstractEndNodeType (kind g nid))"
    using isAbstractEndNodeType.simps
    by (simp add: StaticLoadFieldNode.hyps(1))
  from notseq notend
  show ?case using StaticLoadFieldNode step.cases
    by (smt (z3) IRNode.distinct(1297) IRNode.distinct(1315) IRNode.distinct(1329) IRNode.distinct(871) IRNode.inject(18) Pair_inject option.discI)
next
  case (StoreFieldNode nid f newval uu obj nxt m val ref h' h m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps isAbstractMergeNodeType.simps
    by (simp add: StoreFieldNode.hyps(1))
  have notend: "\<not>(isAbstractEndNodeType (kind g nid))"
    using isAbstractEndNodeType.simps
    by (simp add: StoreFieldNode.hyps(1))
  from notseq notend
  show ?case using StoreFieldNode step.cases
    by (smt (z3) IRNode.distinct(1315) IRNode.distinct(1725) IRNode.distinct(1937) IRNode.distinct(909) IRNode.inject(37) Pair_inject Value.inject(3) evalDet option.discI option.inject)
next
  case (StaticStoreFieldNode nid f newval uv nxt m val h' h m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps isAbstractMergeNodeType.simps
    by (simp add: StaticStoreFieldNode.hyps(1))
  have notend: "\<not>(isAbstractEndNodeType (kind g nid))"
    using isAbstractEndNodeType.simps
    by (simp add: StaticStoreFieldNode.hyps(1))
  from notseq notend
  show ?case using StoreFieldNode step.cases
    by (smt (z3) IRNode.distinct(1315) IRNode.distinct(1725) IRNode.distinct(1937) IRNode.distinct(909) IRNode.inject(37) Pair_inject StaticStoreFieldNode.hyps(1) StaticStoreFieldNode.hyps(2) StaticStoreFieldNode.hyps(3) StaticStoreFieldNode.hyps(4) evalDet option.distinct(1))
qed

code_pred (modes: i \<Rightarrow> i * i * i \<Rightarrow> o * o * o \<Rightarrow> bool) step .

inductive step_top :: "Program \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> DynamicHeap \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> DynamicHeap \<Rightarrow> bool"
  ("_ \<turnstile> _ \<longrightarrow> _" 55) 
  for p where

  Lift:
  "\<lbrakk>Some g = p s;
    g \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')\<rbrakk> 
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#stk, h) \<longrightarrow> ((s,nid',m')#stk, h')" |

  InvokeNodeStep:
  "\<lbrakk>Some g = p s;
    is_Invoke (kind g nid);

    callTarget = ir_callTarget (kind g nid);
    kind g callTarget = (MethodCallTargetNode targetMethod arguments);

    g m \<turnstile> arguments \<longmapsto> vs;
    m' = set_params m vs\<rbrakk>
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#stk, h) \<longrightarrow> ((targetMethod,0,m')#(s,nid,m)#stk, h)" |

  ReturnNode:
  "\<lbrakk>Some g = p s;
    kind g nid = (ReturnNode (Some expr) _);
    g m \<turnstile> (kind g expr) \<mapsto> v;

    Some c_g = p c_s;
    c_m' = m_set c_nid v c_m;
    c_nid' = (succ c_g c_nid)!0\<rbrakk> 
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#(c_s,c_nid,c_m)#stk, h) \<longrightarrow> ((c_s,c_nid',c_m')#stk, h)" |

  ReturnNodeVoid:
  "\<lbrakk>Some g = p s;
    kind g nid = (ReturnNode None _);
    Some c_g = p c_s;
    c_m' = m_set c_nid (ObjRef (Some (2048))) c_m;
    
    c_nid' = (succ c_g c_nid)!0\<rbrakk> 
    \<Longrightarrow> p \<turnstile> ((s,nid,m)#(c_s,c_nid,c_m)#stk, h) \<longrightarrow> ((c_s,c_nid',c_m')#stk, h)" |

  UnwindNode:
  "\<lbrakk>Some g = p s;
    kind g nid = (UnwindNode exception);

    g m \<turnstile> (kind g exception) \<mapsto> e;

    Some c_g = (p c_s);      
    kind c_g c_nid = (InvokeWithExceptionNode _ _ _ _ _ _ exEdge);

    c_m' = m_set c_nid e c_m\<rbrakk>
  \<Longrightarrow> p \<turnstile> ((s,nid,m)#(c_s,c_nid,c_m)#stk, h) \<longrightarrow> ((c_s,exEdge,c_m')#stk, h)"

text_raw \<open>\Snip{TopStepSemantics}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] step_top.Lift [no_vars]}}{top:lift}
\induct{@{thm[mode=Rule] step_top.InvokeNodeStep [no_vars]}}{top:invoke}
\induct{@{thm[mode=Rule] step_top.ReturnNode [no_vars]}}{top:return}
\induct{@{thm[mode=Rule] step_top.UnwindNode [no_vars]}}{top:unwind}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>


code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) step_top .

type_synonym Trace = "(Signature \<times> ID \<times> MapState) list"

fun has_return :: "MapState \<Rightarrow> bool" where
  "has_return m = ((m_val m 0) \<noteq> UndefVal)"

inductive exec :: "Program 
      \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> DynamicHeap
      \<Rightarrow> Trace 
      \<Rightarrow> (Signature \<times> ID \<times> MapState) list \<times> DynamicHeap
      \<Rightarrow> Trace 
      \<Rightarrow> bool"
  ("_ \<turnstile> _ | _ \<longrightarrow>* _ | _")
  for p
  where
  "\<lbrakk>p \<turnstile> (((s,nid,m)#xs),h) \<longrightarrow> (((s',nid',m')#ys),h');
    \<not>(has_return m');

    l' = (l @ [(s, nid,m)]);

    exec p (((s',nid',m')#ys),h') l' next_state l''\<rbrakk> 
    \<Longrightarrow> exec p (((s,nid,m)#xs),h) l next_state l''" 
(* TODO: refactor this stopping condition to be more abstract *)
  |
  "\<lbrakk>p \<turnstile> (((s,nid,m)#xs),h) \<longrightarrow> (((s',nid',m')#ys),h');
    has_return m';

    l' = (l @ [(s,nid,m)])\<rbrakk>
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
  "p3 = set_params new_map_state [IntVal 32 3]"

(* Eg. call eg2_sq with [3] \<longrightarrow> 9 *)
values "{m_val (prod.snd (prod.snd (hd (prod.fst res)))) 0 
        | res. (\<lambda>x . Some eg2_sq) \<turnstile> ([('''',0, p3), ('''',0, p3)], new_heap) \<rightarrow>*2* res}"

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
        | res. (\<lambda>x. Some eg3_sq) \<turnstile> ([('''', 0, p3), ('''', 0, p3)], new_heap) \<rightarrow>*3* res}"

definition eg4_sq :: IRGraph where
  "eg4_sq = irgraph [
    (0, StartNode None 4, VoidStamp),
    (1, ParameterNode 0, default_stamp),
    (3, MulNode 1 1, default_stamp),
    (4, NewInstanceNode 4 ''obj_class'' None 5, ObjectStamp ''obj_class'' True True True),
    (5, StoreFieldNode 5 field_sq 3 None (Some 4) 6, VoidStamp),
    (6, ReturnNode (Some 3) None, default_stamp)
   ]"

(* Eg. call eg2_sq with [3] \<longrightarrow> heap with object 0={sq: 9} *)
values "{h_load_field field_sq (Some 0) (prod.snd res)
        | res. (\<lambda>x. Some eg4_sq) \<turnstile> ([('''', 0, p3), ('''', 0, p3)], new_heap) \<rightarrow>*3* res}"
end

