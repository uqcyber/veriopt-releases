section \<open>Data-flow Semantics\<close>

theory IRTreeEval
  imports
    Graph.IRGraph
begin

text \<open>
We define a tree representation of data-flow nodes, as an abstraction of the graph view.

Data-flow trees are evaluated in the context of a method state
(currently called MapState in the theories for historical reasons).

The method state consists of the values for each method parameter, references to
method parameters use an index of the parameter within the parameter list, as such
we store a list of parameter values which are looked up at parameter references.

The method state also stores a mapping of node ids to values. The contents of this
mapping is calculates during the traversal of the control flow graph.

As a concrete example, as the @{term SignedDivNode} can have side-effects
(during division by zero), it is treated as part of the control-flow, since
the data-flow phase is specified to be side-effect free.
As a result, the control-flow semantics for @{term SignedDivNode} calculates the
value of a node and maps the node identifier to the value within the method state.
The data-flow semantics then just reads the value stored in the method state for the node.
\<close>

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


(* =========== TODO: move into IRGraph? ============== *)

(* A finite version of 'ids'.  There should be an easier way... *)
fun f_ids :: "IRGraph \<Rightarrow> ID fset" where
  "f_ids g = fset_of_list(sorted_list_of_set (dom (Rep_IRGraph g)))"
(* NOTE: above does not remove NoNode?
  "f_ids g = \<lbrace> nid |\<in>| dom g . (\<nexists>s. g nid = (Some (NoNode, s))) \<rbrace>"
*)

lemma f_ids[code]: "f_ids (irgraph m) = fset_of_list (map fst (no_node m))"
  sorry 
  (* TODO: apply (simp add: as_list.rep_eq) *)

export_code f_ids


fun find_node_and_stamp :: "IRGraph \<Rightarrow> (IRNode \<times> Stamp) \<Rightarrow> ID option" where
  "find_node_and_stamp g (n,s) =
     find (\<lambda>i. kind g i = n \<and> stamp g i = s) (sorted_list_of_fset(f_ids g))"

export_code find_node_and_stamp


(* ======================== START OF NEW TREE STUFF ==========================*)
subsection \<open>Data-flow Tree Representation\<close>

datatype IRUnaryOp = UnaryAbs | UnaryNeg
datatype IRBinaryOp = BinAdd | BinMul | BinSub

datatype (discs_sels) IRExpr =
  UnaryExpr (ir_uop: IRUnaryOp) (ir_value: IRExpr) 
  | BinaryExpr (ir_op: IRBinaryOp) (ir_x: IRExpr) (ir_y: IRExpr) 
(* TODO
  | AndExpr (ir_x: IRExpr) (ir_y: IRExpr)
  | ConditionalExpr (ir_condition: IRExpr) (ir_trueValue: IRExpr) (ir_falseValue: IRExpr) 
*)
  | ConstantExpr (ir_const: Value) 
(* TODO
  | IntegerEqualsNode (ir_x: IRExpr) (ir_y: IRExpr) 
  | IntegerLessThanNode (ir_x: IRExpr) (ir_y: IRExpr) 
  | IsNullNode (ir_value: IRExpr) 
  | LogicNegationNode (ir_value: IRExpr)
*)
(* TODO
  | NegateNode (ir_value: IRExpr) 
  | NotNode (ir_value: IRExpr) 
  | OrNode (ir_x: IRExpr) (ir_y: IRExpr) 
*)
  | ParameterExpr (ir_index: nat) (ir_stamp: Stamp)
(* Not needed?
  | PiNode (ir_object: IRExpr) (ir_guard_opt: "IRExpr option")
  | ShortCircuitOrNode (ir_x: IRExpr) (ir_y: IRExpr)
*)
(* Not needed?
  | UnwindNode (ir_exception: IRExpr) 
  | ValueProxyNode (ir_value: IRExpr) (ir_loopExit: IRExpr) 
*)
(* TODO
  | XorNode (ir_x: IRExpr) (ir_y: IRExpr) 
*)
  | LeafExpr (ir_nid: ID) (ir_stamp: Stamp)
  (* LeafExpr is for pre-evaluated nodes, like LoadFieldNode, SignedDivNode. *) 


inductive
  rep :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ _ \<triangleright> _" 55)
  for g where

  ConstantNode:
  "\<lbrakk>kind g n = ConstantNode c\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (ConstantExpr c)" |

  ParameterNode:
  "\<lbrakk>kind g n = ParameterNode i;
    stamp g n = s\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (ParameterExpr i s)" |

  AbsNode:
  "\<lbrakk>kind g n = AbsNode x;
    g x \<triangleright> xe\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (UnaryExpr UnaryAbs xe)" |

  AddNode:
  "\<lbrakk>kind g n = AddNode x y;
    g x \<triangleright> xe;
    g x \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (BinaryExpr BinAdd xe ye)" |

  MulNode:
  "\<lbrakk>kind g n = MulNode x y;
    g x \<triangleright> xe;
    g x \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (BinaryExpr BinMul xe ye)" |

  SubNode:
  "\<lbrakk>kind g n = SubNode x y;
    g x \<triangleright> xe;
    g x \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (BinaryExpr BinSub xe ye)" |

  LoadFieldNode: (* TODO others *)
  "\<lbrakk>kind g n = LoadFieldNode nid f obj nxt;
    stamp g n = s\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (LeafExpr nid s)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as exprE) rep .

text_raw \<open>\Snip{repRules}%
\begin{center}
@{thm[mode=Rule] rep.ConstantNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.ParameterNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.AbsNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.AddNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.MulNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.SubNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.LoadFieldNode [no_vars]}\\[8px]
\end{center}
\EndSnip\<close>

values "{t. eg2_sq 4  \<triangleright> t}"


(* ======== TODO: Functions for re-calculating stamps ========== *)
fun stamp_unary :: "IRUnaryOp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "stamp_unary op s1 = s1"

fun stamp_binary :: "IRBinaryOp \<Rightarrow> Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "stamp_binary op s1 s2 = s1"

export_code stamp_unary stamp_binary 

(* Creates the appropriate IRNode for a given binary operator. *)
fun bin_node :: "IRBinaryOp \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode" where
  "bin_node BinAdd x y = AddNode x y" |
  "bin_node BinMul x y = MulNode x y" |
  "bin_node BinSub x y = SubNode x y"

(* TODO: switch these to new Values2 *)
fun unary_eval :: "IRUnaryOp \<Rightarrow> Value \<Rightarrow> Value" where
  "unary_eval UnaryAbs (IntVal b1 v1)  = IntVal 32 (abs v1)" |
  "unary_eval op v1 = UndefVal"

fun bin_eval :: "IRBinaryOp \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "bin_eval BinAdd (IntVal b1 v1) (IntVal b2 v2) = IntVal 32 (v1+v2)" |
  "bin_eval BinMul (IntVal b1 v1) (IntVal b2 v2) = IntVal 32 (v1*v2)" |
  "bin_eval BinSub (IntVal b1 v1) (IntVal b2 v2) = IntVal 32 (v1-v2)" |
  "bin_eval op v1 v2 = UndefVal"

inductive fresh_id :: "IRGraph \<Rightarrow> ID \<Rightarrow> bool" where
  "nid \<notin> ids g \<Longrightarrow> fresh_id g nid"

code_pred fresh_id .

(* This generates a specific fresh ID (max+1), in a code-friendly way. *)
fun get_fresh_id :: "IRGraph \<Rightarrow> ID" where
(* Previous attempts - cannot generate code due to nat not Enum. 
  "get_fresh_id g = 100"
  "get_fresh_id g = (ffold max (0::nat) (f_ids g))"
  "get_fresh_id g = fst(last(as_list g))"
  "get_fresh_id g = last(sorted_list_of_set (dom (Rep_IRGraph g)))"
*)
  "get_fresh_id g = last(sorted_list_of_fset(f_ids g)) + 1"

export_code get_fresh_id
(* these examples return 6 and 7 respectively *)
value "get_fresh_id eg2_sq"
value "get_fresh_id (add_node 6 (ParameterNode 2, default_stamp) eg2_sq)"

(* Second version of tree insertion into graph:

      g \<triangleleft> expr \<leadsto> (g',nid) re-inserts expr into g and returns the new root nid.

   This means that we can try to re-use existing nodes by finding node IDs bottom-up.
*)
inductive
  unrep :: "IRGraph \<Rightarrow> IRExpr \<Rightarrow> (IRGraph \<times> ID) \<Rightarrow> bool" ("_ \<triangleleft> _ \<leadsto> _" 55)
  where

  ConstantNodeSame:
  "\<lbrakk>find_node_and_stamp g (ConstantNode c, constantAsStamp c) = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ConstantExpr c) \<leadsto> (g, nid)" |

  ConstantNodeNew:
  "\<lbrakk>find_node_and_stamp g (ConstantNode c, constantAsStamp c) = None;
    nid = get_fresh_id g;
    g' = add_node nid (ConstantNode c, constantAsStamp c) g \<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ConstantExpr c) \<leadsto> (g', nid)" |


  ParameterNodeSame:
  "\<lbrakk>find_node_and_stamp g (ParameterNode i, s) = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ParameterExpr i s) \<leadsto> (g, nid)" |

  ParameterNodeNew:
  "\<lbrakk>find_node_and_stamp g (ParameterNode i, s) = None;
    nid = get_fresh_id g;
    g' = add_node nid (ParameterNode i, s) g\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ParameterExpr i s) \<leadsto> (g', nid)" |


  AbsNodeSame:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    find_node_and_stamp g2 (AbsNode x, stamp g2 x) = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (UnaryExpr UnaryAbs xe) \<leadsto> (g2, nid)" |

  AbsNodeNew:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    find_node_and_stamp g2 (AbsNode x, stamp g2 x) = None;
    nid = get_fresh_id g2;
    s' = stamp_unary UnaryAbs (stamp g2 x);
    g' = add_node nid (AbsNode x, s') g2\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (UnaryExpr UnaryAbs xe) \<leadsto> (g', nid)" |


  BinaryNodeSame:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    g2 \<triangleleft> ye \<leadsto> (g3, y);
    s' = stamp_binary op (stamp g3 x) (stamp g3 y);
    find_node_and_stamp g3 (bin_node op x y, s') = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (BinaryExpr op xe ye) \<leadsto> (g3, nid)" |

  BinaryNodeNew:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    g2 \<triangleleft> ye \<leadsto> (g3, y);
    s' = stamp_binary op (stamp g3 x) (stamp g3 y);
    find_node_and_stamp g3 (bin_node op x y, s') = None;
    nid = get_fresh_id g3;
    g' = add_node nid (bin_node op x y, s') g3\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (BinaryExpr op xe ye) \<leadsto> (g', nid)" |

  AllLeafNodes:
  "stamp g nid = s
    \<Longrightarrow> g \<triangleleft> (LeafExpr nid s) \<leadsto> (g, nid)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as unrepE)
(*
  [show_steps,show_mode_inference,show_intermediate_results] 
*)  unrep .

text_raw \<open>\Snip{unrepRules}%
\begin{center}
@{thm[mode=Rule] unrep.ConstantNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.ConstantNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.ParameterNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.ParameterNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.BinaryNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.BinaryNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.AllLeafNodes [no_vars]}\\[8px]
\end{center}
\EndSnip\<close>

definition sq_param0 :: IRExpr where
  "sq_param0 = BinaryExpr BinMul 
    (ParameterExpr 0 (IntegerStamp 32 (- 2147483648) 2147483647))
    (ParameterExpr 0 (IntegerStamp 32 (- 2147483648) 2147483647))"

values "{(nid, g) . (eg2_sq \<triangleleft> sq_param0 \<leadsto> (g, nid))}"


subsection \<open>Data-flow Tree Evaluation\<close>

inductive
  eval :: "MapState \<Rightarrow> IRExpr \<Rightarrow> Value \<Rightarrow> bool" ("_ \<turnstile> _ \<mapsto> _" 55)
  for m where

  ConstantExpr:
  "m \<turnstile> (ConstantExpr c) \<mapsto> c" |

  ParameterExpr:
  "m \<turnstile> (ParameterExpr i s) \<mapsto> (m_params m)!i" |

  UnaryExpr:
  "\<lbrakk>m \<turnstile> xe \<mapsto> v\<rbrakk>
    \<Longrightarrow> m \<turnstile> (UnaryExpr op xe) \<mapsto> unary_eval op v" |

  BinaryExpr:
  "\<lbrakk>m \<turnstile> xe \<mapsto> x;
    m \<turnstile> ye \<mapsto> y\<rbrakk>
    \<Longrightarrow> m \<turnstile> (BinaryExpr op xe ye) \<mapsto> bin_eval op x y" |

  LeafExpr:
  "\<lbrakk>val = m_values m nid\<rbrakk>
    \<Longrightarrow> m \<turnstile> LeafExpr nid s \<mapsto> val"

text_raw \<open>\Snip{evalRules}%
\begin{center}
@{thm[mode=Rule] eval.ConstantExpr [no_vars]}\\[8px]
@{thm[mode=Rule] eval.ParameterExpr [no_vars]}\\[8px]
@{thm[mode=Rule] eval.UnaryExpr [no_vars]}\\[8px]
@{thm[mode=Rule] eval.BinaryExpr [no_vars]}\\[8px]
@{thm[mode=Rule] eval.LeafExpr [no_vars]}\\[8px]
\end{center}
\EndSnip\<close>

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as evalE)
  [show_steps,show_mode_inference,show_intermediate_results] 
  eval .

text_raw \<open>\Snip{evalCode}%
code\_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as evalE)
  [show\_steps,show\_mode_inference,show\_intermediate\_results] 
  eval .
\EndSnip\<close>

values "{v. eval (new_map [IntVal 32 5]) sq_param0 v}"

end

