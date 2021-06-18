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
    g y \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (BinaryExpr BinAdd xe ye)" |

  MulNode:
  "\<lbrakk>kind g n = MulNode x y;
    g x \<triangleright> xe;
    g y \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (BinaryExpr BinMul xe ye)" |

  SubNode:
  "\<lbrakk>kind g n = SubNode x y;
    g x \<triangleright> xe;
    g y \<triangleright> ye\<rbrakk>
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

fun stamp_expr :: "IRExpr \<Rightarrow> Stamp" where
"stamp_expr (UnaryExpr op x) = stamp_unary op (stamp_expr x)" |
"stamp_expr (BinaryExpr bop x y) = stamp_binary bop (stamp_expr x) (stamp_expr y)" |
"stamp_expr (ConstantExpr val) = constantAsStamp val" |
"stamp_expr (LeafExpr i s) = s" |
"stamp_expr (ParameterExpr i s) = s"

export_code stamp_unary stamp_binary stamp_expr

(* Creates the appropriate IRNode for a given binary operator. *)
fun bin_node :: "IRBinaryOp \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode" where
  "bin_node BinAdd x y = AddNode x y" |
  "bin_node BinMul x y = MulNode x y" |
  "bin_node BinSub x y = SubNode x y"

(* TODO: switch these to new Values2 *)
fun unary_eval :: "IRUnaryOp \<Rightarrow> Value \<Rightarrow> Value" where
  "unary_eval UnaryAbs (IntVal32 v1)  = IntVal32 ( (if sint(v1) < 0 then - v1 else v1) )" |
  "unary_eval UnaryAbs (IntVal64 v1)  = IntVal64 ( (if sint(v1) < 0 then - v1 else v1) )" |
  "unary_eval op v1 = UndefVal"

fun bin_eval :: "IRBinaryOp \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "bin_eval BinAdd v1 v2 = intval_add v1 v2" |
  "bin_eval BinMul v1 v2 = intval_mul v1 v2" |
  "bin_eval BinSub v1 v2 = intval_sub v1 v2"
(*  "bin_eval op v1 v2 = UndefVal" *)

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
  and
  unrepList :: "IRGraph \<Rightarrow> IRExpr list \<Rightarrow> (IRGraph \<times> ID list) \<Rightarrow> bool" ("_ \<triangleleft>\<triangleleft> _ \<leadsto> _" 55)
  for g where

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
  "\<lbrakk>g \<triangleleft>\<triangleleft> [xe, ye] \<leadsto> (g2, [x, y]);
    s' = stamp_binary op (stamp g2 x) (stamp g2 y);
    find_node_and_stamp g2 (bin_node op x y, s') = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (BinaryExpr op xe ye) \<leadsto> (g2, nid)" |

  BinaryNodeNew:
  "\<lbrakk>g \<triangleleft>\<triangleleft> [xe, ye] \<leadsto> (g2, [x, y]);
    s' = stamp_binary op (stamp g2 x) (stamp g2 y);
    find_node_and_stamp g2 (bin_node op x y, s') = None;
    nid = get_fresh_id g2;
    g' = add_node nid (bin_node op x y, s') g2\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (BinaryExpr op xe ye) \<leadsto> (g', nid)" |

  AllLeafNodes:
  "stamp g nid = s
    \<Longrightarrow> g \<triangleleft> (LeafExpr nid s) \<leadsto> (g, nid)" |

  NilList:
  "g \<triangleleft>\<triangleleft> [] \<leadsto> (g, [])" |

(* TODO: this will fail for [xe,ye] where they are not equal.
         Figure out how to generate code for this?
*)
  ConsList:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    g \<triangleleft>\<triangleleft> xes \<leadsto> (g2, xs)\<rbrakk>
    \<Longrightarrow> g \<triangleleft>\<triangleleft> (xe#xes) \<leadsto> (g2, x#xs)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as unrepE)
(*
  [show_steps,show_mode_inference,show_intermediate_results] 
*)  unrep .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as unrepListE) unrepList .

text_raw \<open>\Snip{unrepRules}%
\begin{center}
@{thm[mode=Rule] unrep_unrepList.ConstantNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.ConstantNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.ParameterNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.ParameterNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.BinaryNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.BinaryNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.AllLeafNodes [no_vars]}\\[8px]
\end{center}
\EndSnip\<close>

definition sq_param0 :: IRExpr where
  "sq_param0 = BinaryExpr BinMul 
    (ParameterExpr 0 (IntegerStamp 32 (- 2147483648) 2147483647))
    (ParameterExpr 0 (IntegerStamp 32 (- 2147483648) 2147483647))"

values "{(nid, g) . (eg2_sq \<triangleleft> sq_param0 \<leadsto> (g, nid))}"


subsection \<open>Data-flow Tree Evaluation\<close>

inductive
  evaltree :: "MapState \<Rightarrow> IRExpr \<Rightarrow> Value \<Rightarrow> bool" ("_ \<turnstile> _ \<mapsto> _" 55)
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
@{thm[mode=Rule] evaltree.ConstantExpr [no_vars]}\\[8px]
@{thm[mode=Rule] evaltree.ParameterExpr [no_vars]}\\[8px]
@{thm[mode=Rule] evaltree.UnaryExpr [no_vars]}\\[8px]
@{thm[mode=Rule] evaltree.BinaryExpr [no_vars]}\\[8px]
@{thm[mode=Rule] evaltree.LeafExpr [no_vars]}\\[8px]
\end{center}
\EndSnip\<close>

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as evalT)
  [show_steps,show_mode_inference,show_intermediate_results] 
  evaltree .

text_raw \<open>\Snip{evalCode}%
code\_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as evalE)
  [show\_steps,show\_mode_inference,show\_intermediate\_results] 
  evaltree .
\EndSnip\<close>

values "{v. evaltree (new_map [IntVal32 5]) sq_param0 v}"


(* derive a forward reasoning rule for each case. *)
inductive_cases ConstantExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "m \<turnstile> (ConstantExpr c) \<mapsto> val"
inductive_cases ParameterExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "m \<turnstile> (ParameterExpr i s) \<mapsto> val"
inductive_cases UnaryExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "m \<turnstile> (UnaryExpr op xe) \<mapsto> val"
inductive_cases BinaryExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "m \<turnstile> (BinaryExpr op xe ye) \<mapsto> val"
inductive_cases LeafExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "m \<turnstile> (LeafExpr nid s) \<mapsto> val"

(* group those forward rules into a named set *)
lemmas EvalTreeE\<^marker>\<open>tag invisible\<close> = 
  ConstantExprE
  ParameterExprE
  UnaryExprE
  BinaryExprE
  LeafExprE


lemma evaltree_det:
  fixes m e v1
  shows "(m \<turnstile> e \<mapsto> v1) \<Longrightarrow> 
         (\<forall> v2. ((m \<turnstile> e \<mapsto> v2) \<longrightarrow> v1 = v2))"
  apply (induction rule: "evaltree.induct")
  by (rule allI; rule impI; elim EvalTreeE; auto)+


subsection \<open>Data-flow Tree Refinement\<close>

(* This is the induced semantic equivalence relation between expressions.
   Note that syntactic equality implies semantics equivalence, but not vice versa.
*)
definition equiv_exprs :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<doteq> _" 55) where
  "(e1 \<doteq> e2) = (\<forall> m v. ((m \<turnstile> e1 \<mapsto> v) \<longleftrightarrow> (m \<turnstile> e2 \<mapsto> v)))"


(* We define a refinement ordering over IRExpr and show that it is a preorder.
  Note that it is asymmetric because e2 may refer to fewer variables than e1. *)
instantiation IRExpr :: preorder begin

definition
  le_expr_def [simp]: "(e1 \<le> e2) \<longleftrightarrow> (\<forall> m v. ((m \<turnstile> e1 \<mapsto> v) \<longrightarrow> (m \<turnstile> e2 \<mapsto> v)))"

definition
  lt_expr_def [simp]: "(e1 < e2) \<longleftrightarrow> (e1 \<le> e2 \<and> \<not> (e1 \<doteq> e2))"

(*
  assumes less_le_not_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
  and order_refl [iff]: "x \<le> x"
  and order_trans: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
*)
instance proof
  fix x y z :: IRExpr
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)" by (simp add: equiv_exprs_def; auto)
  show "x \<le> x" by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp 
qed



(*
Step 2b: prove monotonicity rules for each subexpression position?
 
Step 3: if e1 isrefby e2 then g[e1] isREFby g[e2]
*)
end
end

