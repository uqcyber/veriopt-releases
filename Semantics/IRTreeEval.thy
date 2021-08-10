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

type_synonym MapState = "ID \<Rightarrow> Value"
type_synonym Params = "Value list"

definition new_map_state :: "MapState" where
  "new_map_state = (\<lambda>x. UndefVal)"

fun val_to_bool :: "Value \<Rightarrow> bool" where
  "val_to_bool (IntVal32 val) = (if val = 0 then False else True)" |
  "val_to_bool v = False"

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal32  1)" |
  "bool_to_val False = (IntVal32 0)"


(* TODO: move the following phi helpers to step semantics? *)
(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index v (x # xs) = (if (x=v) then 0 else find_index v xs + 1)"

fun phi_list :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "phi_list g nid = 
    (filter (\<lambda>x.(is_PhiNode (kind g x)))
      (sorted_list_of_set (usages g nid)))"

fun input_index :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> nat" where
  "input_index g n n' = find_index n' (inputs_of (kind g n))"

fun phi_inputs :: "IRGraph \<Rightarrow> nat \<Rightarrow> ID list \<Rightarrow> ID list" where
  "phi_inputs g i nodes = (map (\<lambda>n. (inputs_of (kind g n))!(i + 1)) nodes)"

fun set_phis :: "ID list \<Rightarrow> Value list \<Rightarrow> MapState \<Rightarrow> MapState" where
  "set_phis [] [] m = m" |
  "set_phis (nid # xs) (v # vs) m = (set_phis xs vs (m(nid := v)))" |
  "set_phis [] (v # vs) m = m" |
  "set_phis (x # xs) [] m = m"


fun find_node_and_stamp :: "IRGraph \<Rightarrow> (IRNode \<times> Stamp) \<Rightarrow> ID option" where
  "find_node_and_stamp g (n,s) =
     find (\<lambda>i. kind g i = n \<and> stamp g i = s) (sorted_list_of_set(ids g))"

export_code find_node_and_stamp


(* ======================== START OF NEW TREE STUFF ==========================*)
subsection \<open>Data-flow Tree Representation\<close>

datatype IRUnaryOp =
    UnaryAbs
  | UnaryNeg
  | UnaryNot
  | UnaryLogicNegation

datatype IRBinaryOp =
    BinAdd
  | BinMul
  | BinSub
  | BinAnd
  | BinOr
  | BinXor
  | BinIntegerEquals
  | BinIntegerLessThan
  | BinIntegerBelow

datatype IRConvertOp =
    ConvertNarrow 
  | ConvertSignExtend 
  | ConvertZeroExtend

datatype (discs_sels) IRExpr =
    UnaryExpr (ir_uop: IRUnaryOp) (ir_value: IRExpr)
  | BinaryExpr (ir_op: IRBinaryOp) (ir_x: IRExpr) (ir_y: IRExpr)
  | ConditionalExpr (ir_condition: IRExpr) (ir_trueValue: IRExpr) (ir_falseValue: IRExpr)
  | ConstantExpr (ir_const: Value)
  | ConvertExpr (ir_cop: IRConvertOp) (ir_input: IRExpr) (*(ir_input_bits: nat) (ir_result_bits: nat)*)
(* TODO
  | IsNullNode (ir_value: IRExpr) 
  | RefNode ?
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
  | LeafExpr (ir_nid: ID) (ir_stamp: Stamp)
  (* LeafExpr is for pre-evaluated nodes, like LoadFieldNode, SignedDivNode. *) 


(* These kinds of nodes are evaluated during the control flow, so are already in MapState. *)
fun is_preevaluated :: "IRNode \<Rightarrow> bool" where
  "is_preevaluated (InvokeNode nid _ _ _ _ _) = True" |
  "is_preevaluated (InvokeWithExceptionNode nid _ _ _ _ _ _) = True" |
  "is_preevaluated (NewInstanceNode nid _ _ _) = True" |
  "is_preevaluated (LoadFieldNode nid _ _ _) = True" |
  "is_preevaluated (SignedDivNode nid _ _ _ _ _) = True" |
  "is_preevaluated (SignedRemNode nid _ _ _ _ _) = True" |
  "is_preevaluated (ValuePhiNode nid _ _) = True" |
  "is_preevaluated _ = False"


inductive
  rep :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<turnstile> _ \<triangleright> _" 55)
  for g where

  ConstantNode:
  "\<lbrakk>kind g n = ConstantNode c\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (ConstantExpr c)" |

  ParameterNode:
  "\<lbrakk>kind g n = ParameterNode i;
    stamp g n = s\<rbrakk>
    \<Longrightarrow> g  \<turnstile> n \<triangleright> (ParameterExpr i s)" |

  ConditionalNode:
  "\<lbrakk>kind g n = ConditionalNode c t f;
    g \<turnstile> c \<triangleright> ce;
    g \<turnstile> t \<triangleright> te;
    g \<turnstile> f \<triangleright> fe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (ConditionalExpr ce te fe)" |

(* Unary nodes *)
  AbsNode:
  "\<lbrakk>kind g n = AbsNode x;
    g \<turnstile> x \<triangleright> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (UnaryExpr UnaryAbs xe)" |

  NotNode:
  "\<lbrakk>kind g n = NotNode x;
    g \<turnstile> x \<triangleright> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (UnaryExpr UnaryNot xe)" |

  NegateNode:
  "\<lbrakk>kind g n = NegateNode x;
    g \<turnstile> x \<triangleright> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (UnaryExpr UnaryNeg xe)" |

  LogicNegationNode:
  "\<lbrakk>kind g n = LogicNegationNode x;
    g \<turnstile> x \<triangleright> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (UnaryExpr UnaryLogicNegation xe)" |

(* Binary nodes *)
  AddNode:
  "\<lbrakk>kind g n = AddNode x y;
    g \<turnstile> x \<triangleright> xe;
    g \<turnstile> y \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (BinaryExpr BinAdd xe ye)" |

  MulNode:
  "\<lbrakk>kind g n = MulNode x y;
    g \<turnstile> x \<triangleright> xe;
    g \<turnstile> y \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (BinaryExpr BinMul xe ye)" |

  SubNode:
  "\<lbrakk>kind g n = SubNode x y;
    g \<turnstile> x \<triangleright> xe;
    g \<turnstile> y \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (BinaryExpr BinSub xe ye)" |

  AndNode:
  "\<lbrakk>kind g n = AndNode x y;
    g \<turnstile> x \<triangleright> xe;
    g \<turnstile> y \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (BinaryExpr BinAnd xe ye)" |

  OrNode:
  "\<lbrakk>kind g n = OrNode x y;
    g \<turnstile> x \<triangleright> xe;
    g \<turnstile> y \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (BinaryExpr BinOr xe ye)" |

  XorNode:
  "\<lbrakk>kind g n = XorNode x y;
    g \<turnstile> x \<triangleright> xe;
    g \<turnstile> y \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (BinaryExpr BinXor xe ye)" |

  IntegerBelowNode:
  "\<lbrakk>kind g n = IntegerBelowNode x y;
    g \<turnstile> x \<triangleright> xe;
    g \<turnstile> y \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (BinaryExpr BinIntegerBelow xe ye)" |

  IntegerEqualsNode:
  "\<lbrakk>kind g n = IntegerEqualsNode x y;
    g \<turnstile> x \<triangleright> xe;
    g \<turnstile> y \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (BinaryExpr BinIntegerEquals xe ye)" |

  IntegerLessThanNode:
  "\<lbrakk>kind g n = IntegerLessThanNode x y;
    g \<turnstile> x \<triangleright> xe;
    g \<turnstile> y \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (BinaryExpr BinIntegerLessThan xe ye)" |

(* Convert Nodes *)
  NarrowNode:
  "\<lbrakk>kind g n = NarrowNode x;
    g \<turnstile> x \<triangleright> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (ConvertExpr ConvertNarrow xe)" |

  SignExtendNode:
  "\<lbrakk>kind g n = SignExtendNode x;
    g \<turnstile> x \<triangleright> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (ConvertExpr ConvertSignExtend xe)" |

  ZeroExtendNode:
  "\<lbrakk>kind g n = ZeroExtendNode x;
    g \<turnstile> x \<triangleright> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (ConvertExpr ConvertZeroExtend xe)" |

(* Leaf Node *)
  LeafNode:
  "\<lbrakk>is_preevaluated (kind g n);
    stamp g n = s\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<triangleright> (LeafExpr n s)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as exprE) rep .


inductive
  replist :: "IRGraph \<Rightarrow> ID list \<Rightarrow> IRExpr list \<Rightarrow> bool" ("_ \<turnstile> _ \<triangleright>\<^sub>L _" 55)
  for g where

  RepNil:
  "g \<turnstile> [] \<triangleright>\<^sub>L []" |

  RepCons:
  "\<lbrakk>g \<turnstile> x \<triangleright> xe;
    g \<turnstile> xs \<triangleright>\<^sub>L xse\<rbrakk>
    \<Longrightarrow> g \<turnstile> x#xs \<triangleright>\<^sub>L xe#xse"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as exprListE) replist .


text_raw \<open>\Snip{repRules}%
\begin{center}
@{thm[mode=Rule] rep.ConstantNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.ParameterNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.AbsNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.AddNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.MulNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.SubNode [no_vars]}\\[8px]
@{thm[mode=Rule] rep.LeafNode [no_vars]}\\[8px]
\end{center}
\EndSnip\<close>

values "{t. eg2_sq \<turnstile> 4 \<triangleright> t}"

inductive_cases ConstantNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (ConstantExpr c)"
inductive_cases ParameterNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (ParameterExpr i s)"
inductive_cases ConditionalNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (ConditionalExpr ce te fe)"
inductive_cases AbsNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (UnaryExpr UnaryAbs xe)"
inductive_cases NotNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (UnaryExpr UnaryNot xe)"
inductive_cases NegateNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (UnaryExpr UnaryNeg xe)"
inductive_cases LogicNegationNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (UnaryExpr UnaryLogicNegation xe)"
inductive_cases AddNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (BinaryExpr BinAdd xe ye)"
inductive_cases MulNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (BinaryExpr BinMul xe ye)"
inductive_cases SubNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (BinaryExpr BinSub xe ye)"
inductive_cases AndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (BinaryExpr BinAnd xe ye)"
inductive_cases OrNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (BinaryExpr BinOr xe ye)"
inductive_cases XorNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (BinaryExpr BinXor xe ye)"
inductive_cases IntegerBelowNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (BinaryExpr BinIntegerBelow xe ye)"
inductive_cases IntegerEqualsNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (BinaryExpr BinIntegerEquals xe ye)"
inductive_cases IntegerLessThanNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (BinaryExpr BinIntegerLessThan xe ye)"
inductive_cases NarrowNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (ConvertExpr ConvertNarrow xe)"
inductive_cases SignExtendNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (ConvertExpr ConvertSignExtend xe)"
inductive_cases ZeroExtendNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (ConvertExpr ConvertZeroExtend xe)"
inductive_cases LeafNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<triangleright> (LeafExpr nid s)"

(* group those forward rules into a named set *)
lemmas RepE\<^marker>\<open>tag invisible\<close> = 
  ConstantNodeE
  ParameterNodeE
  ConditionalNodeE
  AbsNodeE
  NotNodeE
  NegateNodeE
  LogicNegationNodeE
  AddNodeE
  MulNodeE
  SubNodeE
  AndNodeE
  OrNodeE
  XorNodeE
  IntegerBelowNodeE
  IntegerEqualsNodeE
  IntegerLessThanNodeE
  NarrowNodeE
  SignExtendNodeE
  ZeroExtendNodeE
  LeafNodeE

(* ======== TODO: Functions for re-calculating stamps ========== *)
fun stamp_unary :: "IRUnaryOp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "stamp_unary op (IntegerStamp b lo hi) = unrestricted_stamp (IntegerStamp b lo hi)" |
  (* for now... *)
  "stamp_unary op _ = IllegalStamp"

fun stamp_binary :: "IRBinaryOp \<Rightarrow> Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "stamp_binary op (IntegerStamp b1 lo1 hi1) (IntegerStamp b2 lo2 hi2) =
    (if (b1 = b2) then unrestricted_stamp (IntegerStamp b1 lo1 hi1) else IllegalStamp)" |
  (* for now... *)
  "stamp_binary op _ _ = IllegalStamp"

(* TODO: we may need to put stamp information into expression trees somehow.. *)
fun stamp_convert_op :: "IRConvertOp \<Rightarrow> Stamp \<Rightarrow> Stamp" where 
  "stamp_convert_op op (IntegerStamp b lo hi) = unrestricted_stamp (IntegerStamp b lo hi)" |
  "stamp_convert_op op _ = IllegalStamp"

fun stamp_expr :: "IRExpr \<Rightarrow> Stamp" where
  "stamp_expr (UnaryExpr op x) = stamp_unary op (stamp_expr x)" |
  "stamp_expr (ConvertExpr cop x) = stamp_convert_op cop (stamp_expr x)" |
  "stamp_expr (BinaryExpr bop x y) = stamp_binary bop (stamp_expr x) (stamp_expr y)" |
  "stamp_expr (ConstantExpr val) = constantAsStamp val" |
  "stamp_expr (LeafExpr i s) = s" |
  "stamp_expr (ParameterExpr i s) = s" |
  "stamp_expr (ConditionalExpr c t f) = meet (stamp_expr t) (stamp_expr f)"


export_code stamp_unary stamp_binary stamp_expr

fun unary_node :: "IRUnaryOp \<Rightarrow> ID \<Rightarrow> IRNode" where
  "unary_node UnaryAbs v = AbsNode v" |
  "unary_node UnaryNot v = NotNode v" |
  "unary_node UnaryNeg v = NegateNode v" |
  "unary_node UnaryLogicNegation v = LogicNegationNode v"

(* Creates the appropriate IRNode for a given binary operator. *)
fun bin_node :: "IRBinaryOp \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode" where
  "bin_node BinAdd x y = AddNode x y" |
  "bin_node BinMul x y = MulNode x y" |
  "bin_node BinSub x y = SubNode x y" |
  "bin_node BinAnd x y = AndNode x y" |
  "bin_node BinOr  x y = OrNode x y" |
  "bin_node BinXor x y = XorNode x y" |
  "bin_node BinIntegerEquals x y = IntegerEqualsNode x y" |
  "bin_node BinIntegerLessThan x y = IntegerLessThanNode x y" |
  "bin_node BinIntegerBelow x y = IntegerBelowNode x y"

(*fun convert_node :: "IRConvertOp \<Rightarrow> ID \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> IRNode" where*)
fun convert_node :: "IRConvertOp \<Rightarrow> ID \<Rightarrow> IRNode" where
  "convert_node ConvertNarrow v = NarrowNode v" |
  "convert_node ConvertSignExtend v = SignExtendNode v"  |
  "convert_node ConvertZeroExtend v = ZeroExtendNode v"

(* TODO: switch these to new Values2 *)
fun unary_eval :: "IRUnaryOp \<Rightarrow> Value \<Rightarrow> Value" where
  "unary_eval UnaryAbs v = intval_abs v" |
  "unary_eval UnaryNeg v = intval_negate v" |
  "unary_eval UnaryNot v = intval_not v" |
  "unary_eval UnaryLogicNegation (IntVal32 v1) = (if v1 = 0 then (IntVal32 1) else (IntVal32 0))" |
  "unary_eval op v1 = UndefVal"

fun bin_eval :: "IRBinaryOp \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "bin_eval BinAdd v1 v2 = intval_add v1 v2" |
  "bin_eval BinMul v1 v2 = intval_mul v1 v2" |
  "bin_eval BinSub v1 v2 = intval_sub v1 v2" |
  "bin_eval BinAnd v1 v2 = intval_and v1 v2" |
  "bin_eval BinOr  v1 v2 = intval_or v1 v2" |
  "bin_eval BinXor v1 v2 = intval_xor v1 v2" |
  "bin_eval BinIntegerEquals v1 v2 = intval_equals v1 v2" |
  "bin_eval BinIntegerLessThan v1 v2 = intval_less_than v1 v2" |
  "bin_eval BinIntegerBelow v1 v2 = intval_below v1 v2"
(*  "bin_eval op v1 v2 = UndefVal" *)


value "word_of_int (sint (240 :: 32 word)) :: 8 word" 

fun convert_eval :: "IRConvertOp \<Rightarrow> Value \<Rightarrow> Value" where
  "convert_eval ConvertNarrow v = v" | 
  "convert_eval ConvertSignExtend v = v" | 
  "convert_eval ConvertZeroExtend v = v" 

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
  "get_fresh_id g = last(sorted_list_of_set(ids g)) + 1"

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
  unrepList :: "IRGraph \<Rightarrow> IRExpr list \<Rightarrow> (IRGraph \<times> ID list) \<Rightarrow> bool" ("_ \<triangleleft>\<^sub>L _ \<leadsto> _" 55)
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

  ConditionalNodeSame:
  "\<lbrakk>g \<triangleleft>\<^sub>L [ce, te, fe] \<leadsto> (g2, [c, t, f]);
    s' = meet (stamp g2 t) (stamp g2 f);
    find_node_and_stamp g2 (ConditionalNode c t f, s') = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ConditionalExpr ce te fe) \<leadsto> (g2, nid)" |

  ConditionalNodeNew:
  "\<lbrakk>g \<triangleleft>\<^sub>L [ce, te, fe] \<leadsto> (g2, [c, t, f]);
    s' = meet (stamp g2 t) (stamp g2 f);
    find_node_and_stamp g2 (ConditionalNode c t f, s') = None;
    nid = get_fresh_id g2;
    g' = add_node nid (ConditionalNode c t f, s') g2\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ConditionalExpr ce te fe) \<leadsto> (g', nid)" |

  UnaryNodeSame:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    s' = stamp_unary op (stamp g2 x);
    find_node_and_stamp g2 (unary_node op x, s') = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (UnaryExpr op xe) \<leadsto> (g2, nid)" |

  UnaryNodeNew:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    s' = stamp_unary op (stamp g2 x);
    find_node_and_stamp g2 (unary_node op x, s') = None;
    nid = get_fresh_id g2;
    g' = add_node nid (unary_node op x, s') g2\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (UnaryExpr op xe) \<leadsto> (g', nid)" |

  BinaryNodeSame:
  "\<lbrakk>g \<triangleleft>\<^sub>L [xe, ye] \<leadsto> (g2, [x, y]);
    s' = stamp_binary op (stamp g2 x) (stamp g2 y);
    find_node_and_stamp g2 (bin_node op x y, s') = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (BinaryExpr op xe ye) \<leadsto> (g2, nid)" |

  BinaryNodeNew:
  "\<lbrakk>g \<triangleleft>\<^sub>L [xe, ye] \<leadsto> (g2, [x, y]);
    s' = stamp_binary op (stamp g2 x) (stamp g2 y);
    find_node_and_stamp g2 (bin_node op x y, s') = None;
    nid = get_fresh_id g2;
    g' = add_node nid (bin_node op x y, s') g2\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (BinaryExpr op xe ye) \<leadsto> (g', nid)" |

  ConvertNodeSame:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    s' = stamp_convert_op op (stamp g2 x);
    find_node_and_stamp g2 (convert_node op x, s') = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ConvertExpr op xe) \<leadsto> (g2, nid)" |

  ConvertNodeNew:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    s' = stamp_convert_op op (stamp g2 x);
    find_node_and_stamp g2 (convert_node op x, s') = None;
    nid = get_fresh_id g2;
    g' = add_node nid (convert_node op x, s') g2\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ConvertExpr op xe) \<leadsto> (g', nid)" |

  AllLeafNodes:
  "stamp g nid = s
    \<Longrightarrow> g \<triangleleft> (LeafExpr nid s) \<leadsto> (g, nid)" |

  UnrepNil:
  "g \<triangleleft>\<^sub>L [] \<leadsto> (g, [])" |

(* TODO: this will fail for [xe,ye] where they are not equal.
         Figure out how to generate code for this?
*)
  UnrepCons:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    g2 \<triangleleft>\<^sub>L xes \<leadsto> (g3, xs)\<rbrakk>
    \<Longrightarrow> g \<triangleleft>\<^sub>L (xe#xes) \<leadsto> (g3, x#xs)"

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
@{thm[mode=Rule] unrep_unrepList.ConditionalNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.ConditionalNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.BinaryNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.BinaryNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.UnaryNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.UnaryNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep_unrepList.AllLeafNodes [no_vars]}\\[8px]
\end{center}
\EndSnip\<close>

definition sq_param0 :: IRExpr where
  "sq_param0 = BinaryExpr BinMul 
    (ParameterExpr 0 (IntegerStamp 32 (- 2147483648) 2147483647))
    (ParameterExpr 0 (IntegerStamp 32 (- 2147483648) 2147483647))"

(*
instantiation IRGraph :: equal begin

definition "(g1 = g2) \<longleftrightarrow> 
              (f_ids g1 = f_ids g2 \<and>
               (\<forall>n. (n \<in> ids g1 \<Longrightarrow> (Rep_IRGraph g1 n = Rep_IRGraph g2 n))))"
instance proof 
  fix x y :: IRGraph
  show "x = y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)" by (simp add: equiv_exprs_def; auto)
  show "x \<le> x" by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp 
qed
end
*)

values "{(nid, g) . (eg2_sq \<triangleleft> sq_param0 \<leadsto> (g, nid))}"


subsection \<open>Data-flow Tree Evaluation\<close>

inductive
  evaltree :: "MapState \<Rightarrow> Params \<Rightarrow> IRExpr \<Rightarrow> Value \<Rightarrow> bool" ("[_,_] \<turnstile> _ \<mapsto> _" 55)
  for m p where

  ConstantExpr:
  "\<lbrakk>c \<noteq> UndefVal\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ConstantExpr c) \<mapsto> c" |

  ParameterExpr:
  "\<lbrakk>valid_value s (p!i)\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ParameterExpr i s) \<mapsto> p!i" |

  ConditionalExpr:
  "\<lbrakk>[m,p] \<turnstile> ce \<mapsto> cond;
    branch = (if val_to_bool cond then te else fe);
    [m,p] \<turnstile> branch \<mapsto> v\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ConditionalExpr ce te fe) \<mapsto> v" |

  UnaryExpr:
  "\<lbrakk>[m,p] \<turnstile> xe \<mapsto> v\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (UnaryExpr op xe) \<mapsto> unary_eval op v" |

  ConvertExpr:
  "\<lbrakk>[m,p] \<turnstile> xe \<mapsto> v\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ConvertExpr op xe) \<mapsto> convert_eval op v" |

  BinaryExpr:
  "\<lbrakk>[m,p] \<turnstile> xe \<mapsto> x;
    [m,p] \<turnstile> ye \<mapsto> y\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (BinaryExpr op xe ye) \<mapsto> bin_eval op x y" |

  LeafExpr:
  "\<lbrakk>val = m nid;
    valid_value s val\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> LeafExpr nid s \<mapsto> val"

text_raw \<open>\Snip{evalRules}%
\begin{center}
@{thm[mode=Rule] evaltree.ConstantExpr [no_vars]}\\[8px]
@{thm[mode=Rule] evaltree.ParameterExpr [no_vars]}\\[8px]
@{thm[mode=Rule] evaltree.ConditionalExpr [no_vars]}\\[8px]
@{thm[mode=Rule] evaltree.UnaryExpr [no_vars]}\\[8px]
@{thm[mode=Rule] evaltree.BinaryExpr [no_vars]}\\[8px]
@{thm[mode=Rule] evaltree.LeafExpr [no_vars]}\\[8px]
\end{center}
\EndSnip\<close>

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as evalT)
  [show_steps,show_mode_inference,show_intermediate_results] 
  evaltree .



inductive
  evaltrees :: "MapState \<Rightarrow> Params \<Rightarrow> IRExpr list \<Rightarrow> Value list \<Rightarrow> bool" ("[_,_] \<turnstile> _ \<mapsto>\<^sub>L _" 55)
  for m p where

  EvalNil:
  "[m,p] \<turnstile> [] \<mapsto>\<^sub>L []" |

  EvalCons:
  "\<lbrakk>[m,p] \<turnstile> x \<mapsto> xval;
    [m,p] \<turnstile> yy \<mapsto>\<^sub>L yyval\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (x#yy) \<mapsto>\<^sub>L (xval#yyval)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as evalTs)
  evaltrees .


values "{v. evaltree new_map_state [IntVal32 5] sq_param0 v}"

(* We add all the inductive rules as unsafe intro rules. *)
declare evaltree.intros [intro]
declare evaltrees.intros [intro]

(* We derive a safe elimination (forward) reasoning rule for each case.
  Note that each pattern is as general as possible. *)
inductive_cases ConstantExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (ConstantExpr c) \<mapsto> val"
inductive_cases ParameterExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (ParameterExpr i s) \<mapsto> val"
inductive_cases ConditionalExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (ConditionalExpr c t f) \<mapsto> val"
inductive_cases UnaryExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (UnaryExpr op xe) \<mapsto> val"
inductive_cases ConvertExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (ConvertExpr op xe) \<mapsto> val"
inductive_cases BinaryExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (BinaryExpr op xe ye) \<mapsto> val"
inductive_cases LeafExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (LeafExpr nid s) \<mapsto> val"

inductive_cases EvalNilE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> [] \<mapsto>\<^sub>L vals"
inductive_cases EvalConsE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (x#yy) \<mapsto>\<^sub>L vals"

(* group these forward rules into a named set *)
lemmas EvalTreeE\<^marker>\<open>tag invisible\<close> = 
  ConstantExprE
  ParameterExprE
  ConditionalExprE
  UnaryExprE
  BinaryExprE
  ConvertExprE
  LeafExprE
  EvalNilE
  EvalConsE


subsection \<open>Data-flow Tree Refinement\<close>

text \<open>We define the induced semantic equivalence relation between expressions.
  Note that syntactic equality implies semantic equivalence, but not vice versa.
\<close>
definition equiv_exprs :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<doteq> _" 55) where
  "(e1 \<doteq> e2) = (\<forall> m p v. (([m,p] \<turnstile> e1 \<mapsto> v) \<longleftrightarrow> ([m,p] \<turnstile> e2 \<mapsto> v)))"


text \<open>We also prove that this is a total equivalence relation (@{term "equivp equiv_exprs"})
  (HOL.Equiv\_Relations), so that we can reuse standard results about equivalence relations.
\<close>
lemma "equivp equiv_exprs"
  apply (auto simp add: equivp_def equiv_exprs_def)
  by (metis equiv_exprs_def)+


text \<open>We define a refinement ordering over IRExpr and show that it is a preorder.
  Note that it is asymmetric because e2 may refer to fewer variables than e1.
\<close>
instantiation IRExpr :: preorder begin

definition
  le_expr_def [simp]: "(e1 \<le> e2) \<longleftrightarrow> (\<forall> m p v. (([m,p] \<turnstile> e1 \<mapsto> v) \<longrightarrow> ([m,p] \<turnstile> e2 \<mapsto> v)))"

definition
  lt_expr_def [simp]: "(e1 < e2) \<longleftrightarrow> (e1 \<le> e2 \<and> \<not> (e1 \<doteq> e2))"

instance proof 
  fix x y z :: IRExpr
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)" by (simp add: equiv_exprs_def; auto)
  show "x \<le> x" by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp 
qed
end

end

