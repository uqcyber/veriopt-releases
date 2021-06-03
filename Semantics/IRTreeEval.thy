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




(* ======================== START OF NEW TREE STUFF ==========================*)
subsection \<open>Data-flow Tree Representation\<close>

(* TODO: add a code lemma for this, to return max+1. *)
fun fresh_id :: "IRGraph \<Rightarrow> ID \<Rightarrow> bool" where
  "fresh_id g nid = (nid \<notin> ids g)"


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

values "{t. eg2_sq 4  \<triangleright> t}"


(* ======== TODO: Functions for re-calculating stamps ========== *)
fun stamp_unary :: "IRUnaryOp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "stamp_unary op s1 = s1"

fun stamp_binary :: "IRBinaryOp \<Rightarrow> Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "stamp_binary op s1 s2 = s1"

(* TODO! implement these to find nodes, so we reuse nodes as much as possible. *)
fun find_node :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> ID option" where
  "find_node g n = None"

fun find_node_and_stamp :: "IRGraph \<Rightarrow> (IRNode \<times> Stamp) \<Rightarrow> ID option" where
  "find_node_and_stamp g (n,s) = None"

(* Creates the appropriate IRNode for a given binary operator. *)
fun bin_node :: "IRBinaryOp \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode" where
  "bin_node BinAdd x y = AddNode x y" |
  "bin_node BinMul x y = MulNode x y" |
  "bin_node BinSub x y = SubNode x y"


(* Second version of tree insertion into graph:

      g \<triangleleft> expr \<leadsto> (g',nid) re-inserts expr into g and returns the new root nid.

   This means that we can try to re-use existing nodes by finding node IDs bottom-up.
*)
inductive
  unrep :: "IRGraph \<Rightarrow> IRExpr \<Rightarrow> (IRGraph \<times> ID) \<Rightarrow> bool" ("_ \<triangleleft> _ \<leadsto> _" 55)
  for g where

  ConstantNodeSame:
  "\<lbrakk>find_node_and_stamp g (ConstantNode c, constant_as_stamp c) = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ConstantExpr c) \<leadsto> (g, nid)" |

  ConstantNodeNew:
  "\<lbrakk>find_node_and_stamp g (ConstantNode c, constant_as_stamp c) = None;
    fresh_id g nid;
    g' = add_node nid (ConstantNode c, constant_as_stamp c) g \<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ConstantExpr c) \<leadsto> (g', nid)" |


  ParameterNodeSame:
  "\<lbrakk>find_node_and_stamp g (ParameterNode i, s) = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ParameterExpr i s) \<leadsto> (g, nid)" |

  ParameterNodeNew:
  "\<lbrakk>find_node_and_stamp g (ParameterNode i, s) = None;
    fresh_id g nid;
    g' = add_node nid (ParameterNode i, s) g\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (ParameterExpr i s) \<leadsto> (g', nid)" |


  AbsNodeSame:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    find_node_and_stamp g2 (AbsNode x, stamp g2 x) = Some nid\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (UnaryExpr UnaryAbs xe) \<leadsto> (g2, nid)" |

  AbsNodeNew:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    find_node_and_stamp g2 (AbsNode x, stamp g2 x) = None;
    fresh_id g2 nid;
    s' = stamp_unary UnaryAbs (stamp g2 x);
    g' = add_node nid (AbsNode nidx, s') g2\<rbrakk>
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
    fresh_id g3 nid;
    g' = add_node nid (bin_node op x y, s') g3\<rbrakk>
    \<Longrightarrow> g \<triangleleft> (BinaryExpr op xe ye) \<leadsto> (g', nid)" |


  AllLeafNodes:
  "stamp g nid = s
    \<Longrightarrow> g \<triangleleft> (LeafExpr nid s) \<leadsto> (g, nid)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as unrepE) unrep .

values "{t. eg2_sq 4  \<triangleright> t}"


end

