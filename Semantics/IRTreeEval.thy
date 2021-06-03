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

datatype (discs_sels) IRExpr =
  AbsExpr (ir_value: IRExpr) 
  | AddExpr (ir_x: IRExpr) (ir_y: IRExpr) 
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
  | MulExpr (ir_x: IRExpr) (ir_y: IRExpr) 
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
  | SubExpr (ir_x: IRExpr) (ir_y: IRExpr) 
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
    \<Longrightarrow> g n \<triangleright> (AbsExpr xe)" |

  AddNode:
  "\<lbrakk>kind g n = AddNode x y;
    g x \<triangleright> xe;
    g x \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (AddExpr xe ye)" |

  MulNode:
  "\<lbrakk>kind g n = MulNode x y;
    g x \<triangleright> xe;
    g x \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (MulExpr xe ye)" |

  SubNode:
  "\<lbrakk>kind g n = SubNode x y;
    g x \<triangleright> xe;
    g x \<triangleright> ye\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (SubExpr xe ye)" |

  LoadFieldNode: (* TODO others *)
  "\<lbrakk>kind g n = LoadFieldNode nid f obj nxt;
    stamp g n = s\<rbrakk>
    \<Longrightarrow> g n \<triangleright> (LeafExpr nid s)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as exprE) rep .

values "{t. eg2_sq 4  \<triangleright> t}"


(* ======== TODO: Functions for re-calculating stamps ========== *)
fun stamp_abs :: "Stamp \<Rightarrow> Stamp" where "stamp_abs s = s"
fun stamp_add :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where "stamp_add x y = x"
fun stamp_sub :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where "stamp_sub x y = x"
fun stamp_mul :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where "stamp_mul x y = x"


(* First version of tree insertion into graph:

      g n \<triangleleft> expr \<leadsto> g' re-inserts expr into g, rooted at node ID n.

   This means that we recurse into the expression tree allocating node IDs top-down,
   so every leaf gets given a new ID.

   An alternative (better?) approach would be to decide the node IDs bottom-up,
   so that leaf IDs can be re-used, and intermediate nodes can also be re-used
   if they have not changed. 
 *)
inductive
  unrep :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRExpr \<Rightarrow> IRGraph \<Rightarrow> bool" ("_ _ \<triangleleft> _ \<leadsto> _" 55)
  for g where

  ConstantNode:
  "\<lbrakk>constant_as_stamp c = cstamp;
    g' = add_node n (ConstantNode c, cstamp) g \<rbrakk>
    \<Longrightarrow> g n \<triangleleft> (ConstantExpr c) \<leadsto> g'" |

  ParameterNode:
  "\<lbrakk>g' = add_node n (ParameterNode i, s) g\<rbrakk>
    \<Longrightarrow> g n \<triangleleft> (ParameterExpr i s) \<leadsto> g'" |

  AbsNode:
  "\<lbrakk>fresh_id g nid2;
    g nid2 \<triangleleft> xe \<leadsto> g2;
    s2 = stamp g2 nid2;
    s' = stamp_abs s2; 
    g' = add_node n (AbsNode nid2, s') g2\<rbrakk>
    \<Longrightarrow> g n \<triangleleft> (AbsExpr xe) \<leadsto> g'" |

  AddNode:
  "\<lbrakk>fresh_id g nidx;
    g nidx \<triangleleft> xe \<leadsto> gx;
    sx = stamp gx nidx;
    fresh_id gx nidy;
    g nidy \<triangleleft> ye \<leadsto> gy;
    sy = stamp gy nidy;
    s' = stamp_add sx sy; 
    g' = add_node n (AddNode nidx nidy, s') gy\<rbrakk>
    \<Longrightarrow> g n \<triangleleft> (AddExpr xe ye) \<leadsto> g'" |

  MulNode:
  "\<lbrakk>fresh_id g nidx;
    g nidx \<triangleleft> xe \<leadsto> gx;
    sx = stamp gx nidx;
    fresh_id gx nidy;
    g nidy \<triangleleft> ye \<leadsto> gy;
    sy = stamp gy nidy;
    s' = stamp_sub sx sy; 
    g' = add_node n (MulNode nidx nidy, s') gy\<rbrakk>
    \<Longrightarrow> g n \<triangleleft> (MulExpr xe ye) \<leadsto> g'" |

  SubNode:
  "\<lbrakk>fresh_id g nidx;
    g nidx \<triangleleft> xe \<leadsto> gx;
    sx = stamp gx nidx;
    fresh_id gx nidy;
    g nidy \<triangleleft> ye \<leadsto> gy;
    sy = stamp gy nidy;
    s' = stamp_mul sx sy; 
    g' = add_node n (SubNode nidx nidy, s') gy\<rbrakk>
    \<Longrightarrow> g n \<triangleleft> (SubExpr xe ye) \<leadsto> g'" |

  AllLeafNodes: (* TODO check that kind g nid is indeed a leaf node?
    e.g.  kind g nid = LoadFieldNode nid f obj nxt;
 *)
  "\<lbrakk>kind g nid = node;
    stamp g nid = s;
    fresh_id g nid2;
    g' = add_node nid2 (node, s) g\<rbrakk>
    \<Longrightarrow> g n \<triangleleft> (LeafExpr nid s) \<leadsto> g'"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as unrepE) unrep .

values "{t. eg2_sq 4  \<triangleright> t}"


end

