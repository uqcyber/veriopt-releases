section \<open>Data-flow Semantics\<close>

theory IRTreeEval
  imports
    Graph.Values
    Graph.Stamp
    "HOL-Library.Word"
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

type_synonym ID = nat
type_synonym MapState = "ID \<Rightarrow> Value"
type_synonym Params = "Value list"

definition new_map_state :: "MapState" where
  "new_map_state = (\<lambda>x. UndefVal)"


(* ======================== START OF NEW TREE STUFF ==========================*)
subsection \<open>Data-flow Tree Representation\<close>

datatype IRUnaryOp =
    UnaryAbs
  | UnaryNeg
  | UnaryNot
  | UnaryLogicNegation
  | UnaryNarrow (ir_inputBits: nat) (ir_resultBits: nat)
  | UnarySignExtend (ir_inputBits: nat) (ir_resultBits: nat)
  | UnaryZeroExtend (ir_inputBits: nat) (ir_resultBits: nat)

datatype IRBinaryOp =
    BinAdd
  | BinMul
  | BinSub
  | BinAnd
  | BinOr
  | BinXor
  | BinLeftShift
  | BinRightShift
  | BinURightShift
  | BinIntegerEquals
  | BinIntegerLessThan
  | BinIntegerBelow

datatype (discs_sels) IRExpr =
    UnaryExpr (ir_uop: IRUnaryOp) (ir_value: IRExpr)
  | BinaryExpr (ir_op: IRBinaryOp) (ir_x: IRExpr) (ir_y: IRExpr)
  | ConditionalExpr (ir_condition: IRExpr) (ir_trueValue: IRExpr) (ir_falseValue: IRExpr)
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
  | ConstantExpr (ir_const: Value) (* Ground constant *)
  | ConstantVar (ir_name: string)  (* Pattern variable for constant *)
  | VariableExpr (ir_name: string) (ir_stamp: Stamp) (* Pattern variable for expression *)

fun is_ground :: "IRExpr \<Rightarrow> bool" where
  "is_ground (UnaryExpr op e) = is_ground e" |
  "is_ground (BinaryExpr op e1 e2) = (is_ground e1 \<and> is_ground e2)" |
  "is_ground (ConditionalExpr b e1 e2) = (is_ground b \<and> is_ground e1 \<and> is_ground e2)" |
  "is_ground (ParameterExpr i s) = True" |
  "is_ground (LeafExpr n s) = True" |
  "is_ground (ConstantExpr v) = True" |
  "is_ground (ConstantVar name) = False" |
  "is_ground (VariableExpr name s) = False"

typedef GroundExpr = "{ e :: IRExpr . is_ground e }"
  using is_ground.simps(6) by blast

subsection \<open>Data-flow Tree Evaluation\<close>

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
  "bin_eval BinLeftShift v1 v2 = intval_left_shift v1 v2" |
  "bin_eval BinRightShift v1 v2 = intval_right_shift v1 v2" |
  "bin_eval BinURightShift v1 v2 = intval_uright_shift v1 v2" |
  "bin_eval BinIntegerEquals v1 v2 = intval_equals v1 v2" |
  "bin_eval BinIntegerLessThan v1 v2 = intval_less_than v1 v2" |
  "bin_eval BinIntegerBelow v1 v2 = intval_below v1 v2"
(*  "bin_eval op v1 v2 = UndefVal" *)

inductive not_undef_or_fail :: "Value \<Rightarrow> Value \<Rightarrow> bool" where
  "\<lbrakk>value \<noteq> UndefVal\<rbrakk> \<Longrightarrow> not_undef_or_fail value value"

notation (latex output) (* we can pretend intval_* are partial functions *)
  not_undef_or_fail ("_ = _")

inductive
  evaltree :: "MapState \<Rightarrow> Params \<Rightarrow> IRExpr \<Rightarrow> Value \<Rightarrow> bool" ("[_,_] \<turnstile> _ \<mapsto> _" 55)
  for m p where

  ConstantExpr:
  "\<lbrakk>valid_value (constantAsStamp c) c\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ConstantExpr c) \<mapsto> c" |

  ParameterExpr:
  "\<lbrakk>i < length p; valid_value s (p!i)\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ParameterExpr i s) \<mapsto> p!i" |

  ConditionalExpr:
  "\<lbrakk>[m,p] \<turnstile> ce \<mapsto> cond;
    branch = (if val_to_bool cond then te else fe);
    [m,p] \<turnstile> branch \<mapsto> v;
    v \<noteq> UndefVal\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ConditionalExpr ce te fe) \<mapsto> v" |

  UnaryExpr:
  "\<lbrakk>[m,p] \<turnstile> xe \<mapsto> v;
    result = (unary_eval op v);
    result \<noteq> UndefVal\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (UnaryExpr op xe) \<mapsto> result" |

  BinaryExpr:
  "\<lbrakk>[m,p] \<turnstile> xe \<mapsto> x;
    [m,p] \<turnstile> ye \<mapsto> y;
    result = (bin_eval op x y);
    result \<noteq> UndefVal\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (BinaryExpr op xe ye) \<mapsto> result" |

  LeafExpr:
  "\<lbrakk>val = m n;
    valid_value s val\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> LeafExpr n s \<mapsto> val"

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
  le_expr_def [simp]: "(e2 \<le> e1) \<longleftrightarrow> (\<forall> m p v. (([m,p] \<turnstile> e1 \<mapsto> v) \<longrightarrow> ([m,p] \<turnstile> e2 \<mapsto> v)))"

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
