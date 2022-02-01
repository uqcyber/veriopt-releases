section \<open>Data-flow Semantics\<close>

theory IRTreeEval
  imports
    Graph.Values
    Graph.Stamp
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

(* ======== TODO: Functions for re-calculating stamps ========== *)
fun stamp_unary :: "IRUnaryOp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "stamp_unary op (IntegerStamp b lo hi) = unrestricted_stamp (IntegerStamp b lo hi)" |
  (* for now... *)
  "stamp_unary op _ = IllegalStamp"

definition fixed_32 :: "IRBinaryOp set" where
  "fixed_32 = {BinIntegerEquals, BinIntegerLessThan, BinIntegerBelow}"

fun stamp_binary :: "IRBinaryOp \<Rightarrow> Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "stamp_binary op (IntegerStamp b1 lo1 hi1) (IntegerStamp b2 lo2 hi2) =
    (case op \<in> fixed_32 of True \<Rightarrow> unrestricted_stamp (IntegerStamp 32 lo1 hi1) |
    False \<Rightarrow>
    (if (b1 = b2) then unrestricted_stamp (IntegerStamp b1 lo1 hi1) else IllegalStamp))" |
  (* for now... *)
  "stamp_binary op _ _ = IllegalStamp"

fun stamp_expr :: "IRExpr \<Rightarrow> Stamp" where
  "stamp_expr (UnaryExpr op x) = stamp_unary op (stamp_expr x)" |
  "stamp_expr (BinaryExpr bop x y) = stamp_binary bop (stamp_expr x) (stamp_expr y)" |
  "stamp_expr (ConstantExpr val) = constantAsStamp val" |
  "stamp_expr (LeafExpr i s) = s" |
  "stamp_expr (ParameterExpr i s) = s" |
  "stamp_expr (ConditionalExpr c t f) = meet (stamp_expr t) (stamp_expr f)"

export_code stamp_unary stamp_binary stamp_expr

subsection \<open>Data-flow Tree Evaluation\<close>

fun unary_eval :: "IRUnaryOp \<Rightarrow> Value \<Rightarrow> Value" where
  "unary_eval UnaryAbs v = intval_abs v" |
  "unary_eval UnaryNeg v = intval_negate v" |
  "unary_eval UnaryNot v = intval_not v" |
  "unary_eval UnaryLogicNegation v = intval_logic_negation v" |
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
  "\<lbrakk>valid_value c (constantAsStamp c)\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ConstantExpr c) \<mapsto> c" |

  ParameterExpr:
  "\<lbrakk>i < length p; valid_value (p!i) s\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ParameterExpr i s) \<mapsto> p!i" |

  (* We need to add this to prove certain optimizations
     but it also requires more work to show monotonicity of refinement.
  compatible (stamp_expr te) (stamp_expr fe);*)
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
    valid_value val s\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> LeafExpr n s \<mapsto> val"

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

definition sq_param0 :: IRExpr where
  "sq_param0 = BinaryExpr BinMul 
    (ParameterExpr 0 (IntegerStamp 32 (- 2147483648) 2147483647))
    (ParameterExpr 0 (IntegerStamp 32 (- 2147483648) 2147483647))"

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
inductive_cases BinaryExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (BinaryExpr op xe ye) \<mapsto> val"
inductive_cases LeafExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (LeafExpr n s) \<mapsto> val"
inductive_cases ConstantVarE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (ConstantVar x) \<mapsto> val"
inductive_cases VariableExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (VariableExpr x s) \<mapsto> val"
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
  LeafExprE
  ConstantVarE
  VariableExprE
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

notation less_eq (infix "\<sqsubseteq>" 65)

definition
  le_expr_def [simp]:
    "(e\<^sub>2 \<le> e\<^sub>1) \<longleftrightarrow> (\<forall> m p v. (([m,p] \<turnstile> e\<^sub>1 \<mapsto> v) \<longrightarrow> ([m,p] \<turnstile> e\<^sub>2 \<mapsto> v)))"

definition
  lt_expr_def [simp]:
    "(e\<^sub>1 < e\<^sub>2) \<longleftrightarrow> (e\<^sub>1 \<le> e\<^sub>2 \<and> \<not> (e\<^sub>1 \<doteq> e\<^sub>2))"

instance proof 
  fix x y z :: IRExpr
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)" by (simp add: equiv_exprs_def; auto)
  show "x \<le> x" by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp 
qed

end

abbreviation (output) Refines :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" (infix "\<sqsupseteq>" 64)
  where "e\<^sub>1 \<sqsupseteq> e\<^sub>2 \<equiv> (e\<^sub>2 \<le> e\<^sub>1)"

end
