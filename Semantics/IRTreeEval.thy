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

fun val_to_bool :: "Value \<Rightarrow> bool" where
  "val_to_bool (IntVal32 val) = (if val = 0 then False else True)" |
  "val_to_bool v = False"

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal32  1)" |
  "bool_to_val False = (IntVal32 0)"




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
  "bin_eval BinIntegerEquals v1 v2 = intval_equals v1 v2" |
  "bin_eval BinIntegerLessThan v1 v2 = intval_less_than v1 v2" |
  "bin_eval BinIntegerBelow v1 v2 = intval_below v1 v2"
(*  "bin_eval op v1 v2 = UndefVal" *)

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
    [m,p] \<turnstile> branch \<mapsto> v\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ConditionalExpr ce te fe) \<mapsto> v" |

  UnaryExpr:
  "\<lbrakk>[m,p] \<turnstile> xe \<mapsto> v\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (UnaryExpr op xe) \<mapsto> unary_eval op v" |

  BinaryExpr:
  "\<lbrakk>[m,p] \<turnstile> xe \<mapsto> x;
    [m,p] \<turnstile> ye \<mapsto> y\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (BinaryExpr op xe ye) \<mapsto> bin_eval op x y" |

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



(*
typedef Substitution = "{\<sigma> :: string \<Rightarrow> IRExpr option . finite (dom \<sigma>)}"
proof -
  have "finite(dom(Map.empty)) \<and> ran Map.empty = {}" by auto
  then show ?thesis
    by fastforce
qed
*)

datatype SubValue = SubExpr(s_expr: IRExpr) | SubConst(s_val: Value) | SubNone

type_synonym Substitution = "string \<Rightarrow> SubValue"

fun substitute :: "Substitution \<Rightarrow> IRExpr \<Rightarrow> IRExpr" (infix "@@" 60) where
  "substitute \<sigma> (UnaryExpr op e) = UnaryExpr op (\<sigma> @@ e)" |
  "substitute \<sigma> (BinaryExpr op e1 e2) = BinaryExpr op (\<sigma> @@ e1) (\<sigma> @@ e2)" |
  "substitute \<sigma> (ConditionalExpr b e1 e2) = ConditionalExpr (\<sigma> @@ b) (\<sigma> @@ e1) (\<sigma> @@ e2)" |
  "substitute \<sigma> (ParameterExpr i s) = ParameterExpr i s" |
  "substitute \<sigma> (LeafExpr n s) = LeafExpr n s" |
  "substitute \<sigma> (ConstantExpr v) = ConstantExpr v" |
  "substitute \<sigma> (ConstantVar x) = 
      (case \<sigma> x of SubConst v \<Rightarrow> ConstantExpr v | _ \<Rightarrow> ConstantVar x)" |
  "substitute \<sigma> (VariableExpr x s) = 
      (case \<sigma> x of SubNone \<Rightarrow> (VariableExpr x s) | SubExpr y \<Rightarrow> y)"

fun union :: "Substitution \<Rightarrow> Substitution \<Rightarrow> Substitution" where
  "union \<sigma>1 \<sigma>2 = (\<lambda>name. if \<sigma>1 name = SubNone then \<sigma>2 name else \<sigma>1 name)"

fun compatible :: "Substitution \<Rightarrow> Substitution \<Rightarrow> bool" where
  "compatible \<sigma>1 \<sigma>2 = (\<forall>x. \<sigma>1 x \<noteq> SubNone \<and> \<sigma>2 x \<noteq> SubNone \<longrightarrow> \<sigma>1 x = \<sigma>2 x)"

fun substitution_union :: "Substitution option \<Rightarrow> Substitution option \<Rightarrow> Substitution option" (infix "\<uplus>" 70) where
  "substitution_union s1 s2 = 
      (case s1 of
       None \<Rightarrow> None |
       Some \<sigma>1 \<Rightarrow> 
           (case s2 of
            None \<Rightarrow> None |
            Some \<sigma>2 \<Rightarrow> (if compatible \<sigma>1 \<sigma>2 then Some (union \<sigma>1 \<sigma>2) else None)
           )
      )"

definition EmptySubstitution :: "Substitution" where 
  "EmptySubstitution = (\<lambda>x. SubNone)"

fun match :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> Substitution option" where
  "match (UnaryExpr op e) (UnaryExpr op' e') = 
      (if op = op' then match e e' else None)" |
  "match (BinaryExpr op e1 e2) (BinaryExpr op' e1' e2') = 
      (if op = op' then (match e1 e1') \<uplus> (match e2 e2') else None)" |
  "match (ConditionalExpr b e1 e2) (ConditionalExpr b' e1' e2') = 
      (match b b') \<uplus> ((match e1 e1') \<uplus> (match e2 e2'))" |
  "match (ParameterExpr i1 s1) (ParameterExpr i2 s2) = 
      (if i1 = i2 \<and> s1 = s2 then Some EmptySubstitution else None)" |
  "match (LeafExpr n1 s1) (LeafExpr n2 s2) = 
      (if n1 = n2 \<and> s1 = s2 then Some EmptySubstitution else None)" |
  "match (ConstantExpr v1) (ConstantExpr v2) = 
      (if v1 = v2 then Some EmptySubstitution else None)" |
  "match (ConstantVar name) (ConstantExpr v) = 
      Some(\<lambda>x. if x = name then SubExpr(ConstantExpr v) else SubNone)" |
  "match (VariableExpr x s) e = Some (\<lambda> n. if n = x then SubExpr e else SubNone)" |
  "match _ _ = None"

fun vars :: "IRExpr \<Rightarrow> string set" where
  "vars (UnaryExpr op e) = vars e" |
  "vars (BinaryExpr op e1 e2) = vars e1 \<union> vars e2" |
  "vars (ConditionalExpr b e1 e2) = vars b \<union> vars e1 \<union> vars e2" |
  "vars (ParameterExpr i s) = {}" |
  "vars (LeafExpr n s) = {}" |
  "vars (ConstantExpr v) = {}" |
  "vars (ConstantVar x) = {x}" |
  "vars (VariableExpr x s) = {x}"

typedef Rewrite = "{ (e1,e2) :: IRExpr \<times> IRExpr | e1 e2 . vars e2 \<subseteq> vars e1 }" 
proof -
  have "\<exists>v. vars (ConstantExpr v) \<subseteq> vars (ConstantExpr v)" by simp
  then show ?thesis
    by blast
qed

fun rewrite :: "Rewrite \<Rightarrow> IRExpr \<Rightarrow> IRExpr option" where
  "rewrite r e = (let (e1,e2) = Rep_Rewrite r in 
                   (case match e1 e of
                    Some \<sigma> \<Rightarrow> Some (\<sigma> @@ e2) |
                    None \<Rightarrow> None))"


end