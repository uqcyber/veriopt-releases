section \<open>Conditional Elimination Phase\<close>

theory ConditionalElimination
  imports
    Semantics.IRTreeEvalThms
    Proofs.Rewrites
    Proofs.Bisimulation
begin

subsection \<open>Individual Elimination Rules\<close>

text \<open>The set of rules used for determining whether a condition @{term q1} implies
    another condition @{term q2} or its negation.
    These rules are used for conditional elimination.\<close>

inductive impliesx :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<Rrightarrow> _") and 
      impliesnot :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<Rrightarrow>\<not> _") where
  q_imp_q: 
  "q \<Rrightarrow> q" |
  eq_impliesnot_less:
  "(BinaryExpr BinIntegerEquals x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerLessThan x y)" |
  eq_impliesnot_less_rev:
  "(BinaryExpr BinIntegerEquals x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerLessThan y x)" |
  less_impliesnot_rev_less:
  "(BinaryExpr BinIntegerLessThan x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerLessThan y x)" |
  less_impliesnot_eq:
  "(BinaryExpr BinIntegerLessThan x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerEquals x y)" |
  less_impliesnot_eq_rev:
  "(BinaryExpr BinIntegerLessThan x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerEquals y x)" |
  negate_true:
  "\<lbrakk>x \<Rrightarrow>\<not> y\<rbrakk> \<Longrightarrow> x \<Rrightarrow> (UnaryExpr UnaryLogicNegation y)" |
  negate_false:
  "\<lbrakk>x \<Rrightarrow> y\<rbrakk> \<Longrightarrow> x \<Rrightarrow>\<not> (UnaryExpr UnaryLogicNegation y)"

text \<open>The relation @{term "q1 \<Rrightarrow> q2"} indicates that the implication @{term "q1 \<longrightarrow> q2"}
    is known true (i.e. universally valid), 
    and the relation @{term "q1 \<Rrightarrow>\<not> q2"} indicates that the implication @{term "q1 \<longrightarrow> q2"}
    is known false (i.e. @{term "q1 \<longrightarrow>\<not> q2"} is universally valid.
    If neither @{term "q1 \<Rrightarrow> q2"} nor @{term "q1 \<Rrightarrow>\<not> q2"} then the status is unknown.
    Only the known true and known false cases can be used for conditional elimination.\<close>

fun implies_valid :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" (infix "\<Zinj>" 50) where
  "implies_valid q1 q2 = 
    (\<forall>m p v1 v2. ([m, p] \<turnstile> q1 \<mapsto> v1) \<and> ([m,p] \<turnstile> q2 \<mapsto> v2) \<longrightarrow> 
            (val_to_bool v1 \<longrightarrow> val_to_bool v2))"

fun impliesnot_valid :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" (infix "\<Zpinj>" 50) where
  "impliesnot_valid q1 q2 = 
    (\<forall>m p v1 v2. ([m, p] \<turnstile> q1 \<mapsto> v1) \<and> ([m,p] \<turnstile> q2 \<mapsto> v2) \<longrightarrow> 
            (val_to_bool v1 \<longrightarrow> \<not>val_to_bool v2))"

text \<open>The relation @{term "q1 \<Zinj> q2"} means @{term "q1 \<longrightarrow> q2"} is universally valid, 
      and the relation @{term "q1 \<Zpinj> q2"} means @{term "q1 \<longrightarrow> \<not>q2"} is universally valid.\<close>

lemma eq_impliesnot_less_helper:
  "v1 = v2 \<longrightarrow> \<not>(int_signed_value b v1 < int_signed_value b v2)" 
  by force 

lemma eq_impliesnot_less_val:
  "val_to_bool(intval_equals v1 v2) \<longrightarrow> \<not>val_to_bool(intval_less_than v1 v2)"
  using eq_impliesnot_less_helper bool_to_val.simps bool_to_val_bin.simps intval_equals.simps
    intval_less_than.elims val_to_bool.elims val_to_bool.simps
  by (smt (verit))

lemma eq_impliesnot_less_rev_val:
  "val_to_bool(intval_equals v1 v2) \<longrightarrow> \<not>val_to_bool(intval_less_than v2 v1)"
proof -
  have a: "intval_equals v1 v2 = intval_equals v2 v1"
    using bool_to_val_bin.simps intval_equals.simps intval_equals.elims
    by (smt (verit))
  show ?thesis using a eq_impliesnot_less_val by presburger 
qed

lemma less_impliesnot_rev_less_val:
  "val_to_bool(intval_less_than v1 v2) \<longrightarrow> \<not>val_to_bool(intval_less_than v2 v1)"
  by (smt (verit, del_insts) Value.exhaust Value.inject(1) bool_to_val.simps(2)
      bool_to_val_bin.simps intval_less_than.simps(1) intval_less_than.simps(5)
      intval_less_than.simps(6) intval_less_than.simps(7) val_to_bool.elims(2)) 

lemma less_impliesnot_eq_val:
  "val_to_bool(intval_less_than v1 v2) \<longrightarrow> \<not>val_to_bool(intval_equals v1 v2)"
  using eq_impliesnot_less_val by blast 

lemma logic_negate_type:
  assumes "[m, p] \<turnstile> UnaryExpr UnaryLogicNegation x \<mapsto> v"
  shows "\<exists>b v2. [m, p] \<turnstile> x \<mapsto> IntVal b v2"
  using assms
  by (metis UnaryExprE intval_logic_negation.elims unary_eval.simps(4))

lemma intval_logic_negation_inverse:
  assumes "b > 0"
  assumes "x = IntVal b v"
  shows "val_to_bool (intval_logic_negation x) \<longleftrightarrow> \<not>(val_to_bool x)"
  using assms by (cases x; auto simp: logic_negate_def) 

lemma logic_negation_relation_tree:
  assumes "[m, p] \<turnstile> y \<mapsto> val"
  assumes "[m, p] \<turnstile> UnaryExpr UnaryLogicNegation y \<mapsto> invval"
  shows "val_to_bool val \<longleftrightarrow> \<not>(val_to_bool invval)"
  using assms using intval_logic_negation_inverse
  by (metis UnaryExprE evalDet eval_bits_1_64 logic_negate_type unary_eval.simps(4))

text \<open>The following theorem shows that the known true/false rules are valid.\<close>

theorem implies_impliesnot_valid:
  shows "((q1 \<Rrightarrow> q2) \<longrightarrow> (q1 \<Zinj> q2)) \<and>
         ((q1 \<Rrightarrow>\<not> q2) \<longrightarrow> (q1 \<Zpinj> q2))"
          (is "(?imp \<longrightarrow> ?val) \<and> (?notimp \<longrightarrow> ?notval)")
proof (induct q1 q2  rule: impliesx_impliesnot.induct)
  case (q_imp_q q)
  then show ?case 
    using evalDet by fastforce
next
  case (eq_impliesnot_less x y)
  then show ?case apply auto using eq_impliesnot_less_val evalDet by blast
next
  case (eq_impliesnot_less_rev x y)
  then show ?case apply auto using eq_impliesnot_less_rev_val evalDet by blast
next
  case (less_impliesnot_rev_less x y)
  then show ?case apply auto using less_impliesnot_rev_less_val evalDet by blast
next
  case (less_impliesnot_eq x y)
  then show ?case apply auto using less_impliesnot_eq_val evalDet by blast
next
  case (less_impliesnot_eq_rev x y)
  then show ?case apply auto using eq_impliesnot_less_rev_val evalDet by metis 
next
  case (negate_true x y)
  then show ?case apply auto
    by (metis logic_negation_relation_tree unary_eval.simps(4) unfold_unary)
next
  case (negate_false x y)
  then show ?case apply auto 
    by (metis UnaryExpr logic_negation_relation_tree unary_eval.simps(4)) 
qed





text \<open>
We introduce a type @{term "TriState"} (as in the GraalVM compiler) to represent when static
analysis can tell us information about the value of a Boolean expression.
If @{term "Unknown"} then no information can be inferred and if
@{term "KnownTrue"}/@{term "KnownFalse"} one can infer the expression is always true/false.
\<close>
datatype TriState = Unknown | KnownTrue | KnownFalse

text \<open>
The implies relation corresponds to the LogicNode.implies
method from the compiler which attempts to infer when one
logic nodes value can be inferred from a known logic node.
\<close>
inductive implies :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> TriState \<Rightarrow> bool"
  ("_ \<turnstile> _ & _ \<hookrightarrow> _") for g where
  eq_imp_less:
  "g \<turnstile> (IntegerEqualsNode x y) & (IntegerLessThanNode x y) \<hookrightarrow> KnownFalse" |
  eq_imp_less_rev:
  "g \<turnstile> (IntegerEqualsNode x y) & (IntegerLessThanNode y x) \<hookrightarrow> KnownFalse" |
  less_imp_rev_less:
  "g \<turnstile> (IntegerLessThanNode x y) & (IntegerLessThanNode y x) \<hookrightarrow> KnownFalse" |
  less_imp_not_eq:
  "g \<turnstile> (IntegerLessThanNode x y) & (IntegerEqualsNode x y) \<hookrightarrow> KnownFalse" |
  less_imp_not_eq_rev:
  "g \<turnstile> (IntegerLessThanNode x y) & (IntegerEqualsNode y x) \<hookrightarrow> KnownFalse" |

  x_imp_x:
  "g \<turnstile> x & x \<hookrightarrow> KnownTrue" |

  negate_false:
  "\<lbrakk>g \<turnstile> x & (kind g y) \<hookrightarrow> KnownTrue\<rbrakk> \<Longrightarrow> g \<turnstile> x & (LogicNegationNode y) \<hookrightarrow> KnownFalse" |
  negate_true:
  "\<lbrakk>g \<turnstile> x & (kind g y) \<hookrightarrow> KnownFalse\<rbrakk> \<Longrightarrow> g \<turnstile> x & (LogicNegationNode y) \<hookrightarrow> KnownTrue"



text \<open>
Proofs that the implies relation is correct with respect to the 
existing evaluation semantics.
\<close>

lemma logic_negation_relation:
  assumes "[g, m, p] \<turnstile> y \<mapsto> val"
  assumes "kind g neg = LogicNegationNode y"
  assumes "[g, m, p] \<turnstile> neg \<mapsto> invval"
  assumes "invval \<noteq> UndefVal"
  shows "val_to_bool val \<longleftrightarrow> \<not>(val_to_bool invval)"
  using assms
  by (metis LogicNegationNode encodeeval_def logic_negation_relation_tree repDet)


text \<open>
The following relation corresponds to the UnaryOpLogicNode.tryFold
and BinaryOpLogicNode.tryFold methods and their associated concrete implementations.

The relation determines if a logic operation can be shown true or false
through the stamp typing information.
\<close>
inductive tryFold :: "IRNode \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> bool \<Rightarrow> bool"
  where
  "\<lbrakk>alwaysDistinct (stamps x) (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerEqualsNode x y) stamps False" |
  "\<lbrakk>neverDistinct (stamps x) (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerEqualsNode x y) stamps True" |
  "\<lbrakk>is_IntegerStamp (stamps x);
    is_IntegerStamp (stamps y);
    stpi_upper (stamps x) < stpi_lower (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerLessThanNode x y) stamps True" |
  "\<lbrakk>is_IntegerStamp (stamps x);
    is_IntegerStamp (stamps y);
    stpi_lower (stamps x) \<ge> stpi_upper (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerLessThanNode x y) stamps False"


text \<open>
Proofs that show that when the stamp lookup function is well-formed,
the tryFold relation correctly predicts the output value with respect to
our evaluation semantics.
\<close>
lemma
  assumes "kind g nid = IntegerEqualsNode x y"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "([g, m, p] \<turnstile> x \<mapsto> xval) \<and> ([g, m, p] \<turnstile> y \<mapsto> yval)"
  shows "val_to_bool (intval_equals xval yval) \<longleftrightarrow> v = IntVal 32 1"
proof -
  have "v = intval_equals xval yval"
    using assms(1, 2, 3) BinaryExprE IntegerEqualsNode bin_eval.simps(7)
    by (smt (verit) bin_eval.simps(11) encodeeval_def evalDet repDet)
  then show ?thesis using intval_equals.simps val_to_bool.simps
    by (smt (verit) bool_to_val.simps(1) bool_to_val.simps(2) bool_to_val_bin.simps 
        intval_equals.elims one_neq_zero)
qed


inductive_cases StepE:
  "g, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m',h)"

text \<open>
Perform conditional elimination rewrites on the graph for a particular node.

In order to determine conditional eliminations appropriately the rule needs two
data structures produced by static analysis.
The first parameter is the set of IRNodes that we know result in a true value
when evaluated.
The second parameter is a mapping from node identifiers to the flow-sensitive stamp.

The relation transforms the third parameter to the fifth parameter for a node identifier
which represents the fourth parameter.
\<close>
inductive ConditionalEliminationStep :: 
  "IRExpr set \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> IRGraph \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  impliesTrue:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    g \<turnstile> cid \<simeq> cond;
    \<exists> ce \<in> conds . (ce \<Rrightarrow> cond);
    g' = constantCondition True ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'" |

  impliesFalse:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    g \<turnstile> cid \<simeq> cond;
    \<exists> ce \<in> conds . (ce \<Rrightarrow>\<not> cond);
    g' = constantCondition False ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'" |

  tryFoldTrue:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    tryFold (kind g cid) stamps True;
    g' = constantCondition True ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'" |

  tryFoldFalse:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    tryFold (kind g cid) stamps False;
    g' = constantCondition False ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'"


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationStep .

thm ConditionalEliminationStep.equation

subsection \<open>Control-flow Graph Traversal\<close>

type_synonym Seen = "ID set"
type_synonym Condition = "IRExpr"
type_synonym Conditions = "Condition list"
type_synonym StampFlow = "(ID \<Rightarrow> Stamp) list"

text \<open>
nextEdge helps determine which node to traverse next by returning the first successor
edge that isn't in the set of already visited nodes.
If there is not an appropriate successor, None is returned instead.
\<close>
fun nextEdge :: "Seen \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> ID option" where
  "nextEdge seen nid g = 
    (let nids = (filter (\<lambda>nid'. nid' \<notin> seen) (successors_of (kind g nid))) in 
     (if length nids > 0 then Some (hd nids) else None))"

text \<open>
pred determines which node, if any, acts as the predecessor of another.

Merge nodes represent a special case where-in the predecessor exists as
an input edge of the merge node, to simplify the traversal we treat only
the first input end node as the predecessor, ignoring that multiple nodes
may act as a successor.

For all other nodes, the predecessor is the first element of the predecessors set.
Note that in a well-formed graph there should only be one element in the predecessor set.\<close>
fun pred :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID option" where
  "pred g nid = (case kind g nid of
    (MergeNode ends _ _) \<Rightarrow> Some (hd ends) |
    _ \<Rightarrow> 
      (if IRGraph.predecessors g nid = {} 
        then None else
        Some (hd (sorted_list_of_set (IRGraph.predecessors g nid)))
      )
  )"


text \<open>
When the basic block of an if statement is entered, we know that the condition of the
preceding if statement must be true.
As in the GraalVM compiler, we introduce the registerNewCondition funciton which roughly
corresponds to the ConditionalEliminationPhase.registerNewCondition.
This method updates the flow-sensitive stamp information based on the condition which
we know must be true. 
\<close>
fun clip_upper :: "Stamp \<Rightarrow> int \<Rightarrow> Stamp" where
  "clip_upper (IntegerStamp b l h) c = (IntegerStamp b l c)" |
  "clip_upper s c = s"
fun clip_lower :: "Stamp \<Rightarrow> int \<Rightarrow> Stamp" where
  "clip_lower (IntegerStamp b l h) c = (IntegerStamp b c h)" |
  "clip_lower s c = s"

fun registerNewCondition :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> (ID \<Rightarrow> Stamp)" where
  (* constrain equality by joining the stamps *)
  "registerNewCondition g (IntegerEqualsNode x y) stamps =
    (stamps
      (x := join (stamps x) (stamps y)))
      (y := join (stamps x) (stamps y))" |
  (* constrain less than by removing overlapping stamps *)
  "registerNewCondition g (IntegerLessThanNode x y) stamps =
    (stamps
      (x := clip_upper (stamps x) (stpi_lower (stamps y))))
      (y := clip_lower (stamps y) (stpi_upper (stamps x)))" |
  "registerNewCondition g _ stamps = stamps"

fun hdOr :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "hdOr (x # xs) de = x" |
  "hdOr [] de = de"

text \<open>
The Step relation is a small-step traversal of the graph which handles transitions between
individual nodes of the graph.

It relates a pairs of tuple of the current node, the set of seen nodes, 
the always true stack of IfNode conditions, and the flow-sensitive stamp information.
\<close>
inductive Step 
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> Conditions \<times> StampFlow) \<Rightarrow> (ID \<times> Seen \<times> Conditions \<times> StampFlow) option \<Rightarrow> bool"
  for g where
  \<comment> \<open>
  Hit a BeginNode with an IfNode predecessor which represents
  the start of a basic block for the IfNode.
     1. nid' will be the successor of the begin node.
     2. Find the first and only predecessor.
     3. Extract condition from the preceding IfNode.
     4. Negate condition if the begin node is second branch
        (we've taken the else branch of the condition)
     5. Add the condition or the negated condition to stack
     6. Perform any stamp updates based on the condition using
        the registerNewCondition function and place them on the
        top of the stack of stamp information
  \<close>
  "\<lbrakk>kind g nid = BeginNode nid';

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    Some ifcond = pred g nid;
    kind g ifcond = IfNode cond t f;

    i = find_index nid (successors_of (kind g ifcond));
    c = (if i = 0 then kind g cond else LogicNegationNode cond);
    rep g cond ce;
    ce' = (if i = 0 then ce else UnaryExpr UnaryLogicNegation ce);
    conds' = ce' # conds;

    flow' = registerNewCondition g c (hdOr flow (stamp g))\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow' # flow))" |

  \<comment> \<open>
  Hit an EndNode
     1. nid' will be the usage of EndNode
     2. pop the conditions and stamp stack
  \<close>
  "\<lbrakk>kind g nid = EndNode;

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    nid' = any_usage g nid;

    conds' = tl conds;
    flow' = tl flow\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'))" |

  \<comment> \<open>We can find a successor edge that is not in seen, go there\<close>
  "\<lbrakk>\<not>(is_EndNode (kind g nid));
    \<not>(is_BeginNode (kind g nid));

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    Some nid' = nextEdge seen' nid g\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds, flow) (Some (nid', seen', conds, flow))" |

  \<comment> \<open>We can cannot find a successor edge that is not in seen, give back None\<close>
  "\<lbrakk>\<not>(is_EndNode (kind g nid));
    \<not>(is_BeginNode (kind g nid));

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    None = nextEdge seen' nid g\<rbrakk>
    \<Longrightarrow> Step g (nid, seen, conds, flow) None" |

  \<comment> \<open>We've already seen this node, give back None\<close>
  "\<lbrakk>nid \<in> seen\<rbrakk> \<Longrightarrow> Step g (nid, seen, conds, flow) None"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) Step .


text \<open>
The ConditionalEliminationPhase relation is responsible for combining
the individual traversal steps from the Step relation and the optimizations
from the ConditionalEliminationStep relation to perform a transformation of the
whole graph.
\<close>

inductive ConditionalEliminationPhase 
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> Conditions \<times> StampFlow) \<Rightarrow> IRGraph \<Rightarrow> bool" where

  \<comment> \<open>Can do a step and optimise for the current node\<close>
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    ConditionalEliminationStep (set conds) (hdOr flow (stamp g)) g nid g';
    
    ConditionalEliminationPhase g' (nid', seen', conds', flow') g''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds, flow) g''" |

  \<comment> \<open>Can do a step, matches whether optimised or not causing non-determinism
      We need to find a way to negate ConditionalEliminationStep\<close>
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    
    ConditionalEliminationPhase g (nid', seen', conds', flow') g'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds, flow) g'" |

  \<comment> \<open>Can't do a step but there is a predecessor we can backtrace to\<close>
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    Some nid' = pred g nid;
    seen' = {nid} \<union> seen;
    ConditionalEliminationPhase g (nid', seen', conds, flow) g'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds, flow) g'" |

  \<comment> \<open>Can't do a step and have no predecessors so terminate\<close>
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    None = pred g nid\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds, flow) g"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationPhase .

definition runConditionalElimination :: "IRGraph \<Rightarrow> IRGraph" where
  "runConditionalElimination g = 
    (Predicate.the (ConditionalEliminationPhase_i_i_o g (0, {}, ([], []))))"


end