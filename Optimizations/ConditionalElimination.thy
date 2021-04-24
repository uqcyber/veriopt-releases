section \<open>Conditional Elimination Phase\<close>

theory ConditionalElimination
  imports
    Proofs.IRGraphFrames
    Proofs.Stuttering
    Proofs.Form
    Proofs.Rewrites
    Proofs.Bisimulation
begin

subsection \<open>Individual Elimination Rules\<close>
text \<open>
We introduce a TriState as in the Graal compiler to represent when static
analysis can tell us information about the value of a boolean expression.
Unknown = No information can be inferred
KnownTrue/KnownFalse = We can infer the expression will always be true or false.
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


text \<open>Total relation over partial implies relation\<close>
inductive condition_implies :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> TriState \<Rightarrow> bool"
  ("_ \<turnstile> _ & _ \<rightharpoonup> _") for g where
  "\<lbrakk>\<not>(g \<turnstile> a & b \<hookrightarrow> imp)\<rbrakk> \<Longrightarrow> (g \<turnstile> a & b \<rightharpoonup> Unknown)" |
  "\<lbrakk>(g \<turnstile> a & b \<hookrightarrow> imp)\<rbrakk> \<Longrightarrow> (g \<turnstile> a & b \<rightharpoonup> imp)"

text \<open>
Proofs that the implies relation is correct with respect to the 
existing evaluation semantics.
\<close>


lemma logic_negation_relation:
  assumes "wf_values g"
  assumes "g m \<turnstile> kind g y \<mapsto> val"
  assumes "kind g neg = LogicNegationNode y"
  assumes "g m \<turnstile> kind g neg \<mapsto> invval"
  shows "val_to_bool val \<longleftrightarrow> \<not>(val_to_bool inval)"
proof -
  have "wf_value val"
    using assms(1) assms(2) eval_in_ids wf_values.elims(2)
    by meson
  have "wf_value invval"
    using assms(1,4) eval_in_ids wf_values.simps by blast
  then show ?thesis 
    using assms eval.LogicNegationNode
    by fastforce
qed

lemma implies_valid:
  assumes "wf_graph g \<and> wf_values g"
  assumes "g \<turnstile> x & y \<rightharpoonup> imp"
  assumes "g m \<turnstile> x \<mapsto> v1"
  assumes "g m \<turnstile> y \<mapsto> v2"
  shows "(imp = KnownTrue \<longrightarrow> (val_to_bool v1 \<longrightarrow> val_to_bool v2)) \<and>
         (imp = KnownFalse \<longrightarrow> (val_to_bool v1 \<longrightarrow> \<not>(val_to_bool v2)))"
    (is "(?TP \<longrightarrow> ?TC) \<and> (?FP \<longrightarrow> ?FC)")
  apply (intro conjI; rule impI)
proof -
  assume KnownTrue: ?TP
  show ?TC proof -
  have s: "g \<turnstile> x & y \<hookrightarrow> imp"
    using KnownTrue assms(2) condition_implies.cases by blast
  then show ?thesis
  using KnownTrue assms proof (induct x y imp rule: implies.induct)
    case (eq_imp_less x y)
    then show ?case by simp
  next
    case (eq_imp_less_rev x y)
    then show ?case by simp
  next
    case (less_imp_rev_less x y)
    then show ?case by simp
  next
    case (less_imp_not_eq x y)
    then show ?case by simp
  next
    case (less_imp_not_eq_rev x y)
    then show ?case by simp
  next
    case (x_imp_x x1)
    then show ?case using evalDet
      using assms(2,3) by blast
  next
    case (negate_false x1)
    then show ?case using evalDet
      using assms(2,3) by blast
  next
    case (negate_true x y)
    then show ?case using logic_negation_relation
      by fastforce
  qed
  qed
next
  assume KnownFalse: ?FP
  show ?FC proof -
    have "g \<turnstile> x & y \<hookrightarrow> imp"
    using KnownFalse assms(2) condition_implies.cases by blast
  then show ?thesis
  using assms KnownFalse proof (induct x y imp rule: implies.induct)
    case (eq_imp_less x y)
    obtain b xval where xval: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xval"
      using eq_imp_less.prems(3) by blast
    then obtain yval where yval: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yval"
      using eq_imp_less.prems(3)
      using evalDet by blast
    have eqeval: "g m \<turnstile> (IntegerEqualsNode x y) \<mapsto> bool_to_val(xval = yval)"
      using eval.IntegerEqualsNode
      using xval yval by blast
    have lesseval: "g m \<turnstile> (IntegerLessThanNode x y) \<mapsto> bool_to_val(xval < yval)"
      using eval.IntegerLessThanNode
      using xval yval by blast
    have "xval = yval \<longrightarrow> \<not>(xval < yval)"
      by blast
    then show ?case
      using eqeval lesseval
      by (metis (full_types) "eq_imp_less.prems"(3) "eq_imp_less.prems"(4) bool_to_val.simps(2) evalDet val_to_bool.simps(1))
  next
    case (eq_imp_less_rev x y)
    obtain b xval where xval: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xval"
      using eq_imp_less_rev.prems(3) by blast
    then obtain yval where yval: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yval"
      using eq_imp_less_rev.prems(3)
      using evalDet by blast
    have eqeval: "g m \<turnstile> (IntegerEqualsNode x y) \<mapsto> bool_to_val(xval = yval)"
      using eval.IntegerEqualsNode
      using xval yval by blast
    have lesseval: "g m \<turnstile> (IntegerLessThanNode y x) \<mapsto> bool_to_val(yval < xval)"
      using eval.IntegerLessThanNode
      using xval yval by blast
    have "xval = yval \<longrightarrow> \<not>(yval < xval)"
      by blast
    then show ?case
      using eqeval lesseval
      by (metis (full_types) eq_imp_less_rev.prems(3) eq_imp_less_rev.prems(4) bool_to_val.simps(2) evalDet val_to_bool.simps(1))
  next
    case (less_imp_rev_less x y)
    obtain b xval where xval: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xval"
      using less_imp_rev_less.prems(3) by blast
    then obtain yval where yval: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yval"
      using less_imp_rev_less.prems(3)
      using evalDet by blast
    have lesseval: "g m \<turnstile> (IntegerLessThanNode x y) \<mapsto> bool_to_val(xval < yval)"
      using eval.IntegerLessThanNode
      using xval yval by blast
    have revlesseval: "g m \<turnstile> (IntegerLessThanNode y x) \<mapsto> bool_to_val(yval < xval)"
      using eval.IntegerLessThanNode
      using xval yval by blast
    have "xval < yval \<longrightarrow> \<not>(yval < xval)"
      by simp
    then show ?case
      by (metis (full_types) bool_to_val.simps(2) evalDet less_imp_rev_less.prems(3,4) less_imp_rev_less.prems(3) lesseval revlesseval val_to_bool.simps(1))
  next
    case (less_imp_not_eq x y)
    obtain b xval where xval: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xval"
      using less_imp_not_eq.prems(3) by blast
    then obtain yval where yval: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yval"
      using less_imp_not_eq.prems(3)
      using evalDet by blast
    have eqeval: "g m \<turnstile> (IntegerEqualsNode x y) \<mapsto> bool_to_val(xval = yval)"
      using eval.IntegerEqualsNode
      using xval yval by blast
    have lesseval: "g m \<turnstile> (IntegerLessThanNode x y) \<mapsto> bool_to_val(xval < yval)"
      using eval.IntegerLessThanNode
      using xval yval by blast
    have "xval < yval \<longrightarrow> \<not>(xval = yval)"
      by simp
    then show ?case
      by (metis (full_types) bool_to_val.simps(2) eqeval evalDet less_imp_not_eq.prems(3,4) less_imp_not_eq.prems(3) lesseval val_to_bool.simps(1))
  next
    case (less_imp_not_eq_rev x y)
    obtain b xval where xval: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xval"
      using less_imp_not_eq_rev.prems(3) by blast
    then obtain yval where yval: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yval"
      using less_imp_not_eq_rev.prems(3)
      using evalDet by blast
    have eqeval: "g m \<turnstile> (IntegerEqualsNode y x) \<mapsto> bool_to_val(yval = xval)"
      using eval.IntegerEqualsNode
      using xval yval by blast
    have lesseval: "g m \<turnstile> (IntegerLessThanNode x y) \<mapsto> bool_to_val(xval < yval)"
      using eval.IntegerLessThanNode
      using xval yval by blast
    have "xval < yval \<longrightarrow> \<not>(yval = xval)"
      by simp
    then show ?case
      by (metis (full_types) bool_to_val.simps(2) eqeval evalDet less_imp_not_eq_rev.prems(3,4) less_imp_not_eq_rev.prems(3) lesseval val_to_bool.simps(1))
  next
    case (x_imp_x x1)
    then show ?case by simp
  next
    case (negate_false x y)
    then show ?case using logic_negation_relation sorry
  next
    case (negate_true x1)
    then show ?case by simp
  qed
  qed
qed

lemma implies_true_valid:
  assumes "wf_graph g \<and> wf_values g"
  assumes "g \<turnstile> x & y \<rightharpoonup> imp"
  assumes "imp = KnownTrue"
  assumes "g m \<turnstile> x \<mapsto> v1"
  assumes "g m \<turnstile> y \<mapsto> v2"
  shows "val_to_bool v1 \<longrightarrow> val_to_bool v2"
  using assms implies_valid by blast

lemma implies_false_valid:
  assumes "wf_graph g \<and> wf_values g"
  assumes "g \<turnstile> x & y \<rightharpoonup> imp"
  assumes "imp = KnownFalse"
  assumes "g m \<turnstile> x \<mapsto> v1"
  assumes "g m \<turnstile> y \<mapsto> v2"
  shows "val_to_bool v1 \<longrightarrow> \<not>(val_to_bool v2)"
  using assms implies_valid by blast

text \<open>
The following relation corresponds to the UnaryOpLogicNode.tryFold
and BinaryOpLogicNode.tryFold methods and their associated concrete implementations.

The relation determines if a logic operation can be shown true or false
through the stamp typing information.
\<close>
inductive tryFold :: "IRNode \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> TriState \<Rightarrow> bool"
  where
  "\<lbrakk>alwaysDistinct (stamps x) (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerEqualsNode x y) stamps KnownFalse" |
  "\<lbrakk>neverDistinct (stamps x) (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerEqualsNode x y) stamps KnownTrue" |
  "\<lbrakk>is_IntegerStamp (stamps x);
    is_IntegerStamp (stamps y);
    stpi_upper (stamps x) < stpi_lower (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerLessThanNode x y) stamps KnownTrue" |
  "\<lbrakk>is_IntegerStamp (stamps x);
    is_IntegerStamp (stamps y);
    stpi_lower (stamps x) \<ge> stpi_upper (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerLessThanNode x y) stamps KnownFalse"


text \<open>
Proofs that show that when the stamp lookup function is well-formed,
the tryFold relation correctly predicts the output value with respect to
our evaluation semantics.
\<close>
lemma tryFoldIntegerEqualsAlwaysDistinct:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerEqualsNode x y)"
  assumes "g m \<turnstile> (kind g nid) \<mapsto> v"
  assumes "alwaysDistinct (stamps x) (stamps y)"
  shows "v = IntVal 1 0"
  using assms eval.IntegerEqualsNode join_unequal alwaysDistinct.simps
  by (smt (verit, best) IntegerEqualsNodeE bool_to_val.simps(2) eval_in_ids wf_stamp.elims(2))

lemma tryFoldIntegerEqualsNeverDistinct:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerEqualsNode x y)"
  assumes "g m \<turnstile> (kind g nid) \<mapsto> v"
  assumes "neverDistinct (stamps x) (stamps y)"
  shows "v = IntVal 1 1"
  using assms neverDistinctEqual IntegerEqualsNodeE
  by (smt (verit, ccfv_threshold) Value.inject(1) bool_to_val.simps(1) eval_in_ids wf_stamp.simps)

lemma tryFoldIntegerLessThanTrue:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerLessThanNode x y)"
  assumes "g m \<turnstile> (kind g nid) \<mapsto> v"
  assumes "stpi_upper (stamps x) < stpi_lower (stamps y)"
  shows "v = IntVal 1 1"
proof -
  have stamp_type: "is_IntegerStamp (stamps x)"
    using assms
    by (metis IntegerLessThanNodeE Stamp.disc(2) Value.distinct(1) eval_in_ids valid_value.elims(2) wf_stamp.elims(2))
  obtain xval b where xval: "g m \<turnstile> kind g x \<mapsto> IntVal b xval"
    using assms(2,3) eval.IntegerLessThanNode by auto
  obtain yval b where yval: "g m \<turnstile> kind g y \<mapsto> IntVal b yval"
    using assms(2,3) eval.IntegerLessThanNode by auto
  have "is_IntegerStamp (stamps x) \<and> is_IntegerStamp (stamps y)"
    using assms(4)
    by (metis stamp_type Stamp.disc(2) Value.distinct(1) assms(1) eval_in_ids valid_value.elims(2) wf_stamp.simps yval)
  then have "xval < yval"
    using boundsNoOverlap xval yval assms(1,4)
    using eval_in_ids wf_stamp.elims(2)
    by metis
  then show ?thesis
    by (metis (full_types) IntegerLessThanNodeE Value.sel(3) assms(2) assms(3) bool_to_val.simps(1) evalDet xval yval)
qed

lemma tryFoldIntegerLessThanFalse:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerLessThanNode x y)"
  assumes "g m \<turnstile> (kind g nid) \<mapsto> v"
  assumes "stpi_lower (stamps x) \<ge> stpi_upper (stamps y)"
  shows "v = IntVal 1 0"
  proof -
  have stamp_type: "is_IntegerStamp (stamps x)"
    using assms
    by (metis IntegerLessThanNodeE Stamp.disc(2) Value.distinct(1) eval_in_ids valid_value.elims(2) wf_stamp.elims(2))
  obtain xval b where xval: "g m \<turnstile> kind g x \<mapsto> IntVal b xval"
    using assms(2,3) eval.IntegerLessThanNode by auto
  obtain yval b where yval: "g m \<turnstile> kind g y \<mapsto> IntVal b yval"
    using assms(2,3) eval.IntegerLessThanNode by auto
  have "is_IntegerStamp (stamps x) \<and> is_IntegerStamp (stamps y)"
    using assms(4)
    by (metis stamp_type Stamp.disc(2) Value.distinct(1) assms(1) eval_in_ids valid_value.elims(2) wf_stamp.simps yval)
  then have "\<not>(xval < yval)"
    using boundsAlwaysOverlap xval yval assms(1,4)
    using eval_in_ids wf_stamp.elims(2)
    by metis
  then show ?thesis
    by (smt (verit, best) IntegerLessThanNodeE Value.inject(1) assms(2) assms(3) bool_to_val.simps(2) evalDet xval yval)
qed

theorem tryFoldProofTrue:
  assumes "wf_stamp g stamps"
  assumes "tryFold (kind g nid) stamps tristate"
  assumes "tristate = KnownTrue"
  assumes "g m \<turnstile> kind g nid \<mapsto> v"
  shows "val_to_bool v"
  using assms(2) proof (induction "kind g nid" stamps tristate rule: tryFold.induct)
case (1 stamps x y)
  then show ?case using tryFoldIntegerEqualsAlwaysDistinct assms
    by (smt (verit, best) IRNode.distinct(949) TriState.distinct(5) tryFold.cases tryFoldIntegerEqualsNeverDistinct val_to_bool.simps(1))
next
  case (2 stamps x y)
  then show ?case using tryFoldIntegerEqualsAlwaysDistinct assms
    by (smt (verit) IRNode.distinct(949) TriState.distinct(5) tryFold.cases tryFoldIntegerEqualsNeverDistinct val_to_bool.simps(1))
next
  case (3 stamps x y)
  then show ?case using tryFoldIntegerLessThanTrue assms
    by (smt (verit, best) IRNode.simps(994) TriState.simps(6) tryFold.cases val_to_bool.simps(1))
next
case (4 stamps x y)
  then show ?case using tryFoldIntegerLessThanFalse assms
    by (smt (verit, best) IRNode.simps(994) TriState.simps(6) tryFold.simps tryFoldIntegerLessThanTrue val_to_bool.simps(1))
qed

theorem tryFoldProofFalse:
  assumes "wf_stamp g stamps"
  assumes "tryFold (kind g nid) stamps tristate"
  assumes "tristate = KnownFalse"
  assumes "g m \<turnstile> (kind g nid) \<mapsto> v"
  shows "\<not>(val_to_bool v)"
using assms(2) proof (induction "kind g nid" stamps tristate rule: tryFold.induct)
case (1 stamps x y)
  then show ?case using tryFoldIntegerEqualsAlwaysDistinct assms
    by (smt (verit, best) IRNode.distinct(949) TriState.distinct(5) Value.inject(1) tryFold.cases val_to_bool.elims(2))
next
case (2 stamps x y)
  then show ?case using tryFoldIntegerEqualsNeverDistinct assms
    by (smt (verit, best) IRNode.distinct(949) TriState.distinct(5) Value.inject(1) tryFold.cases tryFoldIntegerEqualsAlwaysDistinct val_to_bool.elims(2))
next
  case (3 stamps x y)
  then show ?case using tryFoldIntegerLessThanTrue assms
    by (smt (verit, best) TriState.distinct(5) tryFold.cases tryFoldIntegerEqualsAlwaysDistinct tryFoldIntegerLessThanFalse val_to_bool.simps(1))
next
  case (4 stamps x y)
  then show ?case using tryFoldIntegerLessThanFalse assms
    by (smt (verit, best) TriState.distinct(5) tryFold.cases tryFoldIntegerEqualsAlwaysDistinct val_to_bool.simps(1))
qed



inductive_cases StepE:
  "g \<turnstile> (nid,m,h) \<rightarrow> (nid',m',h)"

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
  "IRNode set \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> IRGraph \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  impliesTrue:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    \<exists> c \<in> conds . (g \<turnstile> c & cond \<hookrightarrow> KnownTrue);
    g' = constantCondition True ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'" |

  impliesFalse:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    \<exists> c \<in> conds . (g \<turnstile> c & cond \<hookrightarrow> KnownFalse);
    g' = constantCondition False ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'" |

  tryFoldTrue:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    tryFold (kind g cid) stamps KnownTrue;
    g' = constantCondition True ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'" |

  tryFoldFalse:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    tryFold (kind g cid) stamps KnownFalse;
    g' = constantCondition False ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'"


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationStep .

thm ConditionalEliminationStep.equation

subsection \<open>Control-flow Graph Traversal\<close>

type_synonym Seen = "ID set"
type_synonym Conditions = "IRNode list"
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
    (stamps(x := join (stamps x) (stamps y)))(y := join (stamps x) (stamps y))" |
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
    c = (if i = 0 then kind g cond else NegateNode cond);
    conds' = c # conds;

    flow' = registerNewCondition g (kind g cond) (hdOr flow (stamp g))\<rbrakk>
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


inductive ConditionalEliminationPhaseWithTrace\<^marker>\<open>tag invisible\<close>
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> Conditions \<times> StampFlow) \<Rightarrow> ID list \<Rightarrow> IRGraph \<Rightarrow> ID list \<Rightarrow> Conditions \<Rightarrow> bool" where\<^marker>\<open>tag invisible\<close>

  (* Can do a step and optimise for the current nid *)
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    ConditionalEliminationStep (set conds) (hdOr flow (stamp g)) g nid g';
    
    ConditionalEliminationPhaseWithTrace g' (nid', seen', conds', flow') (nid # t) g'' t' conds''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g'' t' conds''" |

  (* Can do a step, matches whether optimised or not causing non-determinism
     Need to find a way to negate ConditionalEliminationStep *)
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    
    ConditionalEliminationPhaseWithTrace g (nid', seen', conds', flow') (nid # t) g' t' conds''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g' t' conds''" |

  (* Can't do a step but there is a predecessor we can backtrace to *)
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    Some nid' = pred g nid;
    seen' = {nid} \<union> seen;
    ConditionalEliminationPhaseWithTrace g (nid', seen', conds, flow) (nid # t) g' t' conds'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g' t' conds'" |

  (* Can't do a step and have no predecessors do terminate *)
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    None = pred g nid\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g (nid # t) conds"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationPhaseWithTrace .


lemma IfNodeStepE: "g \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h) \<Longrightarrow>
  (\<And>cond tb fb val.
        kind g nid = IfNode cond tb fb \<Longrightarrow>
        nid' = (if val_to_bool val then tb else fb) \<Longrightarrow> 
        g m \<turnstile> kind g cond \<mapsto> val \<Longrightarrow> m' = m)"
  using StepE
  by (smt (verit, best) IfNode Pair_inject stepDet)

lemma ifNodeHasCondEvalStutter:
  assumes "(g m h \<turnstile> nid \<leadsto> nid')"
  assumes "kind g nid = IfNode cond t f"
  shows "\<exists> v. (g m \<turnstile> kind g cond \<mapsto> v)"
  using IfNodeStepE assms(1) assms(2)  stutter.cases
  by (meson IfNodeCond)

lemma ifNodeHasCondEval:
  assumes "(g \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h'))"
  assumes "kind g nid = IfNode cond t f"
  shows "\<exists> v. (g m \<turnstile> kind g cond \<mapsto> v)"
  using IfNodeStepE assms(1) assms(2)
  by (smt (z3) IRNode.disc(932) IRNode.simps(938) IRNode.simps(958) IRNode.simps(972) IRNode.simps(974) IRNode.simps(978) Pair_inject StutterStep ifNodeHasCondEvalStutter is_AbstractEndNode.simps is_EndNode.simps(12) step.cases)


lemma replace_if_t:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g m \<turnstile> kind g cond \<mapsto> bool"
  assumes "val_to_bool bool"
  assumes g': "g' = replace_usages nid tb g"
  shows "\<exists>nid' .(g m h \<turnstile> nid \<leadsto> nid') \<longleftrightarrow> (g' m h \<turnstile> nid \<leadsto> nid')"
proof -
  have g1step: "g \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    by (meson IfNode assms(1) assms(2) assms(3))
  have g2step: "g' \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using g' unfolding replace_usages.simps
    by (simp add: stepRefNode)
  from g1step g2step show ?thesis
    using StutterStep by blast
qed

lemma replace_if_t_imp:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g m \<turnstile> kind g cond \<mapsto> bool"
  assumes "val_to_bool bool"
  assumes g': "g' = replace_usages nid tb g"
  shows "\<exists>nid' .(g m h \<turnstile> nid \<leadsto> nid') \<longrightarrow> (g' m h \<turnstile> nid \<leadsto> nid')"
  using replace_if_t assms by blast

lemma replace_if_f:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g m \<turnstile> kind g cond \<mapsto> bool"
  assumes "\<not>(val_to_bool bool)"
  assumes g': "g' = replace_usages nid fb g"
  shows "\<exists>nid' .(g m h \<turnstile> nid \<leadsto> nid') \<longleftrightarrow> (g' m h \<turnstile> nid \<leadsto> nid')"
proof -
  have g1step: "g \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    by (meson IfNode assms(1) assms(2) assms(3))
  have g2step: "g' \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    using g' unfolding replace_usages.simps
    by (simp add: stepRefNode)
  from g1step g2step show ?thesis
    using StutterStep by blast
qed

text \<open>
Prove that the individual conditional elimination rules are correct
with respect to preservation of stuttering steps.
\<close>
lemma ConditionalEliminationStepProof:
  assumes wg: "wf_graph g"
  assumes ws: "wf_stamps g"
  assumes wv: "wf_values g"
  assumes nid: "nid \<in> ids g"
  assumes conds_valid: "\<forall> c \<in> conds . \<exists> v. (g m \<turnstile> c \<mapsto> v) \<and> val_to_bool v"
  assumes ce: "ConditionalEliminationStep conds stamps g nid g'"

  shows "\<exists>nid' .(g m h \<turnstile> nid \<leadsto> nid') \<longrightarrow> (g' m h \<turnstile> nid \<leadsto> nid')"
  using ce using assms
proof (induct g nid g' rule: ConditionalEliminationStep.induct)
  case (impliesTrue g ifcond cid t f cond conds g')
  show ?case proof (cases "(g m h \<turnstile> ifcond \<leadsto> nid')")
    case True
    obtain condv where condv: "g m \<turnstile> kind g cid \<mapsto> condv"
      using implies.simps impliesTrue.hyps(3) impliesTrue.prems(4)
      using impliesTrue.hyps(2) True
      by (metis ifNodeHasCondEvalStutter impliesTrue.hyps(1))
    have condvTrue: "val_to_bool condv"
      by (metis condition_implies.intros(2) condv impliesTrue.hyps(2) impliesTrue.hyps(3) impliesTrue.prems(1) impliesTrue.prems(3) impliesTrue.prems(5) implies_true_valid)
    then show ?thesis
      using constantConditionValid 
      using impliesTrue.hyps(1) condv impliesTrue.hyps(4)
      by blast
  next
    case False
    then show ?thesis by auto
  qed
next
  case (impliesFalse g ifcond cid t f cond conds g')
  then show ?case 
  proof (cases "(g m h \<turnstile> ifcond \<leadsto> nid')")
    case True
    obtain condv where condv: "g m \<turnstile> kind g cid \<mapsto> condv"
      using ifNodeHasCondEvalStutter impliesFalse.hyps(1)
      using True by blast
    have condvFalse: "False = val_to_bool condv"
      by (metis condition_implies.intros(2) condv impliesFalse.hyps(2) impliesFalse.hyps(3) impliesFalse.prems(1) impliesFalse.prems(3) impliesFalse.prems(5) implies_false_valid)
    then show ?thesis
      using constantConditionValid 
      using impliesFalse.hyps(1) condv impliesFalse.hyps(4)
      by blast
  next
    case False
    then show ?thesis
      by auto
  qed
next
  case (tryFoldTrue g ifcond cid t f cond g' conds)
  then show ?case using constantConditionValid tryFoldProofTrue
    using StutterStep constantConditionTrue by metis
next
  case (tryFoldFalse g ifcond cid t f cond g' conds)
  then show ?case using constantConditionValid tryFoldProofFalse
    using StutterStep constantConditionFalse by metis
qed


text \<open>
Prove that the individual conditional elimination rules are correct
with respect to finding a bisimulation between the unoptimized and optimized graphs.
\<close>
lemma ConditionalEliminationStepProofBisimulation:
  assumes wf: "wf_graph g \<and> wf_stamp g stamps \<and> wf_values g"
  assumes nid: "nid \<in> ids g"
  assumes conds_valid: "\<forall> c \<in> conds . \<exists> v. (g m \<turnstile> c \<mapsto> v) \<and> val_to_bool v"
  assumes ce: "ConditionalEliminationStep conds stamps g nid g'"
  assumes gstep: "\<exists> h nid'. (g \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h))" (* we don't yet consider optimizations which produce a step that didn't already exist *)

  shows "nid | g \<sim> g'"
  using ce gstep using assms
proof (induct g nid g' rule: ConditionalEliminationStep.induct)
  case (impliesTrue g ifcond cid t f cond conds g' stamps)
  from impliesTrue(5) obtain h where gstep: "g \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    by (metis IfNode StutterStep condition_implies.intros(2) ifNodeHasCondEvalStutter impliesTrue.hyps(1) impliesTrue.hyps(2) impliesTrue.hyps(3) impliesTrue.prems(2) impliesTrue.prems(4) implies_true_valid)
  have "g' \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using constantConditionTrue impliesTrue.hyps(1) impliesTrue.hyps(4) by blast
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
next
  case (impliesFalse g ifcond cid t f cond conds g' stamps)
  from impliesFalse(5) obtain h where gstep: "g \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    by (metis IfNode condition_implies.intros(2) ifNodeHasCondEval impliesFalse.hyps(1) impliesFalse.hyps(2) impliesFalse.hyps(3) impliesFalse.prems(2) impliesFalse.prems(4) implies_false_valid)
  have "g' \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using constantConditionFalse impliesFalse.hyps(1) impliesFalse.hyps(4) by blast
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
next
  case (tryFoldTrue g ifcond cid t f cond stamps g' conds)
  from tryFoldTrue(5) obtain val where "g m \<turnstile> kind g cid \<mapsto> val"
    using ifNodeHasCondEval tryFoldTrue.hyps(1) by blast
  then have "val_to_bool val"
    using tryFoldProofTrue tryFoldTrue.prems(2) tryFoldTrue(3) 
    by blast
  then obtain h where gstep: "g \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using tryFoldTrue(5)
    by (meson IfNode \<open>g m \<turnstile> kind g cid \<mapsto> val\<close> tryFoldTrue.hyps(1))
  have "g' \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using constantConditionTrue tryFoldTrue.hyps(1) tryFoldTrue.hyps(4) by presburger
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
next
  case (tryFoldFalse g ifcond cid t f cond stamps g' conds)
  from tryFoldFalse(5) obtain h where gstep: "g \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    by (meson IfNode ifNodeHasCondEval tryFoldFalse.hyps(1) tryFoldFalse.hyps(3) tryFoldFalse.prems(2) tryFoldProofFalse)
  have "g' \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using constantConditionFalse tryFoldFalse.hyps(1) tryFoldFalse.hyps(4) by blast
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
qed


text \<open>Mostly experimental proofs from here on out.\<close>

(* lies we tell isabelle to get things to pass *)
lemma if_step:
  assumes "nid \<in> ids g"
  assumes "(kind g nid) \<in> control_nodes"
  shows "(g m h \<turnstile> nid \<leadsto> nid')"
  using assms apply (cases "kind g nid") sorry

lemma StepConditionsValid:
  assumes "\<forall> cond \<in> set conds. (g m \<turnstile> cond \<mapsto> v) \<and> val_to_bool v"
  assumes "Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'))"
  shows "\<forall> cond \<in> set conds'. (g m \<turnstile> cond \<mapsto> v) \<and> val_to_bool v"
  using assms(2) 
proof (induction "(nid, seen, conds, flow)" "Some (nid', seen', conds', flow')" rule: Step.induct)
  case (1 ifcond cond t f i c)
  obtain cv where cv: "g m \<turnstile> c \<mapsto> cv"
    sorry
  have cvt: "val_to_bool cv"
    sorry
  have "set conds' = {c} \<union> set conds"
    using "1.hyps"(8) by auto
  then show ?case using cv cvt assms(1) sorry
next
  case (2)
  from 2(5) have "set conds' \<subseteq> set conds"
    by (metis list.sel(2) list.set_sel(2) subsetI)
  then show ?case using assms(1)
    by blast
next
case (3)
  then show ?case
    using assms(1) by force
qed

lemma ConditionalEliminationPhaseProof:
  assumes "wf_graph g"
  assumes "wf_stamps g"
  assumes "ConditionalEliminationPhase g (0, {}, [], []) g'"
  
  shows "\<exists>nid' .(g m h \<turnstile> 0 \<leadsto> nid') \<longrightarrow> (g' m h \<turnstile> 0 \<leadsto> nid')"
proof -
  have "0 \<in> ids g"
    using assms(1) wf_folds by blast
  show ?thesis
using assms(3) assms proof (induct rule: ConditionalEliminationPhase.induct)
case (1 g nid g' succs nid' g'')
  then show ?case sorry
next
  case (2 succs g nid nid' g'')
  then show ?case sorry
next
  case (3 succs g nid)
  then show ?case 
    by simp
next
  case (4)
  then show ?case sorry
qed
qed

end