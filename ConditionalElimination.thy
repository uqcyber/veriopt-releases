theory ConditionalElimination
  imports
    IREval
    Stuttering
    IRGraphFrames
begin

datatype TriState = Unknown | KnownTrue | KnownFalse

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
  "g \<turnstile> x & x \<hookrightarrow> KnownTrue"

inductive condition_implies :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> TriState \<Rightarrow> bool"
  ("_ \<turnstile> _ & _ \<rightharpoonup> _") for g where
  "\<lbrakk>\<not>(g \<turnstile> a & b \<hookrightarrow> imp)\<rbrakk> \<Longrightarrow> (g \<turnstile> a & b \<rightharpoonup> Unknown)" |
  "\<lbrakk>(g \<turnstile> a & b \<hookrightarrow> imp)\<rbrakk> \<Longrightarrow> (g \<turnstile> a & b \<rightharpoonup> imp)"

lemma implies_true_valid:
  assumes "g \<turnstile> x & y \<rightharpoonup> imp"
  assumes "imp = KnownTrue"
  assumes "g m \<turnstile> x \<mapsto> v1"
  assumes "g m \<turnstile> y \<mapsto> v2"
  shows "val_to_bool v1 \<longrightarrow> val_to_bool v2"
proof -
  have "g \<turnstile> x & y \<hookrightarrow> imp"
    using assms(1) assms(2) condition_implies.cases by blast

then show ?thesis
using assms proof (induct x y imp rule: implies.induct)
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
    using assms(3) assms(4) by blast
qed
qed

lemma implies_false_valid:
  assumes "wff_graph g"
  assumes "g \<turnstile> x & y \<rightharpoonup> imp"
  assumes "imp = KnownFalse"
  assumes "g m \<turnstile> x \<mapsto> v1"
  assumes "g m \<turnstile> y \<mapsto> v2"
  shows "val_to_bool v1 \<longrightarrow> \<not>(val_to_bool v2)"
proof -
  have "g \<turnstile> x & y \<hookrightarrow> imp"
    using assms(2) assms(3) condition_implies.cases by blast

then show ?thesis
using assms proof (induct x y imp rule: implies.induct)
  case (eq_imp_less x y)
  obtain b xval where xval: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xval"
    using eq_imp_less.prems(4) by blast
  then obtain yval where yval: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yval"
    using eq_imp_less.prems(4)
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
    by (metis (full_types) "eq_imp_less.prems"(4) "eq_imp_less.prems"(5) bool_to_val.simps(2) evalDet val_to_bool.simps(1))
next
  case (eq_imp_less_rev x y)
  obtain b xval where xval: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xval"
    using eq_imp_less_rev.prems(4) by blast
  then obtain yval where yval: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yval"
    using eq_imp_less_rev.prems(4)
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
    by (metis (full_types) eq_imp_less_rev.prems(4) eq_imp_less_rev.prems(5) bool_to_val.simps(2) evalDet val_to_bool.simps(1))
next
  case (less_imp_rev_less x y)
  obtain b xval where xval: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xval"
    using less_imp_rev_less.prems(4) by blast
  then obtain yval where yval: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yval"
    using less_imp_rev_less.prems(4)
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
    by (metis (full_types) bool_to_val.simps(2) evalDet less_imp_rev_less.prems(4) less_imp_rev_less.prems(5) lesseval revlesseval val_to_bool.simps(1))
next
  case (less_imp_not_eq x y)
  obtain b xval where xval: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xval"
    using less_imp_not_eq.prems(4) by blast
  then obtain yval where yval: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yval"
    using less_imp_not_eq.prems(4)
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
    by (metis (full_types) bool_to_val.simps(2) eqeval evalDet less_imp_not_eq.prems(4) less_imp_not_eq.prems(5) lesseval val_to_bool.simps(1))
next
  case (less_imp_not_eq_rev x y)
  obtain b xval where xval: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xval"
    using less_imp_not_eq_rev.prems(4) by blast
  then obtain yval where yval: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yval"
    using less_imp_not_eq_rev.prems(4)
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
    by (metis (full_types) bool_to_val.simps(2) eqeval evalDet less_imp_not_eq_rev.prems(4) less_imp_not_eq_rev.prems(5) lesseval val_to_bool.simps(1))
next
  case (x_imp_x x1)
  then show ?case by simp
qed
qed


fun wff_stamps :: "IRGraph \<Rightarrow> bool" where
  "wff_stamps g = (\<forall> n \<in> ids g . 
    (\<forall> v m . (g m \<turnstile> (kind g n) \<mapsto> v) \<longrightarrow> valid_value (stamp g n) v))"

fun replace_usages :: "ID \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "replace_usages nid nid' g = replace_node nid (RefNode nid', stamp g nid') g"

lemma replace_usages_effect:
  assumes "g' = replace_usages nid nid' g"
  shows "kind g' nid = RefNode nid'"
  using IRNode.distinct(1980) assms replace_node_lookup replace_usages.simps by presburger

lemma replace_usages_changeonly:
  assumes "nid \<in> ids g"
  assumes "g' = replace_usages nid nid' g"
  shows "changeonly {nid} g g'"
  using assms unfolding replace_usages.simps
  by (metis DiffI changeonly.elims(3) ids_some replace_node_unchanged)

lemma replace_usages_unchanged:
  assumes "nid \<in> ids g"
  assumes "g' = replace_usages nid nid' g"
  shows "unchanged (ids g - {nid}) g g'"
  using assms unfolding replace_usages.simps
  by (smt (verit, del_insts) DiffE ids_some replace_node_unchanged unchanged.simps)

lemma asConstantEval:
  assumes "wff_stamps g"
  assumes "asConstant (stamp g nid) = val"
  assumes "val \<noteq> UndefVal"
  assumes "g m \<turnstile> (kind g nid) \<mapsto> v"
  shows "v = val"
proof -
  have "\<exists>b l h. stamp g nid = (IntegerStamp b l h)"
    using assms(2,3) asConstant.elims by (cases "stamp g nid"; auto)
  then obtain b l h where "stamp g nid = (IntegerStamp b l h)"
    by blast
  then have "l = h"
    using asConstant.simps(1) assms(2) assms(3) by presburger
  then have "{x . valid_value (stamp g nid) x} = {IntVal b l}"
    using assms(2) assms(3) int_valid_range
    using \<open>stamp g nid = IntegerStamp b l h\<close> by force
  then show ?thesis using assms(1)
    using \<open>l = h\<close> \<open>stamp g nid = IntegerStamp b l h\<close> assms(2) assms(4) by fastforce
qed

fun alwaysDistinct :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "alwaysDistinct stamp1 stamp2 = is_stamp_empty (join stamp1 stamp2)"

fun neverDistinct :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "neverDistinct stamp1 stamp2 = (asConstant stamp1 = asConstant stamp2 \<and> asConstant stamp1 \<noteq> UndefVal)"

lemma tryFoldIntegerEqualsAlwaysDistinct:
  assumes "wff_stamps g"
  assumes "kind g nid = (IntegerEqualsNode x y)"
  assumes "g m \<turnstile> (kind g nid) \<mapsto> v"
  assumes "alwaysDistinct (stamp g x) (stamp g y)"
  shows "v = IntVal 1 0"
  using assms eval.IntegerEqualsNode join_unequal alwaysDistinct.simps
  by (smt IntegerEqualsNodeE NoNodeE bool_to_val.simps(2) ids_some wff_stamps.simps)

lemma tryFoldIntegerEqualsNeverDistinct:
  assumes "wff_stamps g"
  assumes "kind g nid = (IntegerEqualsNode x y)"
  assumes "g m \<turnstile> (kind g nid) \<mapsto> v"
  assumes "neverDistinct (stamp g x) (stamp g y)"
  shows "v = IntVal 1 1"
  using assms asConstantEval neverDistinct.simps
  by (smt IntegerEqualsNodeE Value.inject(1) bool_to_val.simps(1))

inductive_cases StepE:
  "g \<turnstile> (nid,m,h) \<rightarrow> (nid',m',h)"

fun nextNid :: "IRGraph \<Rightarrow> ID" where
  "nextNid g = (Max (ids g)) + 1"

lemma max_plus_one:
  fixes c :: "ID set"
  shows "\<lbrakk>finite c; c \<noteq> {}\<rbrakk> \<Longrightarrow> (Max c) + 1 \<notin> c"
  by (meson Max_gr_iff less_add_one less_irrefl)

lemma ids_finite:
  "finite (ids g)"
  by simp

lemma nextNidNotIn:
  "ids g \<noteq> {} \<longrightarrow> nextNid g \<notin> ids g"
  unfolding nextNid.simps ids_finite
  using ids_finite max_plus_one by blast

fun constantCondition :: "bool \<Rightarrow> ID \<Rightarrow> IRNode \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "constantCondition val nid (IfNode cond t f) g = 
    replace_node nid (IfNode (nextNid g) t f, stamp g nid) 
      (add_node (nextNid g) ((ConstantNode (bool_to_val val)), default_stamp) g)" |
  "constantCondition cond nid _ g = g"

lemma constantConditionTrue:
  assumes "kind g ifcond = IfNode cond t f"
  assumes "g' = constantCondition True ifcond (kind g ifcond) g"
  shows "g' \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
proof -
  have if': "kind g' ifcond = IfNode (nextNid g) t f"
    by (metis IRNode.simps(965) assms(1) assms(2) constantCondition.simps(1) replace_node_lookup)
  have "bool_to_val True = (IntVal 1 1)"
    by auto
  have "ifcond \<noteq> (nextNid g)"
    by (metis IRNode.simps(965) assms(1) emptyE ids_some nextNidNotIn)
  then have c': "kind g' (nextNid g) = ConstantNode (IntVal 1 1)"
    using assms(2) replace_node_unchanged
    by (metis Diff_iff IRNode.distinct(571) \<open>bool_to_val True = IntVal 1 1\<close> add_node_lookup assms(1) constantCondition.simps(1) emptyE ids_some insert_iff)
  from if' c' show ?thesis using IfNode
    by (smt (z3) ConstantNode val_to_bool.simps(1))
qed

lemma constantConditionFalse:
  assumes "kind g ifcond = IfNode cond t f"
  assumes "g' = constantCondition False ifcond (kind g ifcond) g"
  shows "g' \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
proof -
  have if': "kind g' ifcond = IfNode (nextNid g) t f"
    by (metis IRNode.simps(965) assms(1) assms(2) constantCondition.simps(1) replace_node_lookup)
  have "bool_to_val False = (IntVal 1 0)"
    by auto
  have "ifcond \<noteq> (nextNid g)"
    by (metis IRNode.simps(965) assms(1) emptyE ids_some nextNidNotIn)
  then have c': "kind g' (nextNid g) = ConstantNode (IntVal 1 0)"
    using assms(2) replace_node_unchanged
    by (metis Diff_iff IRNode.distinct(571) \<open>bool_to_val False = IntVal 1 0\<close> add_node_lookup assms(1) constantCondition.simps(1) emptyE ids_some insert_iff)
  from if' c' show ?thesis using IfNode
    by (smt (z3) ConstantNode val_to_bool.simps(1))
qed

lemma diff_forall:
  assumes "\<forall>n\<in>ids g - {nid}. cond n"
  shows "\<forall>n. n \<in> ids g \<and> n \<notin> {nid} \<longrightarrow> cond n"
  by (meson Diff_iff assms)

lemma replace_node_changeonly:
  assumes "g' = replace_node nid node g"
  shows "changeonly {nid} g g'"
  using assms replace_node_unchanged
  unfolding changeonly.simps using diff_forall
  sorry (* Isabelle isn't doing good *)

lemma add_node_changeonly:
  assumes "g' = add_node nid node g"
  shows "changeonly {nid} g g'"
  by (metis Rep_IRGraph_inverse add_node.rep_eq assms replace_node.rep_eq replace_node_changeonly)

lemma constantConditionNoEffect:
  assumes "\<not>(is_IfNode (kind g nid))"
  shows "g = constantCondition b nid (kind g nid) g"
  using assms apply (cases "kind g nid")
  using constantCondition.simps 
  apply presburger+
  apply (metis is_IfNode_def)
  using constantCondition.simps 
  by presburger+

lemma constantConditionIfNode:
  assumes "kind g nid = IfNode cond t f"
  shows "constantCondition val nid (kind g nid) g = 
    replace_node nid (IfNode (nextNid g) t f, stamp g nid) 
     (add_node (nextNid g) ((ConstantNode (bool_to_val val)), default_stamp) g)"
  using constantCondition.simps
  by (simp add: assms)

lemma constantCondition_changeonly:
  assumes "nid \<in> ids g"
  assumes "g' = constantCondition b nid (kind g nid) g"
  shows "changeonly {nid} g g'"
proof (cases "is_IfNode (kind g nid)")
  case True
  have "nextNid g \<notin> ids g"
    using nextNidNotIn by (metis emptyE)
  then show ?thesis using assms
    using replace_node_changeonly add_node_changeonly unfolding changeonly.simps
    using True constantCondition.simps(1) is_IfNode_def
    by (metis (full_types) DiffD2 Diff_insert_absorb)
next
  case False
  have "g = g'"
    using constantConditionNoEffect
    using False assms(2) by blast
  then show ?thesis by simp
qed
  

lemma constantConditionNoIf:
  assumes "\<forall>cond t f. kind g ifcond \<noteq> IfNode cond t f"
  assumes "g' = constantCondition val ifcond (kind g ifcond) g"
  shows "\<exists>nid' .(g m h \<turnstile> ifcond \<leadsto> nid') \<longleftrightarrow> (g' m h \<turnstile> ifcond \<leadsto> nid')"
proof -
  have "g' = g"
    using assms(2) assms(1)
    using constantConditionNoEffect
    by (metis IRNode.collapse(11))
  then show ?thesis by simp
qed

lemma constantConditionValid:
  assumes "kind g ifcond = IfNode cond t f"
  assumes "g m \<turnstile> kind g cond \<mapsto> v"
  assumes "const = val_to_bool v"
  assumes "g' = constantCondition const ifcond (kind g ifcond) g"
  shows "\<exists>nid' .(g m h \<turnstile> ifcond \<leadsto> nid') \<longleftrightarrow> (g' m h \<turnstile> ifcond \<leadsto> nid')"
proof (cases "const")
  case True
  have ifstep: "g \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    by (meson IfNode True assms(1) assms(2) assms(3))
  have ifstep': "g' \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using constantConditionTrue
    using True assms(1) assms(4) by presburger
  from ifstep ifstep' show ?thesis
    using Step by blast
next
  case False
  have ifstep: "g \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    by (meson IfNode False assms(1) assms(2) assms(3))
  have ifstep': "g' \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using constantConditionFalse
    using False assms(1) assms(4) by presburger
  from ifstep ifstep' show ?thesis
    using Step by blast
qed

inductive ConditionalEliminationStep :: "IRNode set \<Rightarrow> IRGraph \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  alwaysDistinctEq:
  "\<lbrakk>kind g ifcond = (IfNode cond t f);
    kind g cond = (IntegerEqualsNode x y);
    alwaysDistinct (stamp g x) (stamp g y);
    g' = constantCondition False ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds g ifcond g'" |

  neverDistinctEq:
  "\<lbrakk>kind g ifcond = (IfNode cond t f);
    kind g cond = (IntegerEqualsNode x y);
    neverDistinct (stamp g x) (stamp g y);
    g' = constantCondition True ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds g ifcond g'" |

  impliesTrue:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    \<exists> c \<in> conds . (g \<turnstile> c & cond \<hookrightarrow> KnownTrue);
    g' = constantCondition True ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds g ifcond g'" |

  impliesFalse:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    \<exists> c \<in> conds . (g \<turnstile> c & cond \<hookrightarrow> KnownFalse);
    g' = constantCondition False ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds g ifcond g'"


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationStep .



fun nextEdge :: "ID set \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> ID option" where
  "nextEdge seen nid g = 
    (let nids = (filter (\<lambda>nid'. nid' \<notin> seen) (IRGraph.succ g nid)) in 
     (if length nids > 0 then Some (hd nids) else None))"

fun pred :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID option" where
  "pred g nid = (case kind g nid of
    (MergeNode ends _ _) \<Rightarrow> Some (hd ends) |
    _ \<Rightarrow> 
      (if IRGraph.predecessors g nid = {} 
        then None else
        Some (hd (sorted_list_of_set (IRGraph.predecessors g nid)))
      )
  )"

type_synonym Seen = "ID set"
type_synonym Conditions = "IRNode list"


inductive Step 
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> Conditions) \<Rightarrow> (ID \<times> Seen \<times> Conditions) option \<Rightarrow> bool" where
  (* Hit a BeginNode
     1. nid' will be the successor of the begin node
     2. Find the first and only predecessor
     3. Extract condition from pred (pred is assumed IfNode)
     4. Negate condition if the begin node is second branch
     5. Add condition or negated condition to stack
  *)  
  "\<lbrakk>kind g nid = BeginNode nid';

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    Some ifcond = pred g nid;
    kind g ifcond = IfNode cond t b;

    i = find_index nid (IRGraph.succ g ifcond);
    c = (if i = 0 then kind g cond else NegateNode cond);
    conds' = c # conds\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds) (Some (nid', seen', conds'))" |

  (* Hit an EndNode
     1. nid' will be the usage of EndNode
     2. pop the conditions stack
  *)
  "\<lbrakk>kind g nid = EndNode;

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    nid' = any_usage g nid;

    conds' = tl conds\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds) (Some (nid', seen', conds'))" |

  (* We can find a successor edge that is not in seen, go there *)
  "\<lbrakk>\<not>(is_EndNode (kind g nid));
    \<not>(is_BeginNode (kind g nid));

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    Some nid' = nextEdge seen' nid g\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds) (Some (nid', seen', conds))" |

  (* We can cannot find a successor edge that is not in seen, give back None *)
  "\<lbrakk>\<not>(is_EndNode (kind g nid));
    \<not>(is_BeginNode (kind g nid));

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    None = nextEdge seen' nid g\<rbrakk>
    \<Longrightarrow> Step g (nid, seen, conds) None" |

  (* We've already seen this node, give back None *)
  "\<lbrakk>nid \<in> seen\<rbrakk> \<Longrightarrow> Step g (nid, seen, conds) None"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) Step .

inductive ConditionalEliminationPhase 
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> Conditions) \<Rightarrow> IRGraph \<Rightarrow> bool" where

  (* Can do a step and optimise for the current nid *)
  "\<lbrakk>Step g (nid, seen, conds) (Some (nid', seen', conds'));
    ConditionalEliminationStep (set conds) g nid g';
    
    ConditionalEliminationPhase g' (nid', seen', conds') g''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds) g''" |

  (* Can do a step, matches whether optimised or not causing non-determinism
     Need to find a way to negate ConditionalEliminationStep *)
  "\<lbrakk>Step g (nid, seen, conds) (Some (nid', seen', conds'));
    
    ConditionalEliminationPhase g (nid', seen', conds') g'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds) g'" |

  (* Can't do a step but there is a predecessor we can backtrace to *)
  "\<lbrakk>Step g (nid, seen, conds) None;
    Some nid' = pred g nid;
    seen' = {nid} \<union> seen;
    ConditionalEliminationPhase g (nid', seen', conds) g'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds) g'" |

  (* Can't do a step and have no predecessors do terminate *)
  "\<lbrakk>Step g (nid, seen, conds) None;
    None = pred g nid\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds) g"


code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) 
  ConditionalEliminationPhase .

inductive ConditionalEliminationPhaseWithTrace
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> Conditions) \<Rightarrow> ID list \<Rightarrow> IRGraph \<Rightarrow> ID list \<Rightarrow> Conditions \<Rightarrow> bool" where

  (* Can do a step and optimise for the current nid *)
  "\<lbrakk>Step g (nid, seen, conds) (Some (nid', seen', conds'));
    ConditionalEliminationStep (set conds) g nid g';
    
    ConditionalEliminationPhaseWithTrace g' (nid', seen', conds') (nid # t) g'' t' conds''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds) t g'' t' conds''" |

  (* Can do a step, matches whether optimised or not causing non-determinism
     Need to find a way to negate ConditionalEliminationStep *)
  "\<lbrakk>Step g (nid, seen, conds) (Some (nid', seen', conds'));
    
    ConditionalEliminationPhaseWithTrace g (nid', seen', conds') (nid # t) g' t' conds''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds) t g' t' conds''" |

  (* Can't do a step but there is a predecessor we can backtrace to *)
  "\<lbrakk>Step g (nid, seen, conds) None;
    Some nid' = pred g nid;
    seen' = {nid} \<union> seen;
    ConditionalEliminationPhaseWithTrace g (nid', seen', conds) (nid # t) g' t' conds'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds) t g' t' conds'" |

  (* Can't do a step and have no predecessors do terminate *)
  "\<lbrakk>Step g (nid, seen, conds) None;
    None = pred g nid\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds) t g (nid # t) conds"


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) 
  ConditionalEliminationPhaseWithTrace .


definition exAlwaysDistinct :: "IRGraph" where
  "exAlwaysDistinct = irgraph [
    (0, (StartNode (None) (4)), VoidStamp),
    (1, (ParameterNode (0)), IntegerStamp 32 (1) (2)),
    (2, (ParameterNode (1)), IntegerStamp 32 (3) (4)),
    (3, (IntegerEqualsNode (1) (2)), default_stamp),
    (4, (IfNode (3) (5) (6)), VoidStamp),
    (5, (BeginNode 7), VoidStamp),
    (6, (BeginNode 8), VoidStamp),
    (7, (EndNode), VoidStamp),
    (8, (EndNode), VoidStamp),
    (9, (MergeNode [7, 8] None 11), VoidStamp),
    (10, (ValuePhiNode 10 [1, 2] 9), VoidStamp),
    (11, (ReturnNode ((Some 10)) (None)), default_stamp)]"
values "{g' . ConditionalEliminationPhase exAlwaysDistinct (0, {}, []) g'}"


definition exNeverDistinct :: "IRGraph" where
  "exNeverDistinct = irgraph [
    (0, (StartNode (None) (4)), VoidStamp),
    (1, (ParameterNode (0)), IntegerStamp 32 (1) (1)),
    (2, (ParameterNode (1)), IntegerStamp 32 (1) (1)),
    (3, (IntegerEqualsNode (1) (2)), default_stamp),
    (4, (IfNode (3) (5) (6)), VoidStamp),
    (5, (BeginNode 7), VoidStamp),
    (6, (BeginNode 8), VoidStamp),
    (7, (EndNode), VoidStamp),
    (8, (EndNode), VoidStamp),
    (9, (MergeNode [7, 8] None 11), VoidStamp),
    (10, (ValuePhiNode 10 [1, 2] 9), VoidStamp),
    (11, (ReturnNode ((Some 10)) (None)), default_stamp)]"
values "{g' . ConditionalEliminationPhase exNeverDistinct (0, {}, []) g'}"

definition exImpliesElim :: "IRGraph" where
  "exImpliesElim = irgraph [
    (0, (StartNode (None) (4)), VoidStamp),
    (1, (ParameterNode (0)), default_stamp),
    (2, (ParameterNode (1)), default_stamp),
    (3, (IntegerEqualsNode (1) (2)), default_stamp),
    (4, (IfNode (3) (5) (6)), VoidStamp),
    (5, (BeginNode (9)), VoidStamp),
    (6, (BeginNode (7)), VoidStamp),
    (7, (EndNode), VoidStamp),
    (8, (IntegerLessThanNode (1) (2)), default_stamp),
    (9, (IfNode (8) (10) (11)), default_stamp),
    (10, (BeginNode 12), VoidStamp),
    (11, (BeginNode 13), VoidStamp),
    (12, (EndNode), VoidStamp),
    (13, (EndNode), VoidStamp),
    (14, (MergeNode [12, 13] None 15), VoidStamp),
    (15, (EndNode), VoidStamp),
    (16, (MergeNode [7, 15] None 17), VoidStamp),
    (17, (ReturnNode (Some 1) None), default_stamp)
  ]"
values "{g' . ConditionalEliminationPhase exImpliesElim (0, {}, []) g'}"

(* same as previous but condition is in else so condition is negated -- shouldn't optimize *)
definition exImpliesElimNeg :: "IRGraph" where
  "exImpliesElimNeg = irgraph [
    (0, (StartNode (None) (4)), VoidStamp),
    (1, (ParameterNode (0)), default_stamp),
    (2, (ParameterNode (1)), default_stamp),
    (3, (IntegerEqualsNode (1) (2)), default_stamp),
    (4, (IfNode (3) (6) (5)), VoidStamp),
    (5, (BeginNode (9)), VoidStamp),
    (6, (BeginNode (7)), VoidStamp),
    (7, (EndNode), VoidStamp),
    (8, (IntegerLessThanNode (1) (2)), default_stamp),
    (9, (IfNode (8) (10) (11)), default_stamp),
    (10, (BeginNode 12), VoidStamp),
    (11, (BeginNode 13), VoidStamp),
    (12, (EndNode), VoidStamp),
    (13, (EndNode), VoidStamp),
    (14, (MergeNode [12, 13] None 15), VoidStamp),
    (15, (EndNode), VoidStamp),
    (16, (MergeNode [7, 15] None 17), VoidStamp),
    (17, (ReturnNode (Some 1) None), default_stamp)
  ]"
values "{g' . ConditionalEliminationPhase exImpliesElimNeg (0, {}, []) g'}"


definition ConditionalEliminationTest4_test2Snippet_initial :: IRGraph where
  "ConditionalEliminationTest4_test2Snippet_initial = irgraph [
  (0, (StartNode  (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) 2147483647),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) 2147483647),
  (3, (FrameState []  None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 8), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (EndNode), VoidStamp),
  (9, (MergeNode  [8, 10]  (Some 16) 18), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (BeginNode 15), VoidStamp),
  (12, (BeginNode 10), VoidStamp),
  (13, (IfNode 4 11 12), VoidStamp),
  (14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 1 1),
  (15, (ReturnNode  (Some 14)  None), VoidStamp),
  (16, (FrameState []  None None None), IllegalStamp),
  (17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 2 2),
  (18, (ReturnNode  (Some 17)  None), VoidStamp)
  ]"
values "{g' . ConditionalEliminationPhase ConditionalEliminationTest4_test2Snippet_initial (0, {}, []) g'}"


lemma IfNodeStepE: "g \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h) \<Longrightarrow>
  (\<And>cond tb fb val.
        kind g nid = IfNode cond tb fb \<Longrightarrow>
        nid' = (if val_to_bool val then tb else fb) \<Longrightarrow> 
        g m \<turnstile> kind g cond \<mapsto> val \<Longrightarrow> m' = m)"
  using StepE
  by (smt (verit, best) IfNode Pair_inject stepDet)


lemma ifNodeHasCondEval:
  assumes "(g m h \<turnstile> nid \<leadsto> nid')"
  assumes "kind g nid = IfNode cond t f"
  shows "\<exists> v. (g m \<turnstile> kind g cond \<mapsto> v)"
  by (smt (z3) IRNode.disc(912) IRNode.distinct(871) IRNode.distinct(891) IRNode.distinct(909) IRNode.distinct(923) IRNode.sel(56) StepE assms(1) assms(2) is_EndNode.simps(12) is_sequential_node.simps(18) stutter.cases)


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
    by (simp add: step.RefNode)
  from g1step g2step show ?thesis
    using Step by blast
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
    by (simp add: step.RefNode)
  from g1step g2step show ?thesis
    using Step by blast
qed


lemma ConditionalEliminationStepProof:
  assumes wg: "wff_graph g"
  assumes ws: "wff_stamps g"
  assumes nid: "nid \<in> ids g"
  assumes conds_valid: "\<forall> c \<in> conds . \<exists> v. (g m \<turnstile> c \<mapsto> v) \<and> val_to_bool v"
  assumes ce: "ConditionalEliminationStep conds g nid g'"
  
  shows "\<exists>nid' .(g m h \<turnstile> nid \<leadsto> nid') \<longrightarrow> (g' m h \<turnstile> nid \<leadsto> nid')"
  using ce using assms
proof (induct g nid g' rule: ConditionalEliminationStep.induct)
  case (alwaysDistinctEq g ifcond cond t f x y g' conds)
    then show ?case proof (cases "(g m h \<turnstile> ifcond \<leadsto> nid')")
      case True
      obtain v where v: "g m \<turnstile> kind g cond \<mapsto> v"
        using ifNodeHasCondEval True alwaysDistinctEq.hyps(1)
        by blast
      have "v = IntVal 1 0"
        using tryFoldIntegerEqualsAlwaysDistinct
        using alwaysDistinctEq.prems(2) alwaysDistinctEq.hyps(2) 
              alwaysDistinctEq.hyps(3)
        using v by blast
      then have "False = val_to_bool v"
        by simp
      then show ?thesis 
        using constantConditionValid alwaysDistinctEq.hyps(1) v
        alwaysDistinctEq.hyps(4) 
        by blast
    next
      case False
      then show ?thesis
        by blast
    qed
next
  case (neverDistinctEq g ifcond cond t f x y g')
    then show ?case proof (cases "(g m h \<turnstile> ifcond \<leadsto> nid')")
      case True
      obtain v where v: "g m \<turnstile> kind g cond \<mapsto> v"
        using ifNodeHasCondEval True neverDistinctEq.hyps(1)
        by blast
        (*by (metis IRNode.distinct(921) IRNode.distinct(923) neverDistinctEq.hyps(4) neverDistinctEq.prems(4) ConditionalEliminationStep.cases ids_some replace_usages replace_usages_unchanged)*)
      have "v = IntVal 1 1"
        using tryFoldIntegerEqualsNeverDistinct
        using neverDistinctEq.prems(2) neverDistinctEq.hyps(2) 
              neverDistinctEq.hyps(3)
        using v by blast
      then have "True = val_to_bool v"
        by simp
      then show ?thesis 
        using constantConditionValid neverDistinctEq.hyps(1) v
        neverDistinctEq.hyps(4) 
        by blast
    next
      case False
      then show ?thesis
        by blast
    qed
next
  case (impliesTrue g ifcond cid t f cond conds g')
  obtain condv where condv: "g m \<turnstile> kind g cid \<mapsto> condv"
    using implies.simps impliesTrue.hyps(3) impliesTrue.prems(4)
    using impliesTrue.hyps(2) by auto
  have condvTrue: "val_to_bool condv"
    by (metis condition_implies.intros(2) condv impliesTrue.hyps(2) impliesTrue.hyps(3) impliesTrue.prems(4) implies_true_valid)
  then show ?case 
    using constantConditionValid 
    using impliesTrue.hyps(1) condv impliesTrue.hyps(4)
    by blast
next
  case (impliesFalse g ifcond cid t f cond conds g')
  then show ?case 
  proof (cases "(g m h \<turnstile> ifcond \<leadsto> nid')")
    case True
    obtain condv where condv: "g m \<turnstile> kind g cid \<mapsto> condv"
      using ifNodeHasCondEval impliesFalse.hyps(1)
      using True by blast
    have condvFalse: "False = val_to_bool condv"
      using conds_valid impliesFalse.hyps(3)
      by (metis condition_implies.intros(2) condv impliesFalse.hyps(2) impliesFalse.prems(1) impliesFalse.prems(4) implies_false_valid)
    then show ?thesis
      using constantConditionValid 
      using impliesFalse.hyps(1) condv impliesFalse.hyps(4)
      by blast
  next
    case False
    then show ?thesis
      by auto
  qed
qed


lemma ConditionalEliminationPhaseProof:
  assumes "wff_graph g"
  assumes "wff_stamps g"
  assumes "ConditionalEliminationPhase g (0, {}, []) g'"
  
  shows "\<exists>nid' .(g m h \<turnstile> 0 \<leadsto> nid') \<longrightarrow> (g' m h \<turnstile> 0 \<leadsto> nid')"
proof -
  have "0 \<in> ids g"
    using assms(1) wff_graph.simps by blast
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


lemma replaceUsagesFoldAlwaysDistinct:
  assumes wff: "wff_graph g \<and> wff_stamps g"
  assumes ifkind: "kind g ifcond = (IfNode cond t f)"
  assumes condkind: "kind g cond = (IntegerEqualsNode x y)"
  assumes condeval: "g m \<turnstile> kind g cond \<mapsto> v"
  assumes ran: "alwaysDistinct (stamp g x) (stamp g y)"
  assumes g': "g' = replace_usages ifcond f g"
  shows "\<exists>nid' .(g m h \<turnstile> ifcond \<leadsto> nid') \<longleftrightarrow> (g' m h \<turnstile> ifcond \<leadsto> nid')"
proof -
  have "v = IntVal 1 0"
    using tryFoldIntegerEqualsAlwaysDistinct
    using condeval condkind ran wff by blast
  then have g1step: "g \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    by (metis IfNode condeval ifkind val_to_bool.simps(1))
  have g2step: "g' \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using g' unfolding replace_usages.simps
    by (simp add: step.RefNode)
  from g1step g2step show ?thesis
    using Step by meson
qed

lemma replaceUsagesFoldNeverDistinct:
  assumes wff: "wff_graph g \<and> wff_stamps g"
  assumes ifkind: "kind g ifcond = (IfNode cond t f)"
  assumes condkind: "kind g cond = (IntegerEqualsNode x y)"
  assumes condeval: "g m \<turnstile> kind g cond \<mapsto> v"
  assumes ran: "neverDistinct (stamp g x) (stamp g y)"
  assumes g': "g' = replace_usages ifcond t g"
  shows "\<exists>nid' .(g m h \<turnstile> ifcond \<leadsto> nid') \<longleftrightarrow> (g' m h \<turnstile> ifcond \<leadsto> nid')"
proof -
  have "v = IntVal 1 1"
    using tryFoldIntegerEqualsNeverDistinct
    using condeval condkind ran wff by blast
  then have g1step: "g \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    by (smt IfNode condeval ifkind val_to_bool.simps(1))
  have g2step: "g' \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using g' unfolding replace_usages.simps
    by (simp add: step.RefNode)
  from g1step g2step show ?thesis
    using Step by blast
qed


(*
inductive conditions :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode list \<Rightarrow> bool" where
  "\<lbrakk>kind g nid = IfNode cond tb fb;
    nid' = tb\<rbrakk>
   \<Longrightarrow> conditions g nid nid' [kind g cond]" |
  "\<lbrakk>kind g nid = IfNode cond tb fb;
    nid' = fb\<rbrakk>
   \<Longrightarrow> conditions g nid nid' [NegateNode cond]" |
  "\<lbrakk>\<not>(is_IfNode (kind g nid))\<rbrakk>
   \<Longrightarrow> conditions g nid nid' []"


fun conditions :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode list" where
  "conditions g nid nid' = (case kind g nid of
  IfNode cond tb fb \<Rightarrow> 
    (if (nid' = tb) then [kind g cond] else
    (if (nid' = fb) then [NegateNode cond] else []))
  | _ \<Rightarrow> [])"


inductive exec_logic :: "IRGraph 
      \<Rightarrow> (ID \<times> MapState \<times> DynamicHeap)
      \<Rightarrow> IRNode list
      \<Rightarrow> (ID \<times> MapState \<times> DynamicHeap)
      \<Rightarrow> IRNode list
      \<Rightarrow> bool"
  ("_ \<turnstile> _ > _ \<longrightarrow>* _ > _")
  for g
  where
  "\<lbrakk>g \<turnstile> (nid,m,h) \<rightarrow> (nid',m',h');

    conds = conditions g nid nid';

    cs' = conds @ cs;

    g \<turnstile> (nid',m',h') > cs' \<longrightarrow>* next_state > cs''\<rbrakk> 
    \<Longrightarrow> g \<turnstile> (nid,m,h) > cs \<longrightarrow>* next_state > cs''" |

  "\<lbrakk>\<not>(\<exists>nid' m' h' . (g \<turnstile> (nid,m,h) \<rightarrow> (nid',m',h')))\<rbrakk>
   \<Longrightarrow> g \<turnstile> (nid,m,h) > cs \<longrightarrow>* (nid,m,h) > cs"
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) exec_logic .


definition simple_if :: IRGraph where
  "simple_if = irgraph [
    (12, (ReturnNode (Some 11) None), default_stamp),
    (11, (ValuePhiNode 11 [9,7] 10), default_stamp),
    (10, (MergeNode [5,6] None 12), default_stamp),
    (9, (AddNode 7 8), default_stamp),
    (8, (ParameterNode 2), default_stamp),
    (7, (ParameterNode 1), default_stamp),
    (6, (EndNode), VoidStamp),
    (5, (EndNode), VoidStamp),
    (4, (BeginNode 6), VoidStamp),
    (3, (BeginNode 5), VoidStamp),
    (2, (IfNode 1 3 4), VoidStamp),
    (1, (ParameterNode 0), default_stamp),
    (0, (StartNode None 2), VoidStamp)
  ]"

definition loop :: IRGraph where
  "loop = irgraph [
    (13, (ReturnNode (Some 7) None), default_stamp),
    (12, (LoopEndNode 11), VoidStamp),
    (11, (BeginNode 12), VoidStamp),
    (10, (IfNode 9 11 13), VoidStamp),
    (9, (IntegerLessThanNode 7 6), default_stamp),
    (8, (AddNode 7 5), default_stamp),
    (7, (ValuePhiNode 7 [4,8] 3), default_stamp),
    (6, (ParameterNode 0), default_stamp),
    (5, (ConstantNode (IntVal 32 1)), default_stamp),
    (4, (ConstantNode (IntVal 32 0)), default_stamp),
    (3, (LoopBeginNode [2,12] None None 10), VoidStamp),
    (2, (EndNode), VoidStamp),
    (1, (BeginNode 2), VoidStamp),
    (0, (StartNode None 1), VoidStamp)
  ]"

(*
values "{cs' | s' cs' . simple_if \<turnstile> 
(0, new_map [IntVal 32 0, IntVal 32 1, IntVal 32 2], new_heap) > [] \<longrightarrow>* s' > cs'}"
values "{cs' | s' cs' . loop \<turnstile> 
(0, new_map [IntVal 32 0], new_heap) > [] \<longrightarrow>* s' > cs'}"
values "{cs' | s' cs' . loop \<turnstile> 
(0, new_map [IntVal 32 2], new_heap) > [] \<longrightarrow>* s' > cs'}"

values "{t' | s' t' . simple_if \<turnstile> 
(0, new_map [IntVal 32 0, IntVal 32 1, IntVal 32 2], new_heap) # [] \<longrightarrow>* s' # t'}"
*)

lemma conds_subset:
  assumes "g \<turnstile> (nid, m, h) > cs \<longrightarrow>* (nid', m', h') > cs'"
  shows "set cs \<subseteq> set cs'"
  using assms apply (induct rule: exec_logic.induct)
   apply (metis append_eq_appendI in_set_conv_decomp_last subset_code(1))
  by simp

lemma
  assumes "g \<turnstile> (nid, m, h) > cs \<longrightarrow>* (nid', m', h') > cs'"
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g m \<turnstile> kind g cond \<mapsto> val"
  assumes "val_to_bool val"
  shows "kind g cond \<in> set cs'"
  using assms
proof (induct "(nid, m, h)" cs "(nid', m', h')" cs' rule: "exec_logic.induct")
  case (1 nid' m' h' conds cs' cs cs'')
   have step: "g \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
     using IfNode assms(2) assms(3) assms(4) by presburger
   then have "nid' = tb"
     using stepDet
     by (meson "1.hyps"(1) Pair_inject)
  have conds: "[kind g cond] = conditions g nid tb"
    using conditions.simps assms(2) by simp
  then have "conds = [kind g cond]"
    using "1.hyps"(2)
    using \<open>nid' = tb\<close> by presburger
  then have "kind g cond \<in> set cs'"
    using assms
    by (simp add: "1.hyps"(3) \<open>conds = [kind g cond]\<close>)
  have "set cs' \<subseteq> set cs''"
    using conds_subset
    using "1.hyps"(4) by auto
  then show ?case
    using \<open>kind g cond \<in> set cs'\<close> by auto
next
  case (2 cs)
  have step: "g \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using IfNode assms(2) assms(3) assms(4) by presburger
  then show ?case using assms
    using "2.hyps"(1) by blast
qed



lemma
  assumes "g \<turnstile> (if1, m, h) \<rightarrow> (if2, m', h')"
  assumes "kind g if1 = IfNode cond1 if2 fb1"
  assumes "kind g if2 = IfNode cond2 tb2 fb2"

  assumes "g \<turnstile> kind g cond1 & kind g cond2 \<rightharpoonup> KnownTrue"

  assumes g': "g' = replace_usages if2 tb2 g"
  shows "\<exists>nid' .(g m h \<turnstile> if1 \<leadsto> nid') \<longleftrightarrow> (g' m h \<turnstile> if1 \<leadsto> nid')"
proof -
  have "\<exists>val . (g m \<turnstile> kind g cond1 \<mapsto> val)"
    using StepE 
      assms(1,2) step.IfNode
    sorry
  then show ?thesis sorry
qed


lemma
  assumes "g \<turnstile> (nid, m, h) > cs \<longrightarrow>* (nid'', m'', h'') > cs''"
  assumes "g \<turnstile> (nid'', m'', h'') \<rightarrow> (nid', m', h')"

  assumes "cond1 \<in> set cs"
  assumes "kind g nid'' = IfNode cond2 tb fb"
  assumes "g \<turnstile> cond1 & (kind g cond2) \<rightharpoonup> KnownTrue"
  
  assumes "g m \<turnstile> cond1 \<mapsto> val"
  assumes "val_to_bool val"

  assumes g': "g' = replace_usages nid'' tb2 g"
  shows "\<exists>nid' .(g m h \<turnstile> nid'' \<leadsto> nid') \<longleftrightarrow> (g' m h \<turnstile> nid'' \<leadsto> nid')"
  sorry

(*
lemma
  assumes "p \<turnstile> ((f_s, f_nid, f_m) # f_stk, f_h) | f_trace \<longrightarrow>* ((l_s, l_nid, l_m) # l_stk, l_h) | (f_trace @ trace)"
  assumes "(s, nid, m) \<in> set trace"
  shows "\<exists>xs h xs' h' s' nid' m'. (p \<turnstile> (((s, nid, m)#xs), h) \<longrightarrow> (((s', nid', m')#xs'),h'))"
  using assms 
proof (induct "((f_s, f_nid, f_m) # f_stk, f_h)" f_trace "((l_s, l_nid, l_m) # l_stk, l_h)" "(f_trace @ trace)" rule: "exec.induct")
  case (1 s' nid' m' ys h' l' l)
  then have "set l \<subset> set l'"
    sorry
  from 1 have "set l \<subseteq> set (f_trace @ trace)"
    sorry
  have "set [(f_s, f_nid, f_m)] \<subseteq> set trace"
    sledgehammer
  from 1 show ?case sorry
next
  case (2 l)
  have "(s, nid, m) = (f_s, f_nid, f_m)"
    using "2.hyps"(3) "2.prems" by auto
  then show ?case using "2.hyps"(1)
    by blast
qed
  case (1 p s nid m xs h s' nid' m' ys h' l' l next_state l'')
  then show ?case
    by simp
next
  case (2 p s nid m xs h s' nid' m' ys h' l' l)
  then have "l = f_trace"
    sledgehammer
  then have "trace = [(s, nid, m)]"
    using assms sorry
  then show ?case sorry
qed

lemma
  assumes "p \<turnstile> ([(f_s, f_nid, f_m)], h) | [] \<longrightarrow>* ((l_s, l_nid, l_m) # stk, h') | trace"
  assumes "(s, n, m) \<in> set trace"
  assumes "Some g = p s"
  assumes "kind g n = IfNode cond tb fb"
  assumes "g m \<turnstile> kind g cond \<mapsto> val"
  assumes "val_to_bool val"
  shows "(s, tb, m) \<in> set trace"
  using step.IfNode exec.induct assms

lemma
  assumes "p \<turnstile> ([(f_s, f_nid, f_m)], h) | [] \<longrightarrow>* ((l_s, l_nid, l_m) # stk, h') | trace"
  assumes "(s, n, m) \<in> set trace"
  assumes "Some g = p s"
  assumes "predecessors g n = {ifnode}"
  assumes "kind g ifnode = IfNode cond n fb"
  assumes "g m \<turnstile> kind g cond \<mapsto> val"
  shows "val_to_bool val"
  sorry
*)

lemma
  assumes "g \<turnstile> ifblock >> blockOf g nid"
  assumes "end_kind ifblock = IfNode cond1 tb1 fb1"
  assumes "kind g nid = IfNode cond2 tb2 fb2"
  assumes "g \<turnstile> (kind g cond1) & (kind g cond2) \<rightharpoonup> KnownTrue"

  (* hack to avoid reconsidering negated support *)
assumes "g m \<turnstile> kind g cond1 \<mapsto> bool"
assumes "val_to_bool bool"

assumes "g m \<turnstile> kind g cond2 \<mapsto> condval"

  assumes g': "g' = replace_usages nid tb2 g"
  shows "\<exists>nid' .(g m h \<turnstile> nid \<leadsto> nid') \<longleftrightarrow> (g' m h \<turnstile> nid \<leadsto> nid')"
proof -
  have "val_to_bool condval"
    using assms
    using implies_true_valid by blast
  then show ?thesis using assms replace_if_t
    by blast
qed
*)


end