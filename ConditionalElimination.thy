theory ConditionalElimination
  imports
    IREval
    Stuttering
    CFG
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

lemma join_unequal:
  assumes "joined = (join x_stamp y_stamp)"
  assumes "is_stamp_empty joined"
  shows "\<nexists> x y . x = y \<and> valid_value x_stamp x \<and> valid_value y_stamp y"
  using assms disjoint_empty by auto

fun replace_usages :: "ID \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "replace_usages nid nid' g = replace_node nid (RefNode nid', stamp g nid') g"

lemma replace_usages:
  assumes "nid \<in> ids g"
  assumes "g' = replace_usages nid nid' g"
  shows "kind g' nid = RefNode nid'"
  using assms unfolding replace_usages.simps
  using replace_node_lookup by blast

lemma replace_usages_unchanged:
  assumes "nid \<in> ids g"
  assumes "g' = replace_usages nid nid' g"
  shows "\<forall> n \<in> ids g . n \<noteq> nid \<longrightarrow> kind g n = kind g' n"
  using assms unfolding replace_usages.simps
  by (metis insertE insert_Diff replace_node_unchanged)

lemma
  assumes "(g m h \<turnstile> nid \<leadsto> nid')"
  shows "\<forall> inter. (g \<turnstile> (nid, m, h) \<rightarrow> (inter, m, h)) \<longrightarrow> (g m h \<turnstile> nid \<leadsto> inter)"
  using Step by auto

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

(*
inductive conditionalElimination :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "\<lbrakk>wff_graph g;
    wff_stamps g;
    g' = Predicate.the (nElim g nid)
    \<rbrakk> \<Longrightarrow> conditionalElimination g g'"

code_pred [show_modes] conditionalElimination .
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool) conditionalElimination .

fun elimOne :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRGraph" where
  "elimOne g nid = Predicate.the (nElim g nid)"

fun hasElim :: "IRGraph \<Rightarrow> ID \<Rightarrow> bool" where
  "hasElim g nid = (\<not>(Predicate.is_empty (nElim g nid)))"

fun eliminable :: "IRGraph \<Rightarrow> ID list \<Rightarrow> ID list" where
  "eliminable g nids = filter (hasElim g) nids"

fun hdOr :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "hdOr [] d = d" |
  "hdOr (x # xs) d = x"

fun conditionalElimination :: "IRGraph \<Rightarrow> IRGraph" where
  "conditionalElimination g = (elimOne g 
    (hdOr (eliminable g (sorted_list_of_set (ids g))) 0)
  )"

lemma
  assumes "(g m h \<turnstile> nid \<leadsto> nid')"
  assumes "kind g nid = IfNode cond t f"
  shows "g m \<turnstile> kind g cond \<mapsto> v"
proof -
  have "\<exists>nid''. (g \<turnstile> (nid, m, h) \<rightarrow> (nid'', m, h))"
    using assms(1) stutter.cases by meson
  then show ?thesis using assms(2) step.IfNode sorry
*)

inductive_cases StepE:
  "g \<turnstile> (nid,m,h) \<rightarrow> (nid',m',h)"

inductive ConditionalEliminationStep :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  alwaysDistinctEq:
  "\<lbrakk>kind g ifcond = (IfNode cond t f);
    kind g cond = (IntegerEqualsNode x y);
    alwaysDistinct (stamp g x) (stamp g y);
    g' = (replace_usages ifcond f g)
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep g ifcond g'" |

  neverDistinctEq:
  "\<lbrakk>kind g ifcond = (IfNode cond t f);
    kind g cond = (IntegerEqualsNode x y);
    neverDistinct (stamp g x) (stamp g y);
    g' = (replace_usages ifcond t g)
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep g ifcond g'"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationStep .

inductive ConditionalEliminationPhase :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "\<lbrakk>ConditionalEliminationStep g nid g';
    succs = IRGraph.succ g nid;
    length succs > 0;
    nid' = succs!0;
    ConditionalEliminationPhase g' nid' g''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g nid g''" |

  "\<lbrakk>succs = IRGraph.succ g nid;
    length succs > 0;
    nid' = succs!0;
    ConditionalEliminationPhase g nid' g''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g nid g''" |

  "\<lbrakk>succs = IRGraph.succ g nid;
    length succs \<le> 0\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g nid g"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationPhase .

    

lemma IfNodeStepE: "g \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h) \<Longrightarrow>
  (\<And>cond tb fb val.
        kind g nid = IfNode cond tb fb \<Longrightarrow>
        nid' = (if val_to_bool val then tb else fb) \<Longrightarrow> 
        g m \<turnstile> kind g cond \<mapsto> val \<Longrightarrow> m' = m)"
  using StepE
  by (smt (verit, best) IfNode Pair_inject stepDet)

(*
lemma ifNodeHasCondEval:
  assumes "(g m h \<turnstile> nid \<leadsto> nid')"
  assumes "kind g nid = IfNode cond t f"
  shows "g m \<turnstile> kind g cond \<mapsto> v"
proof -
  obtain nid'' where step: "(g \<turnstile> (nid, m, h) \<rightarrow> (nid'', m, h))"
    using assms(1) stutter.cases by meson
  have "nid'' = t \<or> nid'' = f"
    by (smt (z3) IRNode.disc(912) IRNode.distinct(871) IRNode.distinct(891) IRNode.distinct(909) IRNode.distinct(923) IRNode.inject(11) StepE \<open>g \<turnstile> (nid, m, h) \<rightarrow> (nid'', m, h)\<close> assms(2) is_EndNode.simps(12) is_sequential_node.simps(18))
  obtain v where condkind: "g m \<turnstile> kind g cond \<mapsto> v"
    by (smt (z3) IRNode.disc(912) IRNode.distinct(871) IRNode.distinct(891) IRNode.distinct(909) IRNode.distinct(923) IRNode.sel(56) StepE assms(2) is_EndNode.simps(12) is_sequential_node.simps(18) local.step)
  have "nid'' = (if (val_to_bool v) then t else f)"
    by (metis IfNode \<open>g m \<turnstile> kind g cond \<mapsto> v\<close> assms(2) local.step old.prod.inject stepDet)
  then show ?thesis using assms(2) step IfNodeStepE condkind sorry
qed
*)

lemma ifNodeHasCondEval:
  assumes "(g m h \<turnstile> nid \<leadsto> nid')"
  assumes "kind g nid = IfNode cond t f"
  shows "\<exists> v. (g m \<turnstile> kind g cond \<mapsto> v)"
  by (smt (z3) IRNode.disc(912) IRNode.distinct(871) IRNode.distinct(891) IRNode.distinct(909) IRNode.distinct(923) IRNode.sel(56) StepE assms(1) assms(2) is_EndNode.simps(12) is_sequential_node.simps(18) stutter.cases)


lemma ConditionalEliminationStepProof:
  assumes wg: "wff_graph g"
  assumes ws: "wff_stamps g"
  assumes nid: "nid \<in> ids g"
  assumes ce: "ConditionalEliminationStep g nid g'"
  
  shows "\<exists>nid' .(g m h \<turnstile> nid \<leadsto> nid') \<longrightarrow> (g' m h \<turnstile> nid \<leadsto> nid')"
  using ce using assms
proof (induct g nid g' arbitrary: nid rule: ConditionalEliminationStep.induct)
  case (alwaysDistinctEq g ifcond cond t f x y g')
    then show ?case proof (cases "(g m h \<turnstile> nid \<leadsto> nid')")
      case True
      obtain v where v: "g m \<turnstile> kind g cond \<mapsto> v"
        using ifNodeHasCondEval True alwaysDistinctEq.hyps(1)
        by (metis IRNode.distinct(921) IRNode.distinct(923) alwaysDistinctEq.hyps(4) alwaysDistinctEq.prems(4) ConditionalEliminationStep.cases ids_some replace_usages replace_usages_unchanged)
      have "v = IntVal 1 0"
        using tryFoldIntegerEqualsAlwaysDistinct
        using alwaysDistinctEq.prems(2) alwaysDistinctEq.hyps(2) 
              alwaysDistinctEq.hyps(3)
        using v by blast
      then have g1step: "g \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
        by (metis IfNode alwaysDistinctEq.hyps(1) v val_to_bool.simps(1))
      have g2step: "g' \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
        using alwaysDistinctEq.hyps(4) unfolding replace_usages.simps
        by (simp add: step.RefNode)
      from g1step g2step show ?thesis
        using Step
        by (metis alwaysDistinctEq.prems(3) alwaysDistinctEq.prems(4) ConditionalEliminationStep.cases replace_usages step.RefNode)
    next
      case False
      then show ?thesis
        by blast
    qed
next
  case (neverDistinctEq g ifcond cond t f x y g')
    then show ?case proof (cases "(g m h \<turnstile> nid \<leadsto> nid')")
      case True
      obtain v where v: "g m \<turnstile> kind g cond \<mapsto> v"
        using ifNodeHasCondEval True neverDistinctEq.hyps(1)
        by (metis IRNode.distinct(921) IRNode.distinct(923) neverDistinctEq.hyps(4) neverDistinctEq.prems(4) ConditionalEliminationStep.cases ids_some replace_usages replace_usages_unchanged)
      have "v = IntVal 1 1"
        using tryFoldIntegerEqualsNeverDistinct
        using neverDistinctEq.prems(2) neverDistinctEq.hyps(2) 
              neverDistinctEq.hyps(3)
        using v by blast
      then have g1step: "g \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
        by (smt (z3) IfNode neverDistinctEq.hyps(1) v val_to_bool.simps(1))
      have g2step: "g' \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
        using neverDistinctEq.hyps(4) unfolding replace_usages.simps
        by (simp add: step.RefNode)
      from g1step g2step show ?thesis
        using Step
        by (metis ConditionalEliminationStep.cases neverDistinctEq.prems(3) neverDistinctEq.prems(4) replace_usages step.RefNode)
    next
      case False
      then show ?thesis
        by blast
    qed
  qed

lemma ConditionalEliminationPhaseProof:
  assumes "wff_graph g"
  assumes "wff_stamps g"
  assumes "ConditionalEliminationPhase g 0 g'"
  
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
qed
qed

definition exAlwaysDistinct :: "IRGraph" where
  "exAlwaysDistinct = irgraph [
    (0, (StartNode (None) (4)), VoidStamp),
    (1, (ParameterNode (0)), IntegerStamp 32 (1) (2)),
    (2, (ParameterNode (1)), IntegerStamp 32 (3) (4)),
    (3, (IntegerEqualsNode (1) (2)), default_stamp),
    (4, (IfNode (3) (5) (6)), VoidStamp),
    (5, (ReturnNode ((Some 1)) (None)), default_stamp),
    (6, (ReturnNode ((Some 2)) (None)), default_stamp)]"

definition exNeverDistinct :: "IRGraph" where
  "exNeverDistinct = irgraph [
    (0, (StartNode (None) (4)), VoidStamp),
    (1, (ParameterNode (0)), IntegerStamp 32 (1) (1)),
    (2, (ParameterNode (1)), IntegerStamp 32 (1) (1)),
    (3, (IntegerEqualsNode (1) (2)), default_stamp),
    (4, (IfNode (3) (5) (6)), VoidStamp),
    (5, (ReturnNode ((Some 1)) (None)), default_stamp),
    (6, (ReturnNode ((Some 2)) (None)), default_stamp)]"

values 1 "{g' | g'. ConditionalEliminationPhase exAlwaysDistinct 0 g'}"
values 1 "{g' | g'. ConditionalEliminationPhase exNeverDistinct 0 g'}"

(*
lemma conditionEliminationValid:
  assumes "\<forall>n \<in> ids g. \<exists> v. (g m \<turnstile> kind g n \<mapsto> v)" (* overly strong, refine *)
  assumes "0 \<in> ids g"
  assumes ce: "g' = conditionalElimination g"
  shows "\<forall>nid. \<exists>nid' .(g m h \<turnstile> nid \<leadsto> nid') \<longleftrightarrow> (g' m h \<turnstile> nid \<leadsto> nid')"
  using ce unfolding conditionalElimination.simps elimOne.simps
    eliminable.simps hasElim.simps 
proof (cases "\<exists> nid \<in> ids g. hasElim g nid")
  case True
  then show ?thesis sorry
next
  case False
  have "(eliminable g (sorted_list_of_set (ids g))) = []"
    unfolding eliminable.simps
    by (metis False equals0D filter_False set_empty set_sorted_list_of_set sorted_list_of_set.infinite)
  then have "g' = Predicate.the (nElim g 0)"
    using hdOr.simps
    by (simp add: ce)
  then show ?thesis using assms(1,2) oneNodeElimValid sledgehammer
qed
*)


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
*)

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


end