subsection \<open>Graph Rewriting\<close>

theory
  Rewrites
imports
  IRGraphFrames
  Stuttering
begin

fun replace_usages :: "ID \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "replace_usages nid nid' g = replace_node nid (RefNode nid', stamp g nid') g"

lemma replace_usages_effect:
  assumes "g' = replace_usages nid nid' g"
  shows "kind g' nid = RefNode nid'"
  using assms replace_node_lookup replace_usages.simps IRNode.distinct(2069)
  by (metis)

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
  unfolding nextNid.simps
  using ids_finite max_plus_one by blast

fun constantCondition :: "bool \<Rightarrow> ID \<Rightarrow> IRNode \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "constantCondition val nid (IfNode cond t f) g = 
    replace_node nid (IfNode (nextNid g) t f, stamp g nid) 
      (add_node (nextNid g) ((ConstantNode (bool_to_val val)), constantAsStamp (bool_to_val val)) g)" |
  "constantCondition cond nid _ g = g"

lemma constantConditionTrue:
  assumes "kind g ifcond = IfNode cond t f"
  assumes "g' = constantCondition True ifcond (kind g ifcond) g"
  shows "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
proof -
  have if': "kind g' ifcond = IfNode (nextNid g) t f"
    by (metis IRNode.simps(989) assms(1) assms(2) constantCondition.simps(1) replace_node_lookup)
  have "bool_to_val True = (IntVal 1 1)"
    by auto
  have "ifcond \<noteq> (nextNid g)"
    by (metis IRNode.simps(989) assms(1) emptyE ids_some nextNidNotIn)
  then have c': "kind g' (nextNid g) = ConstantNode (IntVal 1 1)"
    using assms(2) replace_node_unchanged
    by (metis DiffI IRNode.distinct(585) \<open>bool_to_val True = IntVal 1 1\<close> add_node_lookup assms(1) constantCondition.simps(1) emptyE insertE not_in_g)
  from if' c' show ?thesis using IfNode
    by (smt (z3) ConstantNode val_to_bool.simps(1))
qed

lemma constantConditionFalse:
  assumes "kind g ifcond = IfNode cond t f"
  assumes "g' = constantCondition False ifcond (kind g ifcond) g"
  shows "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
proof -
  have if': "kind g' ifcond = IfNode (nextNid g) t f"
    by (metis IRNode.simps(989) assms(1) assms(2) constantCondition.simps(1) replace_node_lookup)
  have "bool_to_val False = (IntVal 1 0)"
    by auto
  have "ifcond \<noteq> (nextNid g)"
    by (metis IRNode.simps(989) assms(1) emptyE ids_some nextNidNotIn)
  then have c': "kind g' (nextNid g) = ConstantNode (IntVal 1 0)"
    using assms(2) replace_node_unchanged
    by (metis DiffI IRNode.distinct(585) \<open>bool_to_val False = IntVal 1 0\<close> add_node_lookup assms(1) constantCondition.simps(1) emptyE insertE not_in_g)
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
  by (metis Rep_IRGraph_inverse add_changed add_node.rep_eq ids_some other_node_unchanged replace_node.rep_eq)

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
     (add_node (nextNid g) ((ConstantNode (bool_to_val val)), constantAsStamp (bool_to_val val)) g)"
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
  shows "\<exists>nid' .(g m p h \<turnstile> ifcond \<leadsto> nid') \<longleftrightarrow> (g' m p h \<turnstile> ifcond \<leadsto> nid')"
proof -
  have "g' = g"
    using assms(2) assms(1)
    using constantConditionNoEffect
    by (metis IRNode.collapse(11))
  then show ?thesis by simp
qed

lemma constantConditionValid:
  assumes "kind g ifcond = IfNode cond t f"
  assumes "[g, m, p] \<turnstile> kind g cond \<mapsto> v"
  assumes "const = val_to_bool v"
  assumes "g' = constantCondition const ifcond (kind g ifcond) g"
  shows "\<exists>nid' .(g m p h \<turnstile> ifcond \<leadsto> nid') \<longleftrightarrow> (g' m p h \<turnstile> ifcond \<leadsto> nid')"
proof (cases "const")
  case True
  have ifstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    by (meson IfNode True assms(1) assms(2) assms(3))
  have ifstep': "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using constantConditionTrue
    using True assms(1) assms(4) by presburger
  from ifstep ifstep' show ?thesis
    using StutterStep by blast
next
  case False
  have ifstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    by (meson IfNode False assms(1) assms(2) assms(3))
  have ifstep': "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using constantConditionFalse
    using False assms(1) assms(4) by presburger
  from ifstep ifstep' show ?thesis
    using StutterStep by blast
qed

end