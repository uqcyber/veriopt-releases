section \<open>Canonicalization optimisation transformations\<close>

theory Canonicalization
  imports 
    IRGraphFrames
    IRStepObj
    Stuttering
begin


lemma eval_const_node:
  assumes xn: "kind g x = (ConstantNode xv)"
  shows "g m \<turnstile> (kind g x) \<mapsto> xv"
  using xn eval.ConstantNode by simp

lemma eval_add_node: 
  assumes x: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xv"
  assumes y: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yv"
  shows "g m \<turnstile> (AddNode x y) \<mapsto> IntVal b (xv+yv)"
  using eval.AddNode x y by blast

lemma add_const_nodes:
  assumes xn: "kind g x = (ConstantNode (IntVal b xv))"
  assumes yn: "kind g y = (ConstantNode (IntVal b yv))"
  assumes zn: "kind g z = (AddNode x y)"
  assumes wn: "kind g w = (ConstantNode (IntVal b (xv+yv)))"
  assumes ez: "g m \<turnstile> (kind g z) \<mapsto> (IntVal b v1)"
  assumes ew: "g m \<turnstile> (kind g w) \<mapsto> (IntVal b v2)"
  shows "v1 = v2"
proof -
  have zv: "g m \<turnstile> (kind g z) \<mapsto> IntVal b (xv+yv)"
    using eval.AddNode eval_const_node xn yn zn by simp
  have wv: "g m \<turnstile> (kind g w) \<mapsto> IntVal b (xv+yv)"
    using eval_const_node wn by auto
  show ?thesis using evalDet zv wv
    using ew ez by blast
qed

text_raw \<open>\Snip{CreateAddNode}%\<close>
fun create_add :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode" where 
  "create_add g x y = 
    (case (kind g x) of 
      ConstantNode (IntVal b xv) \<Rightarrow> 
        (case (kind g y) of
          ConstantNode (IntVal b yv) \<Rightarrow> ConstantNode (IntVal b (xv+yv)) | 
          _ \<Rightarrow> if xv = 0 then RefNode y else AddNode x y
        ) |
      _ \<Rightarrow> (case (kind g y) of
            ConstantNode (IntVal b yv) \<Rightarrow> 
              if yv = 0 then RefNode x else AddNode x y |
            _ \<Rightarrow> AddNode x y
           )
    )"
text_raw \<open>\EndSnip\<close>

lemma comeon:
  assumes "\<forall>b v. x \<noteq> ConstantNode (IntVal b v)"
  shows "(case x of ConstantNode (IntVal _ _) \<Rightarrow> a | _ \<Rightarrow> b) = b"
  using assms
  (*by (smt IRNode.case_eq_if IRNode.collapse(7) Value.case_eq_if is_IntVal_def)*)
  by (smt IRNode.case_eq_if IRNode.sel(59) Value.case_eq_if Value.collapse(1) is_ConstantNode_def)

lemma comeon2:
  assumes "\<forall>b v. kind g x \<noteq> ConstantNode (IntVal b v)"
  shows "(case kind g x of ConstantNode (IntVal _ _) \<Rightarrow> a | _ \<Rightarrow> b) = b"
  using assms comeon
  by (simp add: comeon)

lemma comeon3:
  assumes "\<forall>b v. x \<noteq> ConstantNode (IntVal b v)"
  assumes "a \<noteq> b \<and> a \<noteq> c"
  shows "(case x of ConstantNode (IntVal _ _) \<Rightarrow> a | ConstantNode _ \<Rightarrow> b | _ \<Rightarrow> c) \<noteq> a"
  using assms comeon
  by (smt IRNode.case_eq_if Value.case_eq_if)

lemma comeon4:
  assumes "\<forall>b v. kind g x \<noteq> ConstantNode (IntVal b v)"
  assumes "a \<noteq> b \<and> a \<noteq> c"
  shows "(case kind g x of ConstantNode (IntVal _ _) \<Rightarrow> a | ConstantNode _ \<Rightarrow> b | _ \<Rightarrow> c) \<noteq> a"
  using assms comeon3
  by (simp add: comeon3)

lemma comeon5:
  assumes "\<forall>b v. kind g x \<noteq> ConstantNode (IntVal b v)"
  shows "(case kind g x of ConstantNode (IntVal _ _) \<Rightarrow> a | ConstantNode _ \<Rightarrow> b | _ \<Rightarrow> c) = b
        \<or> (case kind g x of ConstantNode (IntVal _ _) \<Rightarrow> a | ConstantNode _ \<Rightarrow> b | _ \<Rightarrow> c) = c"
  using assms comeon3
  by (smt IRNode.case_eq_if Value.case_eq_if)

text_raw \<open>\Snip{AddNodeCreate}%\<close>
lemma add_node_create:
  assumes xv: "g m \<turnstile> (kind g x) \<mapsto> IntVal b xv"
  assumes yv: "g m \<turnstile> (kind g y) \<mapsto> IntVal b yv"
  shows 
    "(g m \<turnstile> (AddNode x y) \<mapsto> IntVal b (xv+yv)) \<and>
     (g m \<turnstile> (create_add g x y) \<mapsto> IntVal b (xv+yv))"
text_raw \<open>\EndSnip\<close>
proof -
  let ?P = "(g m \<turnstile> (AddNode x y) \<mapsto> IntVal b (xv+yv))"
  let ?Q = "(g m \<turnstile> (create_add g x y) \<mapsto> IntVal b (xv+yv))"
  have P: ?P
    using xv yv eval.AddNode by simp
  have Q: ?Q
  proof (cases "\<exists>b v. (kind g x) = ConstantNode (IntVal b v)")
    case xconst: True
    then show ?thesis
    proof (cases "\<exists>b v. (kind g y) = ConstantNode (IntVal b v)")
      case yconst: True
      then show ?thesis unfolding create_add.simps 
        using xconst eval.ConstantNode xv yv by auto

    next
      case ynotconst: False
      have "create_add g x y = (if xv = 0 then RefNode y else AddNode x y)"
        unfolding create_add.simps 
        (* bad proof *)
        using xconst ynotconst
        apply (cases "kind g x"; auto)
        apply (cases "kind g y"; auto)
        using yv apply auto[1]
        using xv apply auto[1]
        using xv apply auto[1]
        using xv yv apply auto
      proof -
        let ?x = "ConstantNode (IntVal b yv)"
        let ?a = "ConstantNode (IntVal b (xv + yv))"
        let ?b = "AddNode x y"
        let ?c = "AddNode x y"
        have "?a \<noteq> ?b \<and> ?a \<noteq> ?c" by simp 
        then show "(case kind g y of 
                ?x \<Rightarrow> ?a
              | ConstantNode _ \<Rightarrow> ?b | _ \<Rightarrow> ?c) =
              AddNode x y" using comeon4 ynotconst
          by (smt ConstantNodeE IRNode.case_eq_if IRNode.collapse(7) yv)
        (* end bad *)
      qed
      then show ?thesis unfolding create_add.simps
        apply (cases "xv = 0"; auto)
        using eval.RefNode yv apply simp
        using eval.AddNode xv yv by simp
    qed
  next
    case xnotconst: False
    then show ?thesis
    proof (cases "\<exists>b v. (kind g y) = ConstantNode (IntVal b v)")
      case yconst: True
      have yval: "kind g y = ConstantNode (IntVal b yv)"
        using yv yconst by auto
      have "create_add g x y = (if yv = 0 then RefNode x else AddNode x y)"
        unfolding create_add.simps
        (* bad proof *)
        using yconst yval apply auto
        apply (cases "kind g x"; auto)
        using xnotconst xv apply auto[1]
        apply (cases "kind g x"; auto)
        using xnotconst xv by auto
        (* end bad *)
      then show ?thesis unfolding create_add.simps 
        apply (cases "yv = 0"; auto)
        using eval.RefNode xv apply simp
        using eval.AddNode xv yv by simp
    next
      case ynotconst: False
      (* bad proof *)
      let ?x = "ConstantNode (IntVal b xv)"
      let ?a = "case kind g y of ConstantNode (IntVal b yv) \<Rightarrow> ConstantNode (IntVal b (xv + yv))
     | ConstantNode _ \<Rightarrow> if xv = 0 then RefNode y else AddNode x y
     | _ \<Rightarrow> if xv = 0 then RefNode y else AddNode x y"
      let ?b = "case kind g y of
       ConstantNode (IntVal b yv) \<Rightarrow> if yv = 0 then RefNode x else AddNode x y
       | ConstantNode _ \<Rightarrow> AddNode x y | _ \<Rightarrow> AddNode x y"
      have b_def: "?b = AddNode x y"
        using ynotconst comeon5
        by (smt ConstantNodeE IRNode.case_eq_if IRNode.collapse(7) yv)
      have "create_add g x y = ?b"
        unfolding create_add.simps
        using xnotconst ynotconst
      proof -
        let ?exp = "(case kind g x of ?x \<Rightarrow> ?a | ConstantNode _ \<Rightarrow> ?b | _ \<Rightarrow> ?b)"
        show "?exp = ?b"
          using comeon5 xnotconst
          by (smt ConstantNodeE IRNode.case_eq_if is_ConstantNode_def xv)
      qed
      (* end bad *)
      then have "create_add g x y = AddNode x y"
        by (simp add: b_def)
      then show ?thesis unfolding create_add.simps 
        using eval.AddNode xv yv by simp
    qed
  qed
  from P Q show ?thesis by simp
qed


text_raw \<open>\Snip{CreateIfNode}%\<close>
fun create_if :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode"
  where 
  "create_if g cond tb fb = 
    (case (kind g cond) of 
      ConstantNode condv \<Rightarrow> 
        RefNode (if (val_to_bool condv) then tb else fb) |
      _ \<Rightarrow> (if tb = fb then
              RefNode tb
            else 
              IfNode cond tb fb)
    )"
text_raw \<open>\EndSnip\<close>



lemma add_changed:
  assumes "gup = add_node new k g"
  shows "changeonly {new} g gup"
  using assms unfolding add_node_def changeonly.simps
  using add_node.rep_eq add_node_def kind.rep_eq by auto

lemma disjoint_change:
  assumes "changeonly change g gup"
  assumes "nochange = ids g - change"
  shows "unchanged nochange g gup"
  using assms unfolding changeonly.simps unchanged.simps
  by blast

lemma add_node_unchanged:
  assumes "new \<notin> ids g"
  assumes "nid \<in> ids g"
  assumes "gup = add_node new k g"
  assumes "wff_graph g"
  shows "unchanged (eval_usages g nid) g gup"
proof -
  have "new \<notin> (eval_usages g nid)" using assms
    using eval_usages.simps by blast
  then have "changeonly {new} g gup"
    using assms add_changed by blast
  then show ?thesis using assms add_node_def disjoint_change
    using Diff_insert_absorb by auto
qed

lemma eval_uses_imp:
  "((nid' \<in> ids g \<and> nid = nid')
    \<or> nid' \<in> set (inp g nid)
    \<or> (\<exists>nid'' . eval_uses g nid nid'' \<and> eval_uses g nid'' nid'))
    \<longleftrightarrow> eval_uses g nid nid'"
  using use0 use_inp use_trans
  by (meson eval_uses.simps)

lemma wff_use_ids:
  assumes "wff_graph g"
  assumes "nid \<in> ids g"
  assumes "eval_uses g nid nid'"
  shows "nid' \<in> ids g"
  using assms(3)
proof (induction rule: eval_uses.induct)
  case use0
  then show ?case by simp
next
  case use_inp
  then show ?case
    using assms(1) inp_in_g_wff by blast
next
  case use_trans
  then show ?case by blast
qed

lemma no_external_use:
  assumes "wff_graph g"
  assumes "nid' \<notin> ids g"
  assumes "nid \<in> ids g"
  shows "\<not>(eval_uses g nid nid')"
proof -
  have 0: "nid \<noteq> nid'"
    using assms by blast
  have inp: "nid' \<notin> set (inp g nid)"
    using assms
    using inp_in_g_wff by blast
  have rec_0: "\<nexists>n . n \<in> ids g \<and> n = nid'"
    using assms by blast
  have rec_inp: "\<nexists>n . n \<in> ids g \<and> n \<in> set (inp g nid')"
    using assms(2) inp_in_g by blast
  have rec: "\<nexists>nid'' . eval_uses g nid nid'' \<and> eval_uses g nid'' nid'"
    using wff_use_ids assms(1) assms(2) assms(3) by blast
  from inp 0 rec show ?thesis 
    using eval_uses_imp by blast
qed

(* The following function definition and lemmas designed to hide stamps
   from the definition of if_node_create for the ITP paper which does
   not include stamps *)
fun add_node_fake :: "ID \<Rightarrow> IRNode \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "add_node_fake nid k g = add_node nid (k, VoidStamp) g"
lemma add_node_lookup_fake:
  assumes "gup = add_node_fake nid k g"
  assumes "nid \<notin> ids g"
  shows "kind gup nid = k"
  using add_node_lookup proof (cases "k = NoNode")
  case True
  have "kind g nid = NoNode"
    using assms(2)
    using not_in_g by blast
  then show ?thesis using assms
    by (metis add_node_fake.simps add_node_lookup)
next
  case False
  then show ?thesis
    by (simp add: add_node_lookup assms(1))
qed
lemma add_node_unchanged_fake:
  assumes "new \<notin> ids g"
  assumes "nid \<in> ids g"
  assumes "gup = add_node_fake new k g"
  assumes "wff_graph g"
  shows "unchanged (eval_usages g nid) g gup"
  using add_node_fake.simps add_node_unchanged assms by blast


(*
lemma changeonlyEvalDet:
  assumes "changeonly {} g g'"
  shows "(g m \<turnstile> node \<mapsto> val1) \<Longrightarrow>
   (\<forall> val2. ((g' m \<turnstile> node \<mapsto> val2) \<longrightarrow> val1 = val2))"
  apply (induct rule: eval.induct) using evalDet
  apply blast+
  apply force+
  apply (metis ValueProxyNodeE assms changeonly.simps emptyE eval_in_ids)
  apply (metis AbsNodeE Value.simps(1) assms emptyE eval_in_ids other_node_unchanged)
  apply (metis (no_types, lifting) NegateNode NegateNodeE assms evalDet eval_in_ids ex_in_conv other_node_unchanged)
  apply (smt (z3) AddNode all_not_in_conv assms evalAddNode evalDet eval_in_ids other_node_unchanged)
  apply (smt (z3) SubNode SubNodeE assms empty_iff evalDet eval_in_ids other_node_unchanged)
  using assms unfolding changeonly.simps
  apply (metis MulNodeE Value.inject(1) emptyE eval_in_ids)
  using assms unfolding changeonly.simps
  apply (metis EvalE Value.inject(1) emptyE eval_in_ids)
  using assms unfolding changeonly.simps
  apply (metis EvalE Value.inject(1) emptyE eval_in_ids)
  using assms unfolding changeonly.simps
  apply (metis EvalE Value.inject(1) emptyE eval_in_ids)
  using assms unfolding changeonly.simps
  apply (metis EvalE Value.inject(1) emptyE eval_in_ids)
  using assms unfolding changeonly.simps
  apply (metis EvalE Value.inject(1) emptyE eval_in_ids)
  using assms unfolding changeonly.simps
  apply (metis EvalE Value.inject(1) emptyE eval_in_ids)
  using assms unfolding changeonly.simps
  apply (metis IsNullNodeE Value.inject(3) empty_iff eval_in_ids)
  using assms unfolding changeonly.simps 
  using ConditionalNodeE Value.inject(1) emptyE eval_in_ids sorry (* and so on *)
  

lemma changeonlyStepDet:
  assumes "changeonly {} g g'"
  assumes "wff_graph g"
  shows "(g \<turnstile> (nid,m,h) \<rightarrow> next) \<Longrightarrow>
   (\<forall> next'. ((g' \<turnstile> (nid,m,h) \<rightarrow> next') \<longrightarrow> next = next'))"
proof (induction "(nid, m, h)" "next" rule: "step.induct")
  case (SequentialNode "next")
  have "kind g nid = kind g' nid"
    using assms unfolding changeonly.simps
    by (metis SequentialNode.hyps(1) emptyE ids_some is_sequential_node.simps(44))
  then have "succ g nid = succ g' nid"
    using succ.simps by presburger
  then show ?case using SequentialNode
    by (metis \<open>kind g nid = kind g' nid\<close> step.SequentialNode stepDet)
next
  case (IfNode cond tb fb val "next")
  then have "kind g nid = kind g' nid"
    using assms unfolding changeonly.simps
    by (metis IRNode.simps(965) emptyE ids_some)
  from IfNode have condeq: "kind g cond = kind g' cond"
    by (meson assms changeonly.simps emptyE eval_in_ids)
  have "unchanged (eval_usages g nid) g g'"
    using assms(1) by auto
  then have g'cond: "g' m \<turnstile> kind g' cond \<mapsto> val"
    using IfNode.hyps(2) assms(2) stay_same
    by (smt (verit, best) Diff_empty assms(1) disjoint_change eval_usages.simps mem_Collect_eq unchanged.simps)
  from condeq have "g' m \<turnstile> kind g cond \<mapsto> val"
    using g'cond by presburger
  then show ?case using IfNode
    by (metis \<open>kind g nid = kind g' nid\<close> g'cond step.IfNode stepDet)
next
  case (EndNodes merge i phis inputs vs m')
  then show ?case sorry
next
  case (RefNode nid')
  then show ?case sorry
next
  case (NewInstanceNode f obj nxt h' ref m')
  then show ?case sorry
next
  case (LoadFieldNode f obj nxt ref v m')
  then show ?case sorry
next
  case (StaticLoadFieldNode f nxt v m')
  then show ?case sorry
next
  case (StoreFieldNode f newval uu obj nxt val ref h' m')
  then show ?case sorry
next
  case (StaticStoreFieldNode f newval uv nxt val h' m')
then show ?case sorry
qed


(*

  case (SequentialNode nid next' h)
(*
  have "kind g nid = kind g' nid"
    using assms unfolding changeonly.simps
    by (metis SequentialNode.hyps(1) emptyE ids_some is_sequential_node.simps(44))
  then have prem0: "is_sequential_node (kind g' nid)"
    using SequentialNode.hyps(1) by presburger
  then have prem1: "next = succ g' nid ! 0"
    using SequentialNode.hyps(2) \<open>kind g nid = kind g' nid\<close> succ.simps by presburger
*)
  from SequentialNode show ?case using prem0 prem1 step.SequentialNode sorry
next
  case (IfNode cond tb fb val "next")
  have prem0: "kind g' nid = IfNode cond tb fb"
    by (metis IRNode.simps(965) IfNode.hyps(1) assms(1) ex_in_conv not_in_g other_node_unchanged)
  have prem1: "g' m \<turnstile> kind g' cond \<mapsto> val"
    using changeonlyEvalDet
    by (smt (verit, ccfv_SIG) DiffD2 Diff_empty IfNode.hyps(2) assms(1) assms(2) changeonly.simps eval_usages.simps mem_Collect_eq stay_same unchanged.simps) 
  have "next' = (next, m, h)"
    using IfNode sorry
  then show ?case using prem0 prem1 IfNode.hyps(3) step.IfNode
    by presburger
next
  case (EndNodes merge i phis inputs vs m')
  then show ?case sorry
next
  case (RefNode nid')
  then show ?case sorry
next
  case (NewInstanceNode f obj nxt h' ref m')
  then show ?case sorry
next
  case (LoadFieldNode f obj nxt ref v m')
  then show ?case sorry
next
  case (StaticLoadFieldNode f nxt v m')
  then show ?case sorry
next
  case (StoreFieldNode f newval uu obj nxt val ref h' m')
  then show ?case sorry
next
  case (StaticStoreFieldNode f newval uv nxt val h' m')
  then show ?case sorry
qed*)


lemma
  assumes "nid \<in> ids g"
  assumes "wff_graph g"
  assumes "changeonly {} g g'"
  shows "(g m h \<turnstile> nid \<leadsto> nid') \<longleftrightarrow> (g' m h \<turnstile> nid \<leadsto> nid')"
  using stepDet assms unfolding changeonly.simps
proof -
  have "kind g nid = kind g' nid"
    using assms unfolding changeonly.simps 
    by blast
  then show ?thesis sorry
qed
*)


lemma stuttering_successor:
  assumes "(g \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h))"
  shows "{P'. (g m h \<turnstile> nid \<leadsto> P')} = {nid'} \<union> {nid''. (g m h \<turnstile> nid' \<leadsto> nid'')}"
proof -
  have nextin: "nid' \<in> {P'. (g m h \<turnstile> nid \<leadsto> P')}"
    using assms StutterStep by blast
  have nextsubset: "{nid''. (g m h \<turnstile> nid' \<leadsto> nid'')} \<subseteq> {P'. (g m h \<turnstile> nid \<leadsto> P')}"
    by (metis Collect_mono assms stutter.Transitive)
  have "\<forall>n \<in> {P'. (g m h \<turnstile> nid \<leadsto> P')} . n = nid' \<or> n \<in> {nid''. (g m h \<turnstile> nid' \<leadsto> nid'')}"
    using stepDet
    by (metis (no_types, lifting) Pair_inject assms mem_Collect_eq stutter.simps)
  then show ?thesis
    using insert_absorb mk_disjoint_insert nextin nextsubset by auto
qed

(*
fun create_if_relation :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> ID rel"
  where 
  "create_if_relation g nid cond tb fb = 
    (case (kind g cond) of 
      ConstantNode condv \<Rightarrow> 
        (if (val_to_bool condv) then {(nid, tb)} else {(nid, tb)}) |
      _ \<Rightarrow> (if tb = fb then
              {(nid, tb)}
            else 
              {(nid, nid)})
    )"


lemma if_node_create_bisimulation:
  assumes wff: "wff_graph g"
  assumes cv: "g m \<turnstile> (kind g cond) \<mapsto> cv"
  assumes fresh: "nid \<notin> ids g"
  assumes gif: "gif = add_node_fake nid (IfNode cond tb fb) g"
  assumes gcreate: "gcreate = add_node_fake nid (create_if g cond tb fb) g"

  assumes "\<R> = create_if_relation g nid cond tb tb"
  shows "(\<forall>P'. (gif m h \<turnstile> nid \<leadsto> P') \<longrightarrow> (\<exists>Q' . (gcreate m h \<turnstile> nid \<leadsto> Q') \<and> ((P', Q') \<in> \<R>)))
      \<and> (\<forall>Q'. (gcreate m h \<turnstile> nid \<leadsto> Q') \<longrightarrow> (\<exists>P' . (gif m h \<turnstile> nid \<leadsto> P') \<and> ((P', Q') \<in> \<R>)))"
*)

inductive bisimilar :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool"
  ("_ . _ \<sim> _") for nid where
  "\<lbrakk>\<forall>P'. (g m h \<turnstile> nid \<leadsto> P') \<longrightarrow> (\<exists>Q' . (g' m h \<turnstile> nid \<leadsto> Q'));
    \<forall>Q'. (g' m h \<turnstile> nid \<leadsto> Q') \<longrightarrow> (\<exists>P' . (g m h \<turnstile> nid \<leadsto> P'))\<rbrakk>
  \<Longrightarrow> nid . g \<sim> g'"

lemma equal_closure_bisimilar[simp]:
  assumes "{P'. (g m h \<turnstile> nid \<leadsto> P')} = {P'. (g' m h \<turnstile> nid \<leadsto> P')}"
  shows "nid . g \<sim> g'"
  by (metis assms bisimilar.simps mem_Collect_eq)


lemma if_node_create_bisimulation:
  assumes wff: "wff_graph g"
  assumes cv: "g m \<turnstile> (kind g cond) \<mapsto> cv"
  assumes fresh: "nid \<notin> ids g"
  assumes gif: "gif = add_node_fake nid (IfNode cond tb fb) g"
  assumes gcreate: "gcreate = add_node_fake nid (create_if g cond tb fb) g"

  shows "(\<forall>P'. (gif m h \<turnstile> nid \<leadsto> P') \<longrightarrow> (\<exists>Q' . (gcreate m h \<turnstile> nid \<leadsto> Q')))
      \<and> (\<forall>Q'. (gcreate m h \<turnstile> nid \<leadsto> Q') \<longrightarrow> (\<exists>P' . (gif m h \<turnstile> nid \<leadsto> P')))"

proof (cases "\<exists> val . (kind g cond) = ConstantNode val")
  let ?gif_closure = "{P'. (gif m h \<turnstile> nid \<leadsto> P')}"
  let ?gcreate_closure = "{P'. (gcreate m h \<turnstile> nid \<leadsto> P')}"
  case constantCond: True
  obtain val where val: "(kind g cond) = ConstantNode val"
    using constantCond by blast
  then show ?thesis 
  proof (cases "val_to_bool val")
    case constantTrue: True
    have if_kind: "kind gif nid = (IfNode cond tb fb)"
      using gif add_node_lookup by simp
    have if_cv: "gif m \<turnstile> (kind gif cond) \<mapsto> val"
      by (metis ConstantNodeE add_node_unchanged_fake cv eval_in_ids fresh gif stay_same val wff)
    have "(gif \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h))"
      using step.IfNode if_kind if_cv
      using constantTrue by presburger
    then have gif_closure: "?gif_closure = {tb} \<union> {nid'. (gif m h \<turnstile> tb \<leadsto> nid')}"
      using stuttering_successor by presburger 
    have ref_kind: "kind gcreate nid = (RefNode tb)"
      using gcreate add_node_lookup constantTrue constantCond unfolding create_if.simps
      by (simp add: val)
    have "(gcreate \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h))"
      using step.RefNode ref_kind by simp
    then have gcreate_closure: "?gcreate_closure = {tb} \<union> {nid'. (gcreate m h \<turnstile> tb \<leadsto> nid')}"
      using stuttering_successor
      by auto
    from gif_closure gcreate_closure show ?thesis
      using equal_closure_bisimilar by auto
  next
    case constantFalse: False
    have if_kind: "kind gif nid = (IfNode cond tb fb)"
      using gif add_node_lookup by simp
    have if_cv: "gif m \<turnstile> (kind gif cond) \<mapsto> val"
      by (metis ConstantNodeE add_node_unchanged_fake cv eval_in_ids fresh gif stay_same val wff)
    have "(gif \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h))"
      using step.IfNode if_kind if_cv
      using constantFalse by presburger
    then have gif_closure: "?gif_closure = {fb} \<union> {nid'. (gif m h \<turnstile> fb \<leadsto> nid')}"
      using stuttering_successor by presburger
    have ref_kind: "kind gcreate nid = RefNode fb"
      using add_node_lookup_fake constantFalse fresh gcreate val by force
    then have "(gcreate \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h))"
      using step.RefNode by presburger
    then have gcreate_closure: "?gcreate_closure = {fb} \<union> {nid'. (gcreate m h \<turnstile> fb \<leadsto> nid')}"
      using stuttering_successor by presburger
    from gif_closure gcreate_closure show ?thesis
      using equal_closure_bisimilar by auto
  qed
next
  let ?gif_closure = "{P'. (gif m h \<turnstile> nid \<leadsto> P')}"
  let ?gcreate_closure = "{P'. (gcreate m h \<turnstile> nid \<leadsto> P')}"
  case notConstantCond: False
  then show ?thesis 
  proof (cases "tb = fb")
    case equalBranches: True
     have if_kind: "kind gif nid = (IfNode cond tb fb)"
      using gif add_node_lookup by simp
    have "(gif \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)) \<or> (gif \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h))"
      using step.IfNode if_kind cv apply (cases "val_to_bool cv")
      apply (metis add_node_fake.simps add_node_unchanged eval_in_ids fresh gif stay_same wff)
      by (metis add_node_unchanged_fake eval_in_ids fresh gif stay_same wff)
    then have gif_closure: "?gif_closure = {tb} \<union> {nid'. (gif m h \<turnstile> tb \<leadsto> nid')}"
      using equalBranches
      using stuttering_successor by presburger
    have iref_kind: "kind gcreate nid = (RefNode tb)"
      using gcreate add_node_lookup notConstantCond equalBranches
      unfolding create_if.simps
      by (cases "(kind g cond)"; auto)
    then have "(gcreate \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h))"
      using step.RefNode by simp
    then have gcreate_closure: "?gcreate_closure = {tb} \<union> {nid'. (gcreate m h \<turnstile> tb \<leadsto> nid')}"
      using stuttering_successor by presburger
    from gif_closure gcreate_closure show ?thesis
      by auto
  next
    case uniqueBranches: False
    let ?tb_closure = "{tb} \<union> {nid'. (gif m h \<turnstile> tb \<leadsto> nid')}"
    let ?fb_closure = "{fb} \<union> {nid'. (gif m h \<turnstile> fb \<leadsto> nid')}"
     have if_kind: "kind gif nid = (IfNode cond tb fb)"
      using gif add_node_lookup by simp
    have if_step: "(gif \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)) \<or> (gif \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h))"
      using step.IfNode if_kind cv apply (cases "val_to_bool cv")
      apply (metis add_node_fake.simps add_node_unchanged eval_in_ids fresh gif stay_same wff)
      by (metis add_node_unchanged_fake eval_in_ids fresh gif stay_same wff)
    then have gif_closure: "?gif_closure = ?tb_closure \<or> ?gif_closure = ?fb_closure"
      using stuttering_successor by presburger
    have gc_kind: "kind gcreate nid = (IfNode cond tb fb)"
      using gcreate add_node_lookup notConstantCond uniqueBranches
      unfolding create_if.simps
      by (cases "(kind g cond)"; auto)
    then have "(gcreate \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)) \<or> (gcreate \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h))"
      by (metis add_node_lookup_fake fresh gcreate gif if_step)
    then have gcreate_closure: "?gcreate_closure = ?tb_closure \<or> ?gcreate_closure = ?fb_closure"
      by (metis add_node_lookup_fake fresh gc_kind gcreate gif gif_closure)
    from gif_closure gcreate_closure show ?thesis
      by auto
  qed
qed


text_raw \<open>\Snip{IfNodeCreate}%\<close>
lemma if_node_create:
  assumes wff: "wff_graph g"
  assumes cv: "g m \<turnstile> (kind g cond) \<mapsto> cv"
  assumes fresh: "nid \<notin> ids g"
  assumes gif: "gif = add_node_fake nid (IfNode cond tb fb) g"
  assumes gcreate: "gcreate = add_node_fake nid (create_if g cond tb fb) g"
  shows "\<exists>nid'. (gif m h \<turnstile> nid \<leadsto> nid') \<and> (gcreate m h \<turnstile> nid \<leadsto> nid')"
text_raw \<open>\EndSnip\<close>
proof (cases "\<exists> val . (kind g cond) = ConstantNode val")
  case True
  show ?thesis
  proof -
    obtain val where val: "(kind g cond) = ConstantNode val"
      using True by blast
    have cond_exists: "cond \<in> ids g"
      using cv eval_in_ids by auto
    have if_kind: "kind gif nid = (IfNode cond tb fb)"
      using gif add_node_lookup by simp
    have if_cv: "gif m \<turnstile> (kind gif cond) \<mapsto> val"
      using step.IfNode if_kind
      using True eval.ConstantNode gif fresh
      using stay_same cond_exists
      using val
      using add_node.rep_eq kind.rep_eq by auto
    have if_step: "gif \<turnstile> (nid,m,h) \<rightarrow> (if val_to_bool val then tb else fb,m,h)"
    proof -
      show ?thesis using step.IfNode if_kind if_cv 
        by (simp)
    qed
    have create_step: "gcreate \<turnstile> (nid,m,h) \<rightarrow> (if val_to_bool val then tb else fb,m,h)"
    proof -
      have create_kind: "kind gcreate nid = (create_if g cond tb fb)"
        using gcreate add_node_lookup_fake
        using fresh by blast
      have create_fun: "create_if g cond tb fb = RefNode (if val_to_bool val then tb else fb)"
        using True create_kind val by simp 
      show ?thesis using step.RefNode create_kind create_fun if_cv 
        by (simp)
    qed
    then show ?thesis using StutterStep create_step if_step
      by blast
  qed
next
  case not_const: False
  obtain nid' where "nid' = (if val_to_bool cv then tb else fb)"
    by blast
  have nid_eq: "(gif \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)) \<and> (gcreate \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h))"
  proof -
    have indep: "\<not>(eval_uses g cond nid)"
      using no_external_use
      using cv eval_in_ids fresh wff by blast
    have nid': "nid' = (if val_to_bool cv then tb else fb)"
      by (simp add: \<open>nid' = (if val_to_bool cv then tb else fb)\<close>)
    have gif_kind: "kind gif nid = (IfNode cond tb fb)"
      using add_node_lookup_fake gif
      using fresh by blast
    then have "nid \<noteq> cond"
      using cv fresh indep
      using eval_in_ids by blast
    have "unchanged (eval_usages g cond) g gif"
      using gif add_node_unchanged_fake
      using cv eval_in_ids fresh wff by blast
    then obtain cv2 where cv2: "gif m \<turnstile> (kind gif cond) \<mapsto> cv2" 
      using cv gif wff stay_same by blast
    then have "cv = cv2"
      using indep gif cv
      using \<open>nid \<noteq> cond\<close>
      using fresh
      using \<open>unchanged (eval_usages g cond) g gif\<close> evalDet stay_same wff by blast
    then have eval_gif: "(gif \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h))"
      using step.IfNode gif_kind nid' cv2 
      by auto
    have gcreate_kind: "kind gcreate nid = (create_if g cond tb fb)"
      using gcreate add_node_lookup_fake
      using fresh by blast
    have eval_gcreate: "gcreate \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)"
    proof (cases "tb = fb")
      case True
      have "create_if g cond tb fb = RefNode tb"
        using not_const True by (cases "(kind g cond)"; auto)
      then show ?thesis
        using True gcreate_kind nid' step.RefNode
        by (simp)
    next
      case False
      have "create_if g cond tb fb = IfNode cond tb fb"
        using not_const False by (cases "(kind g cond)"; auto)
      then show ?thesis
        using eval_gif gcreate gif
        using IfNode \<open>cv = cv2\<close> cv2 gif_kind nid' by auto
    qed
    show ?thesis
      using eval_gcreate eval_gif StutterStep by blast
  qed
  show ?thesis using nid_eq StutterStep by meson
qed

end