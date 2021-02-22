section \<open>Canonicalization optimisation transformations\<close>

theory Canonicalization
  imports 
    IRGraphFrames
    IRStepObj
    ConditionalElimination
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

lemma if_stamp_fold:
  assumes wff: "wff_graph g \<and> wff_stamps g"

  assumes cv: "g m \<turnstile> (kind g cond) \<mapsto> cv"
  assumes condkind: "kind g cond = (IntegerEqualsNode x y)"
  assumes emp: "is_stamp_empty (join (stamp g x) (stamp g y))"

  assumes fresh: "nid \<notin> ids g"
  assumes gif: "gif = add_node nid (IfNode cond tb fb, VoidStamp) g"
  assumes gfb: "gfb = add_node nid (RefNode fb, VoidStamp) g"

  shows "\<exists>nid'. (gif m h \<turnstile> nid \<leadsto> nid') \<and> 
                (gfb m h \<turnstile> nid \<leadsto> nid')"
proof -
  have P: "gif \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
  proof -
    have ifkind: "kind gif nid = IfNode cond tb fb"
      using gif add_node_lookup by blast
    then have condgif: "gif m \<turnstile> (kind gif cond) \<mapsto> cv"
      by (metis add_node_unchanged cv eval_in_ids fresh gif kind_unchanged stay_same wff)
    then have "\<not>(val_to_bool cv)"
      using tryFoldIntegerEqualsAlwaysDistinct alwaysDistinct.simps
      by (metis condkind cv emp val_to_bool.simps(1) wff)
    then show ?thesis
      using step.IfNode ifkind condgif by presburger
  qed
  have Q: "gfb \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
  proof -
    have refkind: "kind gfb nid = RefNode fb"
      using gfb add_node_lookup by blast
    then show ?thesis using step.RefNode by simp
  qed
  show ?thesis using P Q using Step by blast
qed

(* The following function definition and lemmas designed to hide stamps
   from the definition of if_node_create for the ITP paper which does
   not include stamps *)
fun add_node_fake :: "ID \<Rightarrow> IRNode \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "add_node_fake nid k g = add_node nid (k, VoidStamp) g"
lemma add_node_lookup_fake:
  "gup = add_node_fake nid k g \<longrightarrow> kind gup nid = k"
  using add_node_lookup by auto
lemma add_node_unchanged_fake:
  assumes "new \<notin> ids g"
  assumes "nid \<in> ids g"
  assumes "gup = add_node_fake new k g"
  assumes "wff_graph g"
  shows "unchanged (eval_usages g nid) g gup"
  using add_node_fake.simps add_node_unchanged assms by blast


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
        by blast
      have create_fun: "create_if g cond tb fb = RefNode (if val_to_bool val then tb else fb)"
        using True create_kind val by simp 
      show ?thesis using step.RefNode create_kind create_fun if_cv 
        by (simp)
    qed
    show ?thesis using Step create_step if_step by blast
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
      by blast
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
      by blast
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
      using eval_gcreate eval_gif Step by blast
  qed
  show ?thesis using nid_eq Step by blast
qed

end