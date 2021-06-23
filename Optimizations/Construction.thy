section \<open>Graph Construction Phase\<close>

theory
  Construction
imports
  Proofs.Bisimulation
  Proofs.IRGraphFrames
begin

lemma add_const_nodes:
  assumes xn: "kind g x = (ConstantNode (IntVal b xv))"
  assumes yn: "kind g y = (ConstantNode (IntVal b yv))"
  assumes zn: "kind g z = (AddNode x y)"
  assumes wn: "kind g w = (ConstantNode (intval_add (IntVal b xv) (IntVal b yv)))"
  assumes val: "intval_add (IntVal b xv) (IntVal b yv) = IntVal b v1"
  assumes ez: "[g, m, p] \<turnstile> (kind g z) \<mapsto> (IntVal b v1)"
  assumes ew: "[g, m, p] \<turnstile> (kind g w) \<mapsto> (IntVal b v2)"
  shows "v1 = v2"
proof -
  have zv: "[g, m, p] \<turnstile> (kind g z) \<mapsto> IntVal b v1"
    using eval.AddNode eval.ConstantNode xn yn zn val plus_Value_def by metis
  have wv: "[g, m, p] \<turnstile> (kind g w) \<mapsto> IntVal b v2"
    using eval.ConstantNode wn ew by blast 
  show ?thesis using evalDet zv wv ew ez
    using ConstantNode val wn by auto
qed

(* these are incorrect with the introduction of accurate addition semantics *)
(* most obviously due to the resultant b being either 32 or 64 *)
lemma add_val_xzero:
  shows "intval_add (IntVal b 0) (IntVal b yv) = (IntVal b yv)"
  unfolding intval_add.simps sorry

lemma add_val_yzero:
  shows "intval_add (IntVal b xv) (IntVal b 0) = (IntVal b xv)"
  unfolding intval_add.simps sorry

text_raw \<open>\Snip{CreateAddNode}%\<close>
fun create_add :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode" where 
  "create_add g x y = 
    (case (kind g x) of 
      ConstantNode (IntVal b xv) \<Rightarrow> 
        (case (kind g y) of
          ConstantNode (IntVal b yv) \<Rightarrow> 
            ConstantNode (intval_add (IntVal b xv) (IntVal b yv)) | 
          _ \<Rightarrow> if xv = 0 then RefNode y else AddNode x y
        ) |
      _ \<Rightarrow> (case (kind g y) of
            ConstantNode (IntVal b yv) \<Rightarrow> 
              if yv = 0 then RefNode x else AddNode x y |
            _ \<Rightarrow> AddNode x y
           )
    )"
text_raw \<open>\EndSnip\<close>


text_raw \<open>\Snip{AddNodeCreate}%\<close>
lemma add_node_create:
  assumes xv: "[g, m, p] \<turnstile> (kind g x) \<mapsto> IntVal b xv"
  assumes yv: "[g, m, p] \<turnstile> (kind g y) \<mapsto> IntVal b yv"
  assumes res: "res = intval_add (IntVal b xv) (IntVal b yv)"
  shows 
    "([g, m, p] \<turnstile> (AddNode x y) \<mapsto> res) \<and>
     ([g, m, p] \<turnstile> (create_add g x y) \<mapsto> res)"
text_raw \<open>\EndSnip\<close>
proof -
  let ?P = "([g, m, p] \<turnstile> (AddNode x y) \<mapsto> res)"
  let ?Q = "([g, m, p] \<turnstile> (create_add g x y) \<mapsto> res)"
  have P: ?P
    using xv yv res eval.AddNode plus_Value_def by metis
  have Q: ?Q
  proof (cases "is_ConstantNode (kind g x)")
    case xconst: True
    then show ?thesis
    proof (cases "is_ConstantNode (kind g y)")
      case yconst: True
      have "create_add g x y = ConstantNode res"
        using xconst yconst
        using ConstantNodeE is_ConstantNode_def xv yv res by auto
      then show ?thesis using eval.ConstantNode by simp
    next
      case ynotconst: False
      have "kind g x = ConstantNode (IntVal b xv)"
        using ConstantNodeE xconst
        by (metis is_ConstantNode_def xv)
      then have add_def:
        "create_add g x y = (if xv = 0 then RefNode y else AddNode x y)"
        using xconst ynotconst is_ConstantNode_def
        unfolding create_add.simps
        by (simp split: IRNode.split)
      then show ?thesis
      proof (cases "xv = 0")
        case xzero: True
        have ref: "create_add g x y = RefNode y"
          using xzero add_def 
          by meson
        have refval: "[g, m, p] \<turnstile> RefNode y \<mapsto> IntVal b yv"
          using eval.RefNode yv by simp
        have "res = IntVal b yv"
          using res unfolding xzero add_val_xzero by simp
        then show ?thesis using xzero ref refval by simp
      next
        case xnotzero: False
        then show ?thesis
          using P add_def by presburger
      qed
    qed
next
  case notxconst: False
  then show ?thesis
    proof (cases "is_ConstantNode (kind g y)")
      case yconst: True
      have "kind g y = ConstantNode (IntVal b yv)"
        using ConstantNodeE yconst
        by (metis is_ConstantNode_def yv)
      then have add_def:
        "create_add g x y = (if yv = 0 then RefNode x else AddNode x y)"
        using notxconst yconst is_ConstantNode_def
        unfolding create_add.simps
        by (simp split: IRNode.split)
      then show ?thesis
      proof (cases "yv = 0")
        case yzero: True
        have ref: "create_add g x y = RefNode x"
          using yzero add_def 
          by meson
        have refval: "[g, m, p] \<turnstile> RefNode x \<mapsto> IntVal b xv"
          using eval.RefNode xv by simp
        have "res = IntVal b xv"
          using res unfolding yzero add_val_yzero by simp
        then show ?thesis using yzero ref refval by simp
      next
        case ynotzero: False
        then show ?thesis
          using P add_def by presburger
      qed
      
    next
      case notyconst: False
      have "create_add g x y = AddNode x y"
        using notxconst notyconst is_ConstantNode_def 
        create_add.simps by (simp split: IRNode.split)
      then show ?thesis
        using P by presburger
    qed
qed
  from P Q show ?thesis by simp
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
  assumes "wf_graph g"
  shows "unchanged (eval_usages g nid) g gup"
  using add_node_fake.simps add_node_unchanged assms by blast

lemma dom_add_unchanged:
  assumes "nid \<in> ids g"
  assumes "g' = add_node_fake n k g"
  assumes "nid \<noteq> n"
  shows "nid \<in> ids g'"
  using add_changed assms(1) assms(2) assms(3) by force

lemma preserve_wf:
  assumes wf: "wf_graph g"
  assumes "nid \<notin> ids g"
  assumes closed: "inputs g' nid \<union> succ g' nid \<subseteq> ids g"
  assumes g': "g' = add_node_fake nid k g"
  shows "wf_graph g'"
  using assms unfolding wf_folds
  apply (intro conjI)
      apply (metis dom_add_unchanged)
     apply (metis add_node_unchanged_fake assms(1) kind_unchanged)
  sorry

lemma equal_closure_bisimilar:
  assumes "{P'. (g m p h \<turnstile> nid \<leadsto> P')} = {P'. (g' m p h \<turnstile> nid \<leadsto> P')}"
  shows "nid . g \<sim> g'"
  by (metis assms weak_bisimilar.simps mem_Collect_eq)

lemma wf_size:
  assumes "nid \<in> ids g"
  assumes "wf_graph g"
  assumes "is_AbstractEndNode (kind g nid)"
  shows "card (usages g nid) > 0"
  using assms unfolding wf_folds
  by fastforce

lemma sequentials_have_successors:
  assumes "is_sequential_node n"
  shows "size (successors_of n) > 0"
  using assms by (cases n; auto)

lemma step_reaches_successors_only:
  assumes "(g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h))"
  assumes wf: "wf_graph g"
  shows "nid' \<in> succ g nid \<or> nid' \<in> usages g nid"
  using assms proof (induct "(nid, m, h)" "(nid', m, h)"rule: step.induct)
  case SequentialNode
  then show ?case using sequentials_have_successors
    by (metis nth_mem succ.simps)
next
  case (IfNode cond tb fb val)
  then show ?case using successors_of_IfNode
    by (simp add: IfNode.hyps(1))
next
  case (EndNodes i phis inputs vs)
  have "nid \<in> ids g"
    using assms(1) step_in_ids
    by blast
  then have usage_size: "card (usages g nid) > 0"
    using wf EndNodes(1) wf_size
    by blast
  then have usage_size: "size (sorted_list_of_set (usages g nid)) > 0"
    by (metis length_sorted_list_of_set)
  have "usages g nid \<subseteq> ids g"
    using wf by fastforce
  then have finite_usage: "finite (usages g nid)"
    by (metis bot_nat_0.extremum_strict list.size(3) sorted_list_of_set.infinite usage_size)
  from EndNodes(2) have "nid' \<in> usages g nid"
    unfolding any_usage.simps
    using usage_size finite_usage
    by (metis hd_in_set length_greater_0_conv sorted_list_of_set(1))
  then show ?case
    by simp
next
  case (NewInstanceNode f obj ref)
  then show ?case using successors_of_NewInstanceNode by simp
next
  case (LoadFieldNode f obj ref v)
  then show ?case by simp
next
  case (SignedDivNode x y zero sb v1 v2 v)
  then show ?case by simp
next
  case (SignedRemNode x y zero sb v1 v2 v)
  then show ?case by simp
next
  case (StaticLoadFieldNode f v)
  then show ?case by simp
next
  case (StoreFieldNode f newval uu obj val ref)
  then show ?case by simp
next
  case (StaticStoreFieldNode f newval uv val)
  then show ?case by simp
qed

lemma stutter_closed:
  assumes "g m p h \<turnstile> nid \<leadsto> nid'"
  assumes "wf_graph g"
  shows "\<exists> n \<in> ids g . nid' \<in> succ g n \<or> nid' \<in> usages g n"
  using assms
proof (induct nid nid' rule: stutter.induct)
  case (StutterStep nid nid')
  have "nid \<in> ids g"
    using StutterStep.hyps step_in_ids by blast
  then show ?case using StutterStep step_reaches_successors_only
    by blast
next
  case (Transitive nid nid'' nid')
  then show ?case
    by blast
qed


lemma unchanged_step:
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  assumes wf: "wf_graph g"
  assumes kind: "kind g nid = kind g' nid"
  assumes unchanged: "unchanged (eval_usages g nid) g g'"
  assumes succ: "succ g nid = succ g' nid"
  (*assumes usage: "unchanged (usages g nid) g g'"*)
  shows "g', p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
using assms proof (induct "(nid, m, h)" "(nid', m, h)" rule: step.induct)
case SequentialNode
  then show ?case
    by (metis step.SequentialNode)
next
  case (IfNode cond tb fb val)
  then show ?case using stay_same step.IfNode
    by (metis (no_types, lifting) IRNodes.inputs_of_IfNode child_unchanged inputs.elims list.set_intros(1))
next
  case (EndNodes i phis inputs vs)
  then show ?case sorry (* this is going to be a big problem *)
next
  case (NewInstanceNode f obj ref)
  then show ?case using step.NewInstanceNode
    by metis
next
  case (LoadFieldNode f obj ref v)
  have "obj \<in> inputs g nid"
    using LoadFieldNode(1) inputs_of_LoadFieldNode 
    using opt_to_list.simps
    by (simp add: LoadFieldNode.hyps(1))
  then have "unchanged (eval_usages g obj) g g'"
    using unchanged
    using child_unchanged by blast
  then have "[g', m, p] \<turnstile> kind g' obj \<mapsto> ObjRef ref"
    using unchanged wf stay_same
    using LoadFieldNode.hyps(2) by presburger
  then show ?case using step.LoadFieldNode
    by (metis LoadFieldNode.hyps(1) LoadFieldNode.hyps(3) LoadFieldNode.hyps(4) assms(3))
next
  case (SignedDivNode x y zero sb v1 v2 v)
  have "x \<in> inputs g nid"
    using SignedDivNode(1) inputs_of_SignedDivNode
    using opt_to_list.simps
    by (simp add: SignedDivNode.hyps(1))
  then have "unchanged (eval_usages g x) g g'"
    using unchanged
    using child_unchanged by blast
  then have "[g', m, p] \<turnstile> kind g' x \<mapsto> v1"
    using unchanged wf stay_same
    using SignedDivNode.hyps(2) by presburger
  have "y \<in> inputs g nid"
    using SignedDivNode(1) inputs_of_SignedDivNode
    using opt_to_list.simps
    by (simp add: SignedDivNode.hyps(1))
  then have "unchanged (eval_usages g y) g g'"
    using unchanged
    using child_unchanged by blast
  then have "[g', m, p] \<turnstile> kind g' y \<mapsto> v2"
    using unchanged wf stay_same
    using SignedDivNode.hyps(3) by presburger
  then show ?case using step.SignedDivNode
    by (metis SignedDivNode.hyps(1) SignedDivNode.hyps(4) SignedDivNode.hyps(5) \<open>[g', m, p] \<turnstile> kind g' x \<mapsto> v1\<close> kind)
next
  case (SignedRemNode x y zero sb v1 v2 v)
  have "x \<in> inputs g nid"
    using SignedRemNode(1) inputs_of_SignedRemNode
    using opt_to_list.simps
    by (simp add: SignedRemNode.hyps(1))
  then have "unchanged (eval_usages g x) g g'"
    using unchanged
    using child_unchanged by blast
  then have "[g', m, p] \<turnstile> kind g' x \<mapsto> v1"
    using unchanged wf stay_same
    using SignedRemNode.hyps(2) by presburger
  have "y \<in> inputs g nid"
    using SignedRemNode(1) inputs_of_SignedRemNode
    using opt_to_list.simps
    by (simp add: SignedRemNode.hyps(1))
  then have "unchanged (eval_usages g y) g g'"
    using unchanged
    using child_unchanged by blast
  then have "[g', m, p] \<turnstile> kind g' y \<mapsto> v2"
    using unchanged wf stay_same
    using SignedRemNode.hyps(3) by presburger
  then show ?case
    by (metis SignedRemNode.hyps(1) SignedRemNode.hyps(4) SignedRemNode.hyps(5) \<open>[g', m, p] \<turnstile> kind g' x \<mapsto> v1\<close> kind step.SignedRemNode)
next
  case (StaticLoadFieldNode f v)
  then show ?case using step.StaticLoadFieldNode
    by metis
next
  case (StoreFieldNode f newval uu obj val ref)
  have "obj \<in> inputs g nid"
    using StoreFieldNode(1) inputs_of_StoreFieldNode
    using opt_to_list.simps
    by (simp add: StoreFieldNode.hyps(1))
  then have "unchanged (eval_usages g obj) g g'"
    using unchanged
    using child_unchanged by blast
  then have "[g', m, p] \<turnstile> kind g' obj \<mapsto> ObjRef ref"
    using unchanged wf stay_same
    using StoreFieldNode.hyps(3) by presburger
  have "newval \<in> inputs g nid"
    using StoreFieldNode(1) inputs_of_StoreFieldNode
    using opt_to_list.simps
    by (simp add: StoreFieldNode.hyps(1))
  then have "unchanged (eval_usages g newval) g g'"
    using unchanged
    using child_unchanged by blast
  then have "[g', m, p] \<turnstile> kind g' newval \<mapsto> val"
    using unchanged wf stay_same
    using StoreFieldNode.hyps(2) by blast
  then show ?case using step.StoreFieldNode
    by (metis StoreFieldNode.hyps(1) StoreFieldNode.hyps(4) StoreFieldNode.hyps(5) \<open>[g', m, p] \<turnstile> kind g' obj \<mapsto> ObjRef ref\<close> assms(3))
next
  case (StaticStoreFieldNode f newval uv val)
  have "newval \<in> inputs g nid"
    using StoreFieldNode(1) inputs_of_StoreFieldNode
    using opt_to_list.simps
    by (simp add: StaticStoreFieldNode.hyps(1))
  then have "unchanged (eval_usages g newval) g g'"
    using unchanged
    using child_unchanged by blast
  then have "[g', m, p] \<turnstile> kind g' newval \<mapsto> val"
    using unchanged wf stay_same
    using StaticStoreFieldNode.hyps(2) by blast
  then show ?case using step.StaticStoreFieldNode
    by (metis StaticStoreFieldNode.hyps(1) StaticStoreFieldNode.hyps(3) StaticStoreFieldNode.hyps(4) kind)
qed


lemma unchanged_closure:
  assumes "nid \<notin> ids g"
  assumes wf: "wf_graph g \<and> wf_graph g'"
  assumes g': "g' = add_node_fake nid k g"
  assumes "nid' \<in> ids g"
  shows "(g m p h \<turnstile> nid' \<leadsto> nid'') \<longleftrightarrow> (g' m p h \<turnstile> nid' \<leadsto> nid'')" 
    (is "?P \<longleftrightarrow> ?Q")
proof
  assume P: "?P"
  have niddiff: "nid \<noteq> nid'"
    using assms
    by blast
  from P show "?Q" using assms niddiff
  proof (induction rule: stutter.induct)
    case (StutterStep start e)
    have unchanged: "unchanged (eval_usages g start) g g'"
      using StutterStep.prems(4) add_node_unchanged_fake assms(1) g' wf by blast
    have succ_same: "succ g start = succ g' start"
      using StutterStep.prems(4) kind_unchanged succ.simps unchanged by presburger
    have "kind g start = kind g' start"
      by (metis StutterStep.prems(4) add_node_fake.elims add_node_unchanged assms(1) assms(2) g' kind_unchanged)
    then have "g', p \<turnstile> (start, m, h) \<rightarrow> (e, m, h)"
      using unchanged_step wf unchanged succ_same
      by (meson StutterStep.hyps)
    then show ?case
      using stutter.StutterStep by blast
  next
    case (Transitive nid nid'' nid')
    then show ?case
      by (metis add_node_unchanged_fake kind_unchanged step_in_ids stutter.Transitive stutter.cases succ.simps unchanged_step)
  qed
next
  assume Q: "?Q"
  have niddiff: "nid \<noteq> nid'"
    using assms
    by blast
  from Q show "?P" using assms niddiff
  proof (induction rule: stutter.induct)
    case (StutterStep start e)
    have "eval_usages g' start \<subseteq> eval_usages g start"
      using g' eval_usages sorry
    then have unchanged: "unchanged (eval_usages g' start) g' g"
      by (smt (verit, ccfv_SIG) StutterStep.prems(4) add_node_unchanged_fake assms(1) g' subset_iff unchanged.simps wf)
    have succ_same: "succ g start = succ g' start"
      using StutterStep.prems(4) eval_usages_self node_unchanged succ.simps unchanged
      by (metis (no_types, lifting) StutterStep.hyps step_in_ids)
    have "kind g start = kind g' start"
      by (metis StutterStep.prems(4) add_node_fake.elims add_node_unchanged assms(1) assms(2) g' kind_unchanged)
    then have "g, p \<turnstile> (start, m, h) \<rightarrow> (e, m, h)"
      using StutterStep(1) wf unchanged_step unchanged succ_same 
      sorry (* :( *)
    then show ?case
      using stutter.StutterStep by blast
  next
    case (Transitive nid nid'' nid')
    then show ?case
      using add_node_unchanged_fake kind_unchanged step_in_ids stutter.Transitive stutter.cases succ.simps unchanged_step
      sorry
  qed
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

lemma if_node_create_bisimulation:
  fixes h :: FieldRefHeap
  assumes wf: "wf_graph g"
  assumes cv: "[g, m, p] \<turnstile> (kind g cond) \<mapsto> cv"
  assumes fresh: "nid \<notin> ids g"
  assumes closed: "{cond, tb, fb} \<subseteq> ids g"
  assumes gif: "gif = add_node_fake nid (IfNode cond tb fb) g"
  assumes gcreate: "gcreate = add_node_fake nid (create_if g cond tb fb) g"

  shows "nid . gif \<sim> gcreate"

proof -
  have indep: "\<not>(eval_uses g cond nid)"
    using cv eval_in_ids fresh no_external_use wf by blast
  have "kind gif nid = IfNode cond tb fb"
    using gif add_node_lookup by simp
  then have "{cond, tb, fb} = inputs gif nid \<union> succ gif nid"
    using inputs_of_IfNode successors_of_IfNode
    by (metis empty_set inputs.simps insert_is_Un list.simps(15) succ.simps)
  then have wf_gif: "wf_graph gif"
    using closed wf preserve_wf
    using fresh gif by presburger
  have "create_if g cond tb fb = IfNode cond tb fb \<or>
        create_if g cond tb fb = RefNode tb \<or>
        create_if g cond tb fb = RefNode fb"
    by (cases "kind g cond"; auto)
  then have "kind gcreate nid  = IfNode cond tb fb \<or>
        kind gcreate nid = RefNode tb \<or>
        kind gcreate nid = RefNode fb" 
    using gcreate add_node_lookup
    using add_node_lookup_fake fresh by presburger
  then have "inputs gcreate nid \<union> succ gcreate nid \<subseteq> {cond, tb, fb}"
    using inputs_of_IfNode successors_of_IfNode inputs_of_RefNode successors_of_RefNode
    by force
  then have wf_gcreate: "wf_graph gcreate"
    using closed wf preserve_wf fresh gcreate
    by (metis subset_trans)
  have tb_unchanged: "{nid'. (gif m p h \<turnstile> tb \<leadsto> nid')} = {nid'. (gcreate m p h \<turnstile> tb \<leadsto> nid')}"
  proof -
    have "\<not>(\<exists>n \<in> ids g. nid \<in> succ g n \<or> nid \<in> usages g n)"
      using wf
      by (metis (no_types, lifting) fresh mem_Collect_eq subsetD usages.simps wf_folds(1,3))
    then have "nid \<notin> {nid'. (g m p h \<turnstile> tb \<leadsto> nid')}"
      using wf stutter_closed
      by (metis mem_Collect_eq)
    have gif_set: "{nid'. (gif m p h \<turnstile> tb \<leadsto> nid')} = {nid'. (g m p h \<turnstile> tb \<leadsto> nid')}"
      using unchanged_closure fresh wf gif closed wf_gif
      by blast
    have gcreate_set: "{nid'. (gcreate m p h \<turnstile> tb \<leadsto> nid')} = {nid'. (g m p h \<turnstile> tb \<leadsto> nid')}"
      using unchanged_closure fresh wf gcreate closed wf_gcreate
      by blast
    from gif_set gcreate_set show ?thesis by simp
  qed
  have fb_unchanged: "{nid'. (gif m p h \<turnstile> fb \<leadsto> nid')} = {nid'. (gcreate m p h \<turnstile> fb \<leadsto> nid')}"
      proof -
    have "\<not>(\<exists>n \<in> ids g. nid \<in> succ g n \<or> nid \<in> usages g n)"
      using wf
      by (metis (no_types, lifting) fresh mem_Collect_eq subsetD usages.simps wf_folds(1,3))
    then have "nid \<notin> {nid'. (g m p h \<turnstile> fb \<leadsto> nid')}"
      using wf stutter_closed
      by (metis mem_Collect_eq)
    have gif_set: "{nid'. (gif m p h \<turnstile> fb \<leadsto> nid')} = {nid'. (g m p h \<turnstile> fb \<leadsto> nid')}"
      using unchanged_closure fresh wf gif closed wf_gif
      by blast
    have gcreate_set: "{nid'. (gcreate m p h \<turnstile> fb \<leadsto> nid')} = {nid'. (g m p h \<turnstile> fb \<leadsto> nid')}"
      using unchanged_closure fresh wf gcreate closed wf_gcreate
      by blast
    from gif_set gcreate_set show ?thesis by simp
  qed
  show ?thesis
proof (cases "\<exists> val . (kind g cond) = ConstantNode val")
  let ?gif_closure = "{P'. (gif m p h \<turnstile> nid \<leadsto> P')}"
  let ?gcreate_closure = "{P'. (gcreate m p h \<turnstile> nid \<leadsto> P')}"
  case constantCond: True
  obtain val where val: "(kind g cond) = ConstantNode val"
    using constantCond by blast
  then show ?thesis 
  proof (cases "val_to_bool val")
    case constantTrue: True
    have if_kind: "kind gif nid = (IfNode cond tb fb)"
      using gif add_node_lookup by simp
    have if_cv: "[gif, m, p] \<turnstile> (kind gif cond) \<mapsto> val"
      by (metis ConstantNodeE add_node_unchanged_fake cv eval_in_ids fresh gif stay_same val wf)
    have "(gif, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h))"
      using step.IfNode if_kind if_cv
      using constantTrue by presburger
    then have gif_closure: "?gif_closure = {tb} \<union> {nid'. (gif m p h \<turnstile> tb \<leadsto> nid')}"
      using stuttering_successor by presburger 
    have ref_kind: "kind gcreate nid = (RefNode tb)"
      using gcreate add_node_lookup constantTrue constantCond unfolding create_if.simps
      by (simp add: val)
    have "(gcreate, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h))"
      using stepRefNode ref_kind by simp
    then have gcreate_closure: "?gcreate_closure = {tb} \<union> {nid'. (gcreate m p h \<turnstile> tb \<leadsto> nid')}"
      using stuttering_successor
      by auto
    from gif_closure gcreate_closure have "?gif_closure = ?gcreate_closure"
      using tb_unchanged by simp
    then show ?thesis
      using equal_closure_bisimilar by simp
  next
    case constantFalse: False
    have if_kind: "kind gif nid = (IfNode cond tb fb)"
      using gif add_node_lookup by simp
    have if_cv: "[gif, m, p] \<turnstile> (kind gif cond) \<mapsto> val"
      by (metis ConstantNodeE add_node_unchanged_fake cv eval_in_ids fresh gif stay_same val wf)
    have "(gif, p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h))"
      using step.IfNode if_kind if_cv
      using constantFalse by presburger
    then have gif_closure: "?gif_closure = {fb} \<union> {nid'. (gif m p h \<turnstile> fb \<leadsto> nid')}"
      using stuttering_successor by presburger
    have ref_kind: "kind gcreate nid = RefNode fb"
      using add_node_lookup_fake constantFalse fresh gcreate val by force
    then have "(gcreate, p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h))"
      using stepRefNode by presburger
    then have gcreate_closure: "?gcreate_closure = {fb} \<union> {nid'. (gcreate m p h \<turnstile> fb \<leadsto> nid')}"
      using stuttering_successor by presburger
    from gif_closure gcreate_closure have "?gif_closure = ?gcreate_closure"
      using fb_unchanged by simp
    then show ?thesis
      using equal_closure_bisimilar by simp
  qed
next
  let ?gif_closure = "{P'. (gif m p h \<turnstile> nid \<leadsto> P')}"
  let ?gcreate_closure = "{P'. (gcreate m p h \<turnstile> nid \<leadsto> P')}"
  case notConstantCond: False
  then show ?thesis 
  proof (cases "tb = fb")
    case equalBranches: True
     have if_kind: "kind gif nid = (IfNode cond tb fb)"
      using gif add_node_lookup by simp
    have "(gif, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)) \<or> (gif, p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h))"
      using step.IfNode if_kind cv apply (cases "val_to_bool cv")
      apply (metis add_node_fake.simps add_node_unchanged eval_in_ids fresh gif stay_same wf)
      by (metis add_node_unchanged_fake eval_in_ids fresh gif stay_same wf)
    then have gif_closure: "?gif_closure = {tb} \<union> {nid'. (gif m p h \<turnstile> tb \<leadsto> nid')}"
      using equalBranches
      using stuttering_successor by presburger
    have iref_kind: "kind gcreate nid = (RefNode tb)"
      using gcreate add_node_lookup notConstantCond equalBranches
      unfolding create_if.simps
      by (cases "(kind g cond)"; auto)
    then have "(gcreate, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h))"
      using stepRefNode by simp
    then have gcreate_closure: "?gcreate_closure = {tb} \<union> {nid'. (gcreate m p h \<turnstile> tb \<leadsto> nid')}"
      using stuttering_successor by presburger
    from gif_closure gcreate_closure have "?gif_closure = ?gcreate_closure"
      using tb_unchanged by simp
    then show ?thesis
      using equal_closure_bisimilar by simp
  next
    case uniqueBranches: False
    let ?tb_closure = "{tb} \<union> {nid'. (gif m p h \<turnstile> tb \<leadsto> nid')}"
    let ?fb_closure = "{fb} \<union> {nid'. (gif m p h \<turnstile> fb \<leadsto> nid')}"
     have if_kind: "kind gif nid = (IfNode cond tb fb)"
      using gif add_node_lookup by simp
    have if_step: "(gif, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)) \<or> (gif, p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h))"
      using step.IfNode if_kind cv apply (cases "val_to_bool cv")
      apply (metis add_node_fake.simps add_node_unchanged eval_in_ids fresh gif stay_same wf)
      by (metis add_node_unchanged_fake eval_in_ids fresh gif stay_same wf)
    then have gif_closure: "?gif_closure = ?tb_closure \<or> ?gif_closure = ?fb_closure"
      using stuttering_successor by presburger
    have gc_kind: "kind gcreate nid = (IfNode cond tb fb)"
      using gcreate add_node_lookup notConstantCond uniqueBranches
      unfolding create_if.simps
      by (cases "(kind g cond)"; auto)
    then have "(gcreate, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)) \<or> (gcreate, p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h))"
      by (metis add_node_lookup_fake fresh gcreate gif if_step)
    then have gcreate_closure: "?gcreate_closure = ?tb_closure \<or> ?gcreate_closure = ?fb_closure"
      by (metis add_node_lookup_fake fresh gc_kind gcreate gif gif_closure)
    from gif_closure gcreate_closure have "?gif_closure = ?gcreate_closure"
      using tb_unchanged fb_unchanged
      by (metis add_node_lookup_fake fresh gc_kind gcreate gif)
    then show ?thesis
      using equal_closure_bisimilar by simp
  qed
qed
qed


text_raw \<open>\Snip{IfNodeCreate}%\<close>
lemma if_node_create:
  assumes wf: "wf_graph g"
  assumes cv: "[g, m, p] \<turnstile> (kind g cond) \<mapsto> cv"
  assumes fresh: "nid \<notin> ids g"
  assumes gif: "gif = add_node_fake nid (IfNode cond tb fb) g"
  assumes gcreate: "gcreate = add_node_fake nid (create_if g cond tb fb) g"
  shows "\<exists>nid'. (gif m p h \<turnstile> nid \<leadsto> nid') \<and> (gcreate m p h \<turnstile> nid \<leadsto> nid')"
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
    have if_cv: "[gif, m, p] \<turnstile> (kind gif cond) \<mapsto> val"
      using step.IfNode if_kind
      using True eval.ConstantNode gif fresh
      using stay_same cond_exists
      using val
      using add_node.rep_eq kind.rep_eq by auto
    have if_step: "gif, p \<turnstile> (nid,m,h) \<rightarrow> (if val_to_bool val then tb else fb,m,h)"
    proof -
      show ?thesis using step.IfNode if_kind if_cv 
        by (simp)
    qed
    have create_step: "gcreate, p \<turnstile> (nid,m,h) \<rightarrow> (if val_to_bool val then tb else fb,m,h)"
    proof -
      have create_kind: "kind gcreate nid = (create_if g cond tb fb)"
        using gcreate add_node_lookup_fake
        using fresh by blast
      have create_fun: "create_if g cond tb fb = RefNode (if val_to_bool val then tb else fb)"
        using True create_kind val by simp 
      show ?thesis using stepRefNode create_kind create_fun if_cv 
        by (simp)
    qed
    then show ?thesis using StutterStep create_step if_step
      by blast
  qed
next
  case not_const: False
  obtain nid' where "nid' = (if val_to_bool cv then tb else fb)"
    by blast
  have nid_eq: "(gif, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)) \<and> (gcreate, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h))"
  proof -
    have indep: "\<not>(eval_uses g cond nid)"
      using no_external_use
      using cv eval_in_ids fresh wf by blast
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
      using cv eval_in_ids fresh wf by blast
    then obtain cv2 where cv2: "[gif, m, p] \<turnstile> (kind gif cond) \<mapsto> cv2" 
      using cv gif wf stay_same by blast
    then have "cv = cv2"
      using indep gif cv
      using \<open>nid \<noteq> cond\<close>
      using fresh
      using \<open>unchanged (eval_usages g cond) g gif\<close> evalDet stay_same wf by blast
    then have eval_gif: "(gif, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h))"
      using step.IfNode gif_kind nid' cv2 
      by auto
    have gcreate_kind: "kind gcreate nid = (create_if g cond tb fb)"
      using gcreate add_node_lookup_fake
      using fresh by blast
    have eval_gcreate: "gcreate, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)"
    proof (cases "tb = fb")
      case True
      have "create_if g cond tb fb = RefNode tb"
        using not_const True by (cases "(kind g cond)"; auto)
      then show ?thesis
        using True gcreate_kind nid' stepRefNode
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