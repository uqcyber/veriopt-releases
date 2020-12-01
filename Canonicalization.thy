section \<open>Canonicalization optimisation transformations\<close>

theory Canonicalization
  imports 
    IREval
    IRStep
begin
(*
declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]
*)
lemma eval_const_node:
  assumes xn: "kind g x = ConstantNode xv"
  shows "g m \<turnstile> x (kind g x) \<mapsto> (IntVal xv)"
  using xn eval.ConstantNode by simp

lemma eval_add_node: 
  assumes x: "g m \<turnstile> x (kind g x) \<mapsto> IntVal(xv)"
  assumes y: "g m \<turnstile> y (kind g y) \<mapsto> IntVal(yv)"
  shows "g m \<turnstile> z (AddNode x y) \<mapsto> IntVal(xv+yv)"
  using eval.AddNode x y by blast

lemma add_const_nodes:
  assumes xn: "kind g x = ConstantNode xv"
  assumes yn: "kind g y = ConstantNode yv"
  assumes zn: "kind g z = AddNode x y"
  assumes wn: "kind g w = ConstantNode (xv+yv)"
  assumes ez: "g m \<turnstile> z (kind g z) \<mapsto> (IntVal v1)"
  assumes ew: "g m \<turnstile> w (kind g w) \<mapsto> (IntVal v2)"
  shows "v1 = v2"
proof -
  have zv: "g m \<turnstile> z (kind g z) \<mapsto> IntVal(xv+yv)"
    using eval.AddNode eval_const_node xn yn zn by simp
  have wv: "g m \<turnstile> w (kind g w) \<mapsto> IntVal(xv+yv)"
    using eval_const_node wn by auto
  show ?thesis using evalDet zv wv
    using ew ez by blast
qed

text_raw \<open>\Snip{CreateAddNode}%\<close>
fun create_add :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode" where 
  "create_add g x y = 
    (case kind g x of 
      ConstantNode xv \<Rightarrow> 
        (case kind g y of
          ConstantNode yv \<Rightarrow> ConstantNode (xv+yv) | 
          _ \<Rightarrow> if xv = 0 then RefNode y else AddNode x y
        ) |
      _ \<Rightarrow> (case kind g y of
            ConstantNode yv \<Rightarrow> 
              if yv = 0 then RefNode x else AddNode x y |
            _ \<Rightarrow> AddNode x y
           )
    )"
text_raw \<open>\EndSnip\<close>

text_raw \<open>\Snip{AddNodeCreate}%\<close>
lemma add_node_create:
  assumes xv: "g m \<turnstile> x (kind g x) \<mapsto> IntVal(xv)"
  assumes yv: "g m \<turnstile> y (kind g y) \<mapsto> IntVal(yv)"
  shows 
    "(g m \<turnstile> nid (AddNode x y) \<mapsto> IntVal(xv+yv)) \<and>
     (g m \<turnstile> nid (create_add g x y) \<mapsto> IntVal(xv+yv))"
text_raw \<open>\EndSnip\<close>
proof -
  have ae: "g m \<turnstile> nid (AddNode x y) \<mapsto> IntVal(xv+yv)"
    using eval_add_node xv yv by blast
  have refx: "\<forall>zx. (g m \<turnstile> zx (RefNode x) \<mapsto> IntVal xv)"
    using eval.RefNode xv by blast 
  have refy: "\<forall>zy. (g m \<turnstile> zy (RefNode y) \<mapsto> IntVal yv)"
    using eval.RefNode yv by blast 
  have ce: "g m \<turnstile> nid (create_add g x y) \<mapsto> IntVal(xv+yv)"
  proof (cases "\<exists>xvv. kind g x  = ConstantNode xvv")
    case xvvn: True
    have xvv: "kind g x = ConstantNode xv" 
      using ConstantNode evalDet xv eval.ConstantNode xvvn by fastforce
    have cv1: "create_add g x y = 
                (case kind g y of
                 ConstantNode yvv \<Rightarrow> ConstantNode (xv+yvv) | 
                 _ \<Rightarrow> if xv = 0 then RefNode y else AddNode x y
                )"
      using xvv by simp
    thus ?thesis 
    proof (cases "\<exists>yvv. kind g y = ConstantNode yvv")
      case True
        have yvv: "kind g y = ConstantNode yv"
        using ConstantNode evalDet yv eval.ConstantNode True by fastforce
      then show ?thesis
      proof -
        have c_xvv_yvv: "create_add g x y = ConstantNode (xv+yv)" 
          using xvv yvv by simp 
        have cv1: "g m \<turnstile> nid (create_add g x y) \<mapsto> IntVal(xv+yv)"
          using c_xvv_yvv eval.ConstantNode by auto
        then show ?thesis by blast 
      qed
    next
      case not_const_y:False
      have not_const: "\<forall>yvv. kind g y \<noteq> ConstantNode yvv"
        using not_const_y by blast
      have cv_case: "(case kind g y of
                 ConstantNode yvv \<Rightarrow> ConstantNode (xv+yvv) | 
                 _ \<Rightarrow> if xv = 0 then RefNode y else AddNode x y
                ) = (if xv = 0 then RefNode y else AddNode x y)"
        apply (simp add: not_const)
        apply (cases "xv = 0"; auto)
        apply (cases "case IRGraph.snd g y of None \<Rightarrow> NoNode | Some n \<Rightarrow> n"; auto)
        using not_const_y apply auto[1]
        apply (cases "case IRGraph.snd g y of None \<Rightarrow> NoNode | Some n \<Rightarrow> n"; auto)
        using not_const_y by auto
      have cv2: "create_add g x y = (if xv = 0 then RefNode y else AddNode x y)"
          using cv1 xvvn not_const_y xvv cv_case by simp
      then show ?thesis
      proof (cases "xv = 0")
        case True
        then show ?thesis using xvvn xvv not_const_y True cv2 refy by auto 
      next
        case False
        have cvff: "create_add g x y = AddNode x y"
          using False cv2 by auto
        then show ?thesis using xvvn not_const_y False ae by simp
      qed
    qed
  next
    case xnotconst: False
    then show ?thesis 
    proof (cases "\<exists>yvv. kind g y = ConstantNode yvv")
      case yvvn: True
      have yvv: "kind g y = ConstantNode yv"
        using ConstantNode evalDet yv eval.ConstantNode yvvn by fastforce 
      have cv3: "create_add g x y = (if yv = 0 then RefNode x else AddNode x y)"
        using yvv yvvn apply auto
         apply (cases "case IRGraph.snd g x of None \<Rightarrow> NoNode | Some n \<Rightarrow> n"; auto)
        using xnotconst apply auto[1]
        apply (cases "case IRGraph.snd g x of None \<Rightarrow> NoNode | Some n \<Rightarrow> n"; auto)
        using xnotconst by auto
      then show ?thesis using cv3 ae yvv xv eval.RefNode by auto
    next 
      case ynotconst: False
      have yvv: "kind g y \<noteq> ConstantNode yv"
        using ynotconst by simp
      have xvv: "kind g x \<noteq> ConstantNode xv"
        using xnotconst by simp
      have unwrapy: "(case kind g y of 
              ConstantNode yv \<Rightarrow> if yv = 0 then RefNode x else AddNode x y
            | _ \<Rightarrow> AddNode x y) = AddNode x y"
        apply (cases "kind g y"; auto)
        using ynotconst by auto
      have cv4: "create_add g x y = AddNode x y"
        using xvv yvv unwrapy apply auto
        apply (cases "kind g x"; auto)
        using xnotconst apply auto[1]
        using xnotconst by auto
      thus ?thesis using cv4 ae by simp
    qed
  qed
  thus ?thesis
    using ae by blast
qed

text_raw \<open>\Snip{CreateIfNode}%\<close>
fun create_if :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode"
  where 
  "create_if g cond tb fb = 
    (case kind g cond of 
      ConstantNode condv \<Rightarrow> 
        RefNode (if (val_to_bool condv) then tb else fb) |
      _ \<Rightarrow> (if tb = fb then
              RefNode tb
            else 
              IfNode cond tb fb)
    )"
text_raw \<open>\EndSnip\<close>

text_raw \<open>\Snip{Stutter}%\<close>
inductive stutter:: "IRGraph \<Rightarrow> MapState \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool" ("_ _ \<turnstile> _ \<leadsto> _" 55)
  for g where

  Step:
  "\<lbrakk>g \<turnstile> (nid,m) \<rightarrow> (nid',m)\<rbrakk>
   \<Longrightarrow> g m \<turnstile> nid \<leadsto> nid'" |

  Transitive:
  "\<lbrakk>g \<turnstile> (nid,m) \<rightarrow> (nid'',m);
    g m \<turnstile> nid'' \<leadsto> nid'\<rbrakk>
   \<Longrightarrow> g m \<turnstile> nid \<leadsto> nid'"
text_raw \<open>\EndSnip\<close>

inductive eval_uses:: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool"
  for g where

  "\<lbrakk>kind g nid = n;
    inputs_of n = ls;
    nid' \<in> set ls\<rbrakk>
    \<Longrightarrow> eval_uses g nid nid'" |

  "\<lbrakk>eval_uses g nid nid';
    eval_uses g nid' nid''\<rbrakk>
    \<Longrightarrow> eval_uses g nid nid''"

lemma kind_uneffected:
  assumes oldnid: "nid \<in> ids g"
  assumes newnid: "newnid \<notin> ids g"
  assumes modg: "modg = add_node newnid anyk g"
  shows "(kind g nid) = (kind modg nid)"
proof -
  have uneq: "nid \<noteq> newnid"
    using newnid oldnid by blast
  show ?thesis using uneq modg
    apply (simp add: Abs_IRGraph_inverse snd.rep_eq)
    using irgraph_dom
    by (smt finsert_iff fun_upd_same fun_upd_triv fun_upd_twist ids.simps irgraph_dom_inv irgraph_dom_x irgraph_rng notin_fset option.discI snd.rep_eq)
qed

lemma not_in_no_val:
  assumes "nid \<notin> ids g"
  shows "\<not>(g m \<turnstile> nid (kind g nid) \<mapsto> x)"
proof -
  have kind: "(kind g nid) = NoNode"
    using assms irgraph_dom_inv by auto
  show ?thesis using kind
    by auto
qed

lemma add_implies_kind:
  assumes add: "gup = add_node nid k g"
  shows "kind gup nid = k"
proof -
  have isin: "nid \<in> dom (snd gup)"
    using add apply simp
    by (smt domIff dom_fun_upd finsert_iff ids.simps insert_iff irgraph_dom_inv irgraph_dom_x irgraph_rng notin_fset option.discI)
  show ?thesis using isin add apply simp
    by (smt finsert_iff fun_upd_apply ids.simps irgraph_dom_inv irgraph_dom_x irgraph_rng notin_fset option.case_eq_if option.discI option.sel)
qed

lemma eval_independent:
  assumes indep: "\<not>(eval_uses g1 nid nid') \<and> nid \<noteq> nid'"
  assumes not_in: "nid' \<notin> ids g1"
  assumes g2: "g2 = add_node nid' n g1"
  assumes v1: "g1 m \<turnstile> nid (kind g1 nid) \<mapsto> v1"
  shows "g2 m \<turnstile> nid (kind g2 nid) \<mapsto> v1"
proof -
  have nid_in: "nid \<in> ids g1"
    using not_in_no_val v1 by blast
  then have k: "(kind g1 nid) = (kind g2 nid)"
    using kind_uneffected not_in
    using g2 by blast
  show ?thesis
  proof (cases "is_floating_node (kind g2 nid)")
    case True
    then show ?thesis
      apply (cases "kind g2 nid"; auto) sorry
  next
    case False
    then show ?thesis
      using evalFloating k v1 by fastforce
  qed
qed

lemma eval_independent_eq:
  assumes indep: "\<not>(eval_uses g1 nid nid') \<and> nid \<noteq> nid'"
  assumes not_in: "nid' \<notin> ids g1"
  assumes g2: "g2 = add_node nid' n g1"
  assumes v1: "g1 m \<turnstile> nid (kind g1 nid) \<mapsto> v1"
  assumes v2: "g2 m \<turnstile> nid (kind g2 nid) \<mapsto> v2"
  shows "v1 = v2"
  using eval_independent 
  by (meson evalDet g2 indep not_in v1 v2)

lemma indep_implies_value:
  assumes indep: "\<not>(eval_uses g1 nid nid') \<and> nid \<noteq> nid'"
  assumes not_in: "nid' \<notin> ids g1"
  assumes g2: "g2 = add_node nid' n g1"
  assumes v1: "g1 m \<turnstile> nid (kind g1 nid) \<mapsto> v1"
  shows "\<exists> v2 . (g2 m \<turnstile> nid (kind g2 nid) \<mapsto> v2)"
proof -
  obtain v2 where "v2 = v1" by blast
  have "g2 m \<turnstile> nid (kind g2 nid) \<mapsto> v2"
    using \<open>v2 = v1\<close> eval_independent g2 indep not_in v1 by blast
  then show ?thesis using eval_independent
    by blast
qed

(*
lemma eval_independent:
  assumes fresh: "nid' |\<notin>| fmdom g1"
  assumes g2: "g2 = fmupd nid' n g1"
  assumes v1: "g1 m \<turnstile> nid (kind g1 nid) \<mapsto> v1"
  assumes v2: "g2 m \<turnstile> nid (kind g2 nid) \<mapsto> v2"
  shows "v1 = v2"
proof -
  have eq_kind: "kind g1 nid = kind g2 nid"
    using fresh g2 v1 by auto
  have uses: "eval_uses g1 nid = eval_uses g2 nid"

  have uses_g1: "eval_uses g1 nid nid' \<longrightarrow> nid' |\<in>| fmdom g1"

  have uses_g2: "eval_uses g2 nid nid' \<longrightarrow> nid' |\<in>| fmdom g1"

  show ?thesis
  proof (induction "kind g1 nid")
*)


(*
lemma in_int_val:
  assumes "nid \<in> ids g"
  shows "g m \<turnstile> nid (kind g nid) \<mapsto> IntVal x"
proof -
  have kind: "(kind g nid) \<noteq> NoNode"
    using assms irgraph_dom_x kind.simps apply simp
    sorry
  show ?thesis using kind sorry
qed
*)

lemma we_can_do_this:
  assumes "\<not>(\<exists> val . kind g nid = ConstantNode val)"
  shows "(case kind g nid of ConstantNode condv \<Rightarrow> a | _ \<Rightarrow> b) = b"
  apply (cases "kind g nid"; auto) using assms
  by simp

text_raw \<open>\Snip{IfNodeCreate}%\<close>
lemma if_node_create:
  assumes cv: "g m \<turnstile> cond (kind g cond) \<mapsto> IntVal cv"
  assumes fresh: "nid \<notin> ids g" 
  assumes gif: "gif = add_node nid (IfNode cond tb fb) g"
  assumes gcreate: "gcreate = add_node nid (create_if g cond tb fb) g"
  assumes indep: "\<not>(eval_uses g cond nid)"
  shows "\<exists>nid'. (gif m \<turnstile> nid \<leadsto> nid') \<and> 
                (gcreate m \<turnstile> nid \<leadsto> nid')"
text_raw \<open>\EndSnip\<close>

proof (cases "\<exists> val . kind g cond = ConstantNode val")
  case True
  show ?thesis
  proof -
    obtain val where val: "kind g cond = ConstantNode val"
      using True by blast
    have cond_exists: "cond \<in> ids g"
      using not_in_no_val
      using cv by blast
    have if_cv: "gif m \<turnstile> cond (kind gif cond) \<mapsto> IntVal val"
      using True eval.ConstantNode gif fresh
      using kind_uneffected cond_exists
      using val by presburger
    have if_step: "gif \<turnstile> (nid,m) \<rightarrow> (if val_to_bool val then tb else fb,m)"
    proof -
      have if_kind: "kind gif nid = IfNode cond tb fb"
        using gif add_implies_kind
        by blast
      show ?thesis using step.IfNode if_kind if_cv 
        by blast
    qed
    have create_step: "gcreate \<turnstile> (nid,m) \<rightarrow> (if val_to_bool val then tb else fb,m)"
    proof -
      have create_kind: "kind gcreate nid = create_if g cond tb fb"
        using gcreate add_implies_kind
        by blast
      have create_fun: "create_if g cond tb fb = RefNode (if val_to_bool val then tb else fb)"
        using True create_kind val by simp 
      show ?thesis using step.RefNode create_kind create_fun if_cv 
        by simp
    qed
    show ?thesis using Step create_step if_step by blast
  qed
next
  case not_const: False
  obtain nid' where "nid' = (if val_to_bool cv then tb else fb)"
    by blast
  have nid_eq: "(gif \<turnstile> (nid,m) \<rightarrow> (nid',m)) \<and> (gcreate \<turnstile> (nid,m) \<rightarrow> (nid',m))"
  proof -
    have nid': "nid' = (if val_to_bool cv then tb else fb)"
      by (simp add: \<open>nid' = (if val_to_bool cv then tb else fb)\<close>)
    have gif_kind: "kind gif nid = IfNode cond tb fb"
      using add_implies_kind gif
      by blast
    have "nid \<noteq> cond"
      using cv fresh not_in_no_val by blast
    obtain cv2 where cv2: "gif m \<turnstile> cond (kind gif cond) \<mapsto> cv2" 
      using indep_implies_value
      using \<open>nid \<noteq> cond\<close> cv gif indep
      using fresh by blast
    then have "IntVal cv = cv2"
      using indep eval_independent_eq gif cv
      using \<open>nid \<noteq> cond\<close>
      using fresh by blast
    then have eval_gif: "(gif \<turnstile> (nid,m) \<rightarrow> (nid',m))"
      using step.IfNode gif_kind nid' cv2 by blast
    have gcreate_kind: "kind gcreate nid = create_if g cond tb fb"
      using gcreate add_implies_kind
      by blast
    have eval_gcreate: "gcreate \<turnstile> (nid,m) \<rightarrow> (nid',m)"
    proof (cases "tb = fb")
      case True
      have "create_if g cond tb fb = RefNode tb"
        using not_const True by (cases "kind g cond"; auto)
      then show ?thesis
        using True gcreate_kind nid' step.RefNode by auto
    next
      case False
      have "create_if g cond tb fb = IfNode cond tb fb"
        using not_const False by (cases "kind g cond"; auto)
      then show ?thesis
        using eval_gif gcreate gif by auto
    qed
    show ?thesis
      using eval_gcreate eval_gif by blast
  qed
  show ?thesis using nid_eq Step by blast
qed

(*
(cases "kind g y")

      case (ConstantNode yvv)
      then show ?thesis 
      proof -
        have ex: "g m \<turnstile> x (kind g x) \<mapsto> IntVal(xvv)" 


proof (cases "kind g x")
  case "ConstantNode xv"
  then proof (cases "kind g y")
  case ConstantNode yv
  then 
next
  case _
  then
qed
*)

(*
    (case (kind g x) of
      (ConstantNode xv) \<Rightarrow>
        (case (kind g y) of
          (ConstantNode yv) \<Rightarrow> (add_node g (ConstantNode (xv+yv))) |
          _ \<Rightarrow> (create_add g y x)
        ) |
      _ \<Rightarrow> 
        (case (kind g y) of
          (ConstantNode 0) \<Rightarrow> (g, x) |
          _ \<Rightarrow> (add_node g (AddNode x y))
        )
    )"
*)

end