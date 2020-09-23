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
  assumes det: "\<forall>g m x n v1 v2. 
    (g m \<turnstile> x n \<mapsto> v1) \<and> (g m \<turnstile> x n \<mapsto> v2) \<longrightarrow> v1 = v2"
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
  show ?thesis using det zv wv
    using ew ez by blast
qed

text_raw \<open>\snip{CreateAddNode}{\<close>
fun create_add_node :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode" where 
  "create_add_node g x y = 
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
text_raw \<open>}%endsnip\<close>

text_raw \<open>\snip{AddNodeCreate}{\<close>
lemma add_node_create:
  assumes xn: "xn = kind g x"
  assumes yn: "yn = kind g y"
  assumes xv: "g m \<turnstile> x xn \<mapsto> IntVal(xv)"
  assumes yv: "g m \<turnstile> y yn \<mapsto> IntVal(yv)"
  assumes det: "\<forall>g m x n v1 v2. 
    (g m \<turnstile> x n \<mapsto> v1) \<and> (g m \<turnstile> x n \<mapsto> v2) \<longrightarrow> v1 = v2"
  shows "(g m \<turnstile> nid (AddNode x y) \<mapsto> IntVal(xv+yv)) \<and>
  (g m \<turnstile> nid (create_add_node g x y) \<mapsto> IntVal(xv+yv))"
text_raw \<open>}%endsnip\<close>
proof -
  have ae: "g m \<turnstile> nid (AddNode x y) \<mapsto> IntVal(xv+yv)"
    using eval_add_node xn yn xv yv by blast
  have refx: "g m \<turnstile> zx (RefNode x) \<mapsto> IntVal xv"
    using eval.RefNode xn xv by blast 
  have refy: "g m \<turnstile> zy (RefNode y) \<mapsto> IntVal yv"
    using eval.RefNode yn yv by blast 
  have ce: "g m \<turnstile> nid (create_add_node g x y) \<mapsto> IntVal(xv+yv)"
  proof (cases "kind g x  = ConstantNode xvv")
    case xvvn: True
    have xvv: "xvv = xv" 
      using ConstantNode det xn xv eval.ConstantNode xvvn by fastforce 
    thus ?thesis 
    proof (cases "kind g y = ConstantNode yvv")
      case True
      have yvv: "yvv = yv"
        using ConstantNode det yn yv eval.ConstantNode True by fastforce
      then show ?thesis
      proof -
        have xvv_yvv: "g m \<turnstile> nid (ConstantNode (xvv+yvv)) \<mapsto> IntVal(xv+yv)"
          by (simp add: eval.ConstantNode xvv yvv) 
        have c_xvv_yvv: "create_add_node g x y = ConstantNode (xvv+yvv)" 
          using xvvn True by simp  
        have cv1: "g m \<turnstile> nid (create_add_node g x y) \<mapsto> IntVal(xv+yv)"
          using c_xvv_yvv xvv_yvv by simp
        then show ?thesis by blast 
      qed
    next
      case False
      then show ?thesis
      proof -
        have cv2: "create_add_node g x y = (if xvv = 0 then RefNode y else AddNode x y)"
        proof (cases "xvv = 0")
          case True
          then show ?thesis 
            sorry
        next
          case False
          then show ?thesis
            sorry
        qed
        then show ?thesis using cv2 ae xvv yn yv eval.RefNode by auto
      qed
    qed
  next
    case xnotconst: False
    thus ?thesis 
    proof (cases "kind g y = ConstantNode yvv")
      case True
      have yvv: "yvv = yv"
        using ConstantNode True det yn yv eval.ConstantNode by fastforce 
      have cv3: "create_add_node g x y = (if yvv = 0 then RefNode x else AddNode x y)"
        using xnotconst True
        sorry
      then show ?thesis using cv3 ae yvv xn xv eval.RefNode by auto
    next 
      case False
      have cv4: "create_add_node g x y = AddNode x y"
        using xnotconst False 
        sorry
      thus ?thesis using cv4 ae by simp
    qed
  qed
  thus ?thesis
    using ae by blast
qed

text_raw \<open>\snip{CreateIfNode}{\<close>
fun create_if_node :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode"
  where 
  "create_if_node g cond tb fb = 
    (case kind g cond of 
      ConstantNode condv \<Rightarrow> 
        RefNode (if (val_to_bool condv) then tb else fb) |
      _ \<Rightarrow> (if tb = fb then
              RefNode tb
            else 
              IfNode cond tb fb)
    )"
text_raw \<open>}%endsnip\<close>

text_raw \<open>\snip{Stutter}{\<close>
inductive stutter:: "IRGraph \<Rightarrow> MapState \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool" ("_ _ \<turnstile> _ \<leadsto> _" 55)
  for g where

  Step:
  "\<lbrakk>g \<turnstile> (nid,m) \<rightarrow> (nid',m)\<rbrakk>
   \<Longrightarrow> g m \<turnstile> nid \<leadsto> nid'" |

  Transitive:
  "\<lbrakk>g \<turnstile> (nid,m) \<rightarrow> (nid'',m);
    g m \<turnstile> nid'' \<leadsto> nid'\<rbrakk>
   \<Longrightarrow> g m \<turnstile> nid \<leadsto> nid'"
text_raw \<open>}%endsnip\<close>

inductive eval_uses:: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool"
  for g where

  "\<lbrakk>fmlookup g nid = Some n;
    inputs_of n = ls;
    nid' \<in> list_to_set ls\<rbrakk>
    \<Longrightarrow> eval_uses g nid nid'" |

  "\<lbrakk>eval_uses g nid nid';
    eval_uses g nid' nid''\<rbrakk>
    \<Longrightarrow> eval_uses g nid nid''"

lemma eval_independent:
  assumes "\<not>(eval_uses g1 nid nid')"
  assumes g2: "g2 = fmupd nid' n g1"
  assumes v1: "g1 m \<turnstile> nid (kind g1 nid) \<mapsto> v1"
  assumes v2: "g2 m \<turnstile> nid (kind g2 nid) \<mapsto> v2"
  shows "v1 = v2"
  sorry

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

text_raw \<open>\snip{IfNodeCreate}{\<close>
lemma if_node_create:
  assumes cv_wf: "g m \<turnstile> cond (kind g cond) \<mapsto> IntVal cv"
  assumes fresh: "nid |\<notin>| fmdom g" 
  assumes gif: "gif = fmupd nid (IfNode cond tb fb) g"
  assumes gcreate: "gcreate = fmupd nid (create_if_node g cond tb fb) g"
  assumes det: "\<forall>g m x n v1 v2. 
    (g m \<turnstile> x n \<mapsto> v1) \<and> (g m \<turnstile> x n \<mapsto> v2) \<longrightarrow> v1 = v2"
  shows "\<exists>nid'. (gif m \<turnstile> nid \<leadsto> nid') \<and> 
                (gcreate m \<turnstile> nid \<leadsto> nid')"
text_raw \<open>}%endsnip\<close>

proof (cases "kind g cond = ConstantNode val")
  case True
  show ?thesis
  proof -
    have if_cv: "gif m \<turnstile> cond (kind gif cond) \<mapsto> IntVal val"
      using True eval.ConstantNode gif fresh by auto 
    have if_step: "gif \<turnstile> (nid,m) \<rightarrow> (if val_to_bool val then tb else fb,m)"
    proof -
      have if_kind: "kind gif nid = IfNode cond tb fb"
        by (simp add: gif) 
      show ?thesis using step.IfNode if_kind if_cv 
        by blast
    qed
    have create_step: "gcreate \<turnstile> (nid,m) \<rightarrow> (if val_to_bool val then tb else fb,m)"
    proof -
      have create_kind: "kind gcreate nid = create_if_node g cond tb fb"
        using gcreate by simp
      have create_fun: "create_if_node g cond tb fb = RefNode (if val_to_bool val then tb else fb)"
        using True create_kind by simp 
      show ?thesis using step.RefNode create_kind create_fun if_cv 
        by simp
    qed
    show ?thesis using Step create_step if_step by blast
  qed
next
  case not_const: False
  show ?thesis
  proof -
    have if_kind: "kind gif cond = kind g cond"
      using gif fresh cv_wf by auto 
    have if_cv: "gif m \<turnstile> cond (kind gif cond) \<mapsto> IntVal cv"
      using if_kind cv_wf fresh  sorry
    have if_step: "gif \<turnstile> (nid,m) \<rightarrow> (if val_to_bool cv then tb else fb,m)"
      using not_const eval.ConstantNode gif fresh  sorry
    have create_step: "gcreate \<turnstile> (nid,m) \<rightarrow> (if val_to_bool cv then tb else fb,m)"
      sorry
    show ?thesis
      using Step create_step if_step by blast
  qed
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
          _ \<Rightarrow> (create_add_node g y x)
        ) |
      _ \<Rightarrow> 
        (case (kind g y) of
          (ConstantNode 0) \<Rightarrow> (g, x) |
          _ \<Rightarrow> (add_node g (AddNode x y))
        )
    )"
*)

end