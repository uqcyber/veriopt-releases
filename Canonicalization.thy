section \<open>Canonicalization optimisation transformations\<close>

theory Canonicalization
  imports 
    IRGraphFrames
    IRStepObj
    
begin


lemma eval_const_node:
  assumes xn: "kind g x = Some (ConstantNode xv)"
  shows "g m \<turnstile> x (the (kind g x)) \<mapsto> (IntVal xv)"
  using xn eval.ConstantNode by simp

lemma eval_add_node: 
  assumes x: "g m \<turnstile> x (the (kind g x)) \<mapsto> IntVal(xv)"
  assumes y: "g m \<turnstile> y (the (kind g y)) \<mapsto> IntVal(yv)"
  shows "g m \<turnstile> z (AddNode x y) \<mapsto> IntVal(xv+yv)"
  using eval.AddNode x y by blast

lemma add_const_nodes:
  assumes xn: "kind g x = Some (ConstantNode xv)"
  assumes yn: "kind g y = Some (ConstantNode yv)"
  assumes zn: "kind g z = Some (AddNode x y)"
  assumes wn: "kind g w = Some (ConstantNode (xv+yv))"
  assumes ez: "g m \<turnstile> z (the (kind g z)) \<mapsto> (IntVal v1)"
  assumes ew: "g m \<turnstile> w (the (kind g w)) \<mapsto> (IntVal v2)"
  shows "v1 = v2"
proof -
  have zv: "g m \<turnstile> z (the (kind g z)) \<mapsto> IntVal(xv+yv)"
    using eval.AddNode eval_const_node xn yn zn by simp
  have wv: "g m \<turnstile> w (the (kind g w)) \<mapsto> IntVal(xv+yv)"
    using eval_const_node wn by auto
  show ?thesis using evalDet zv wv
    using ew ez by blast
qed

text_raw \<open>\Snip{CreateAddNode}%\<close>
fun create_add :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode" where 
  "create_add g x y = 
    (case the (kind g x) of 
      ConstantNode xv \<Rightarrow> 
        (case the (kind g y) of
          ConstantNode yv \<Rightarrow> ConstantNode (xv+yv) | 
          _ \<Rightarrow> if xv = 0 then RefNode y else AddNode x y
        ) |
      _ \<Rightarrow> (case the (kind g y) of
            ConstantNode yv \<Rightarrow> 
              if yv = 0 then RefNode x else AddNode x y |
            _ \<Rightarrow> AddNode x y
           )
    )"
text_raw \<open>\EndSnip\<close>


text_raw \<open>\Snip{AddNodeCreate}%\<close>
lemma add_node_create:
  assumes xv: "g m \<turnstile> x (the (kind g x)) \<mapsto> IntVal(xv)"
  assumes yv: "g m \<turnstile> y (the (kind g y)) \<mapsto> IntVal(yv)"
  shows 
    "(g m \<turnstile> nid (AddNode x y) \<mapsto> IntVal(xv+yv)) \<and>
     (g m \<turnstile> nid (create_add g x y) \<mapsto> IntVal(xv+yv))"
  (is "?P \<and> ?Q")
  text_raw \<open>\EndSnip\<close>
proof -
  have P: ?P
    using xv yv eval.AddNode by simp
  have Q: ?Q
  proof (cases "\<exists>v. the (kind g x) = ConstantNode v")
    case xconst: True
    then show ?thesis
    proof (cases "\<exists>v. the (kind g y) = ConstantNode v")
      case yconst: True
      then show ?thesis unfolding create_add.simps 
        using xconst eval.ConstantNode xv yv by auto

    next
      case ynotconst: False
      have "create_add g x y = (if xv = 0 then RefNode y else AddNode x y)"
        using xconst ynotconst create_add.simps sorry
      then show ?thesis unfolding create_add.simps
        apply (cases "xv = 0"; auto)
        using eval.RefNode yv apply simp
        using eval.AddNode xv yv by simp
    qed
  next
    case xnotconst: False
    then show ?thesis
    proof (cases "\<exists>v. the (kind g y) = ConstantNode v")
      case yconst: True
      have "create_add g x y = (if yv = 0 then RefNode x else AddNode x y)"
        using xnotconst yconst create_add.simps sorry
      then show ?thesis unfolding create_add.simps 
        apply (cases "yv = 0"; auto)
        using eval.RefNode xv apply simp
        using eval.AddNode xv yv by simp
    next
      case ynotconst: False
      have "create_add g x y = AddNode x y"
        using xnotconst xnotconst create_add.simps sorry
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
    (case the (kind g cond) of 
      ConstantNode condv \<Rightarrow> 
        RefNode (if (val_to_bool condv) then tb else fb) |
      _ \<Rightarrow> (if tb = fb then
              RefNode tb
            else 
              IfNode cond tb fb)
    )"
text_raw \<open>\EndSnip\<close>

text_raw \<open>\Snip{Stutter}%\<close>
inductive stutter:: "Program \<Rightarrow> Signature \<Rightarrow> MapState \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool" ("_ _ _ \<turnstile> _ \<leadsto> _" 55)
  for g s m where

  Step:
  "\<lbrakk>(g,s) \<turnstile> (nid,m,heap) \<rightarrow> (nid',m,heap)\<rbrakk>
   \<Longrightarrow> g s m \<turnstile> nid \<leadsto> nid'" |

  Transitive:
  "\<lbrakk>(g,s) \<turnstile> (nid,m,heap) \<rightarrow> (nid'',m,heap);
    g s m \<turnstile> nid'' \<leadsto> nid'\<rbrakk>
   \<Longrightarrow> g s m \<turnstile> nid \<leadsto> nid'"
text_raw \<open>\EndSnip\<close>

lemma add_node_lookup:
  assumes "g' = add_node nid k g"
  shows "kind g' nid = Some k"
  using assms unfolding add_node.simps
  using Rep_IRGraph_inverse kind.transfer by auto


text_raw \<open>\Snip{IfNodeCreate}%\<close>
lemma if_node_create:
  assumes cv: "g m \<turnstile> cond (the (kind g cond)) \<mapsto> IntVal cv"
  assumes fresh: "nid \<notin> ids g" 
  assumes gif: "gif = add_node nid (IfNode cond tb fb) g"
  assumes gif_lookup: "gif = gif_prog sig"
  assumes gcreate: "gcreate = add_node nid (create_if g cond tb fb) g"
  assumes gcreate_lookup: "gcreate = gcreate_prog sig"
  assumes indep: "\<not>(eval_uses g cond nid)"
  fixes heap :: Heap
  shows "\<exists>nid'. (gif_prog sig m \<turnstile> nid \<leadsto> nid') \<and> 
                (gcreate_prog sig m \<turnstile> nid \<leadsto> nid')"
text_raw \<open>\EndSnip\<close>
proof (cases "\<exists> val . the (kind g cond) = ConstantNode val")
  case True
  show ?thesis
  proof -
    obtain val where val: "the (kind g cond) = ConstantNode val"
      using True by blast
    have cond_exists: "cond \<in> ids g"
      using cv sorry
    have if_kind: "kind gif nid = Some (IfNode cond tb fb)"
      using gif add_node_lookup by simp
    have if_cv: "gif m \<turnstile> cond (the (kind gif cond)) \<mapsto> IntVal val"
      using step.IfNode if_kind
      using True eval.ConstantNode gif fresh
      using stay_same cond_exists
      using val sorry
    have if_step: "(gif_prog, sig) \<turnstile> (nid,m,heap) \<rightarrow> (if val_to_bool val then tb else fb,m,heap)"
    proof -
      show ?thesis using step.IfNode if_kind if_cv 
        by (simp add: gif_lookup)
    qed
    have create_step: "(gcreate_prog, sig) \<turnstile> (nid,m,heap) \<rightarrow> (if val_to_bool val then tb else fb,m,heap)"
    proof -
      have create_kind: "kind gcreate nid = Some (create_if g cond tb fb)"
        using gcreate add_node_lookup
        by blast
      have create_fun: "create_if g cond tb fb = RefNode (if val_to_bool val then tb else fb)"
        using True create_kind val by simp 
      show ?thesis using step.RefNode create_kind create_fun if_cv 
        by (simp add: gcreate_lookup)
    qed
    show ?thesis using Step create_step if_step by blast
  qed
next
  case not_const: False
  obtain nid' where "nid' = (if val_to_bool cv then tb else fb)"
    by blast
  have nid_eq: "((gif_prog, sig) \<turnstile> (nid,m,heap) \<rightarrow> (nid',m,heap)) \<and> ((gcreate_prog, sig) \<turnstile> (nid,m,heap) \<rightarrow> (nid',m,heap))"
  proof -
    have nid': "nid' = (if val_to_bool cv then tb else fb)"
      by (simp add: \<open>nid' = (if val_to_bool cv then tb else fb)\<close>)
    have gif_kind: "kind gif nid = Some (IfNode cond tb fb)"
      using add_node_lookup gif
      by blast
    have "nid \<noteq> cond"
      using cv fresh indep sorry
    obtain cv2 where cv2: "gif m \<turnstile> cond (the (kind gif cond)) \<mapsto> cv2" 
      using \<open>nid \<noteq> cond\<close> cv gif indep
      using fresh sorry
    then have "IntVal cv = cv2"
      using indep gif cv
      using \<open>nid \<noteq> cond\<close>
      using fresh sorry
    then have eval_gif: "((gif_prog, sig) \<turnstile> (nid,m,heap) \<rightarrow> (nid',m,heap))"
      using step.IfNode gif_kind nid' cv2 
      using gif_lookup by auto
    have gcreate_kind: "kind gcreate nid = Some (create_if g cond tb fb)"
      using gcreate add_node_lookup
      by blast
    have eval_gcreate: "(gcreate_prog, sig) \<turnstile> (nid,m,heap) \<rightarrow> (nid',m,heap)"
    proof (cases "tb = fb")
      case True
      have "create_if g cond tb fb = RefNode tb"
        using not_const True by (cases "the (kind g cond)"; auto)
      then show ?thesis
        using True gcreate_kind nid' step.RefNode
        by (simp add: gcreate_lookup)
    next
      case False
      have "create_if g cond tb fb = IfNode cond tb fb"
        using not_const False by (cases "the (kind g cond)"; auto)
      then show ?thesis
        using eval_gif gcreate gif
        using IfNode \<open>IntVal cv = cv2\<close> cv2 gcreate_lookup gif_kind nid' by auto
    qed
    show ?thesis
      using eval_gcreate eval_gif by blast
  qed
  show ?thesis using nid_eq Step by blast
qed


end