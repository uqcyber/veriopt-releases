theory Canonicalization
  imports IREval
begin

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]

lemma eval_const_node:
  assumes xn: "kind g x = ConstantNode xv"
  shows "g m \<turnstile> x (kind g x) \<mapsto> (IntVal xv)"
  using xn ConstantNode by simp

lemma eval_add_node: 
  assumes x: "g m \<turnstile> x (kind g x) \<mapsto> IntVal(xv)"
  assumes y: "g m \<turnstile> y (kind g y) \<mapsto> IntVal(yv)"
  shows "g m \<turnstile> z (AddNode x y) \<mapsto> IntVal(xv+yv)"
  using AddNode x y by blast

lemma add_const_nodes:
  assumes det: "\<forall>g m x n v1 v2. 
    (g m \<turnstile> x n \<mapsto> v1) \<and> (g m \<turnstile> x n \<mapsto> v2) \<longrightarrow> v1 = v2"
  assumes xn: "kind g x = ConstantNode xv"
  assumes yn: "kind g y = ConstantNode yv"
  assumes zn: "kind g z = AddNode x y"
  assumes wn: "kind g w = ConstantNode (xv+yv)"
  assumes ez: "g m \<turnstile> z (kind g z) \<mapsto> v1"
  assumes ew: "g m \<turnstile> w (kind g w) \<mapsto> v2"
  shows "v1 = v2"
proof -
  have zv: "g m \<turnstile> z (kind g z) \<mapsto> IntVal(xv+yv)"
    using AddNode eval_const_node xn yn zn by auto
  have wv: "g m \<turnstile> w (kind g w) \<mapsto> IntVal(xv+yv)"
    using eval_const_node wn by auto
  show ?thesis using det zv wv
    using ew ez by blast
qed

text_raw \<open>\snip{create_add_node}{\<close>
fun create_add_node :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode" where 
  "create_add_node g x y = 
    (case kind g x of 
      ConstantNode xv \<Rightarrow> 
        (case kind g y of
          ConstantNode yv \<Rightarrow> ConstantNode (xv+yv) | 
          _ \<Rightarrow> if xv = 0 then Ref y else AddNode x y
        ) |
      _ \<Rightarrow> (case kind g y of
            ConstantNode yv \<Rightarrow> 
              if yv = 0 then Ref x else AddNode x y |
            _ \<Rightarrow> AddNode x y
           )
    )"
text_raw \<open>}%endsnip\<close>

text_raw \<open>\snip{add_node_create}{\<close>
lemma add_node_create:
  assumes det: "\<forall>g m x n v1 v2. 
    (g m \<turnstile> x n \<mapsto> v1) \<and> (g m \<turnstile> x n \<mapsto> v2) \<longrightarrow> v1 = v2"
  assumes xv: "g m \<turnstile> x (kind g x) \<mapsto> IntVal(xv)"
  assumes yv: "g m \<turnstile> y (kind g y) \<mapsto> IntVal(yv)"
  shows "(g m \<turnstile> nid (AddNode x y) \<mapsto> IntVal(xv+yv)) \<and>
         (g m \<turnstile> nid (create_add_node g x y) \<mapsto> IntVal(xv+yv))"
proof -
  have ae: "g m \<turnstile> nid (AddNode x y) \<mapsto> IntVal(xv+yv)"
    using eval_add_node xv yv by blast
  have ce: "g m \<turnstile> nid (create_add_node g x y) \<mapsto> IntVal(xv+yv)"
  proof (cases "kind g x  = ConstantNode xvv")
    case xvvn: True
    have xvv: "xvv = xv" 
      using ConstantNode det xv eval.ConstantNode xvvn by fastforce 
    thus ?thesis 
    proof (cases "kind g y = ConstantNode yvv")
      case True
      have yvv: "yvv = yv"
        using ConstantNode det yv eval.ConstantNode True by fastforce
      then show ?thesis
      proof -
        have xvv_yvv: "g m \<turnstile> nid (ConstantNode (xvv+yvv)) \<mapsto> IntVal(xv+yv)"
          by (simp add: ConstantNode xvv yvv) 
        have c_xvv_yvv: "create_add_node g x y = ConstantNode (xvv+yvv)" 
          apply auto using xvvn True by simp  
        have cv: "g m \<turnstile> nid (create_add_node g x y) \<mapsto> IntVal(xv+yv)"
          using c_xvv_yvv xvv_yvv by simp
        then show ?thesis by blast 
      qed
    next
      case False
      then show ?thesis
      proof -
        have "create_add_node g x y = (if xvv = 0 then Ref y else AddNode x y)"
          using xvvn False 

text_raw \<open>}%endsnip\<close>

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