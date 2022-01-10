theory TermRewrites
  imports Semantics.IRTreeEvalThms Semantics.TreeToGraphThms

begin

(*
typedef Substitution = "{\<sigma> :: string \<Rightarrow> IRExpr option . finite (dom \<sigma>)}"
proof -
  have "finite(dom(Map.empty)) \<and> ran Map.empty = {}" by auto
  then show ?thesis
    by fastforce
qed
*)

lemma expr_at_node: "g \<turnstile> n \<simeq> (g @@ n)"
  using expr_at_node.simps repDet sorry

lemma graph_refinement:
  "graph_refinement g1 g2 \<Longrightarrow> (\<forall>n m p v. n \<in> ids g1 \<longrightarrow> ([g1, m, p] \<turnstile> n \<mapsto> v) \<longrightarrow> ([g2, m, p] \<turnstile> n \<mapsto> v))"
  unfolding graph_refinement_def expr_at_node.simps
  apply auto
  using expr_at_node.simps encodeeval_def graph_refinement_def le_expr_def 
  by (metis expr_at_node repDet)

datatype SubValue = SubExpr(s_expr: IRExpr) | SubConst(s_val: Value) | SubNone

type_synonym Substitution = "string \<Rightarrow> SubValue"

fun dom :: "Substitution \<Rightarrow> string set" where
  "dom \<sigma> = { s . \<sigma> s \<noteq> SubNone }"

lemma in_dom: "x \<in> dom \<sigma> \<Longrightarrow> \<sigma> x \<noteq> SubNone"
  by simp
  
fun substitute :: "Substitution \<Rightarrow> IRExpr \<Rightarrow> IRExpr" (infix "$" 60) where
  "substitute \<sigma> (UnaryExpr op e) = UnaryExpr op (\<sigma> $ e)" |
  "substitute \<sigma> (BinaryExpr op e1 e2) = BinaryExpr op (\<sigma> $ e1) (\<sigma> $ e2)" |
  "substitute \<sigma> (ConditionalExpr b e1 e2) = ConditionalExpr (\<sigma> $ b) (\<sigma> $ e1) (\<sigma> $ e2)" |
  "substitute \<sigma> (ParameterExpr i s) = ParameterExpr i s" |
  "substitute \<sigma> (LeafExpr n s) = LeafExpr n s" |
  "substitute \<sigma> (ConstantExpr v) = ConstantExpr v" |
  "substitute \<sigma> (ConstantVar x) = 
      (case \<sigma> x of SubConst v \<Rightarrow> ConstantExpr v | _ \<Rightarrow> ConstantVar x)" |
  "substitute \<sigma> (VariableExpr x s) = 
      (case \<sigma> x of SubNone \<Rightarrow> (VariableExpr x s) | SubExpr y \<Rightarrow> y)"

fun union :: "Substitution \<Rightarrow> Substitution \<Rightarrow> Substitution" where
  "union \<sigma>1 \<sigma>2 = (\<lambda>name. if \<sigma>1 name = SubNone then \<sigma>2 name else \<sigma>1 name)"

fun compatible :: "Substitution \<Rightarrow> Substitution \<Rightarrow> bool" where
  "compatible \<sigma>1 \<sigma>2 = (\<forall>x. \<sigma>1 x \<noteq> SubNone \<and> \<sigma>2 x \<noteq> SubNone \<longrightarrow> \<sigma>1 x = \<sigma>2 x)"

fun substitution_union :: "Substitution option \<Rightarrow> Substitution option \<Rightarrow> Substitution option" (infix "\<uplus>" 70) where
  "substitution_union s1 s2 = 
      (case s1 of
       None \<Rightarrow> None |
       Some \<sigma>1 \<Rightarrow> 
           (case s2 of
            None \<Rightarrow> None |
            Some \<sigma>2 \<Rightarrow> (if compatible \<sigma>1 \<sigma>2 then Some (union \<sigma>1 \<sigma>2) else None)
           )
      )"

definition EmptySubstitution :: "Substitution" where 
  "EmptySubstitution = (\<lambda>x. SubNone)"

fun match :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> Substitution option" where
  "match (UnaryExpr op e) (UnaryExpr op' e') = 
      (if op = op' then match e e' else None)" |
  "match (BinaryExpr op e1 e2) (BinaryExpr op' e1' e2') = 
      (if op = op' then (match e1 e1') \<uplus> (match e2 e2') else None)" |
  "match (ConditionalExpr b e1 e2) (ConditionalExpr b' e1' e2') = 
      (match b b') \<uplus> ((match e1 e1') \<uplus> (match e2 e2'))" |
  "match (ParameterExpr i1 s1) (ParameterExpr i2 s2) = 
      (if i1 = i2 \<and> s1 = s2 then Some EmptySubstitution else None)" |
  "match (LeafExpr n1 s1) (LeafExpr n2 s2) = 
      (if n1 = n2 \<and> s1 = s2 then Some EmptySubstitution else None)" |
  "match (ConstantExpr v1) (ConstantExpr v2) = 
      (if v1 = v2 then Some EmptySubstitution else None)" |
  "match (ConstantVar name) (ConstantExpr v) = 
      Some(\<lambda>x. if x = name then SubConst v else SubNone)" |
  "match (VariableExpr x s) e = Some (\<lambda> n. if n = x then SubExpr e else SubNone)" |
  "match _ _ = None"


fun vars :: "IRExpr \<Rightarrow> string set" where
  "vars (UnaryExpr op e) = vars e" |
  "vars (BinaryExpr op e1 e2) = vars e1 \<union> vars e2" |
  "vars (ConditionalExpr b e1 e2) = vars b \<union> vars e1 \<union> vars e2" |
  "vars (ParameterExpr i s) = {}" |
  "vars (LeafExpr n s) = {}" |
  "vars (ConstantExpr v) = {}" |
  "vars (ConstantVar x) = {x}" |
  "vars (VariableExpr x s) = {x}"

typedef Rewrite = "{ (e1,e2) :: IRExpr \<times> IRExpr | e1 e2 . vars e2 \<subseteq> vars e1 }" 
proof -
  have "\<exists>v. vars (ConstantExpr v) \<subseteq> vars (ConstantExpr v)" by simp
  then show ?thesis
    by blast
qed

fun rewrite :: "Rewrite \<Rightarrow> IRExpr \<Rightarrow> IRExpr option" where
  "rewrite r e = (let (e1,e2) = Rep_Rewrite r in 
                   (case match e1 e of
                    Some \<sigma> \<Rightarrow> Some (\<sigma> $ e2) |
                    None \<Rightarrow> None))"

definition rewrite_valid :: "Rewrite \<Rightarrow> bool" where
  "rewrite_valid r = (let (e1,e2) = Rep_Rewrite r in
    (\<forall>\<sigma> e. is_ground e \<longrightarrow> match e1 e = Some \<sigma> \<longrightarrow> (e \<ge> (\<sigma> $ e2))))"

definition rewrite_valid_rep :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "rewrite_valid_rep e1 e2 = (vars e1 \<subseteq> vars e2 \<longrightarrow> (\<forall>\<sigma> e.  match e1 e = Some \<sigma> \<longrightarrow> (e \<ge> (\<sigma> $ e2))))"

definition IntStamp32 :: Stamp where 
  "IntStamp32 = IntegerStamp 32 (fst (bit_bounds 32)) (snd (bit_bounds 32))"

lemma match_succeeds:
  assumes "match e1 e = Some \<sigma>"
  shows "\<sigma> $ e1 = e"
  and "vars e1 = dom \<sigma>"
(*proof (induct e arbitrary: \<sigma> e1 rule: match.induct) *)
sorry

definition isIntExpr :: "IRExpr \<Rightarrow> bool" where
  "isIntExpr e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> is_IntVal32 v)"

lemma int_add_preserve:
  assumes "is_IntExpr ex"
  assumes "is_IntExpr ey"
  shows "isIntExpr (BinaryAdd BinAdd ex ey)"
  sorry

lemma "valid_value (constantAsStamp (IntVal32 v)) (IntVal32 v)"
  sorry

lemma int_constant: "isIntExpr (ConstantExpr (IntVal32 v))"
  sorry

lemma "isIntExpr e \<Longrightarrow> (\<exists>v. \<forall>m p. [m, p] \<turnstile> e \<mapsto> IntVal32 v)"
  sorry

lemma var_x: 
  assumes "\<forall>e \<sigma>. match (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))) e = Some \<sigma>"
  shows "''x'' \<in> vars (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0)))"
    using vars.simps by simp

lemma domx: 
  assumes "match (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))) e = Some \<sigma>" 
  shows "''x'' \<in> dom \<sigma>"
    using match_succeeds(2) var_x
    by (metis assms insertI1 insert_is_Un vars.simps(2) vars.simps(8))

lemma zero_helper_x:
  assumes "match (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))) e = Some \<sigma>"
  shows "\<sigma> ''x'' \<noteq> SubNone"
  using domx in_dom assms by presburger

lemma zero_identity: 
  "rewrite_valid_rep (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))) 
                     (VariableExpr ''x'' IntStamp32)"
proof -
  have pv: "\<forall>vx. intval_add (IntVal32 vx) (IntVal32 0) = IntVal32 vx" 
    using intval_add.simps by simp
  have vvx: "valid_value (constantAsStamp (IntVal32 0)) (IntVal32 0)"
    using valid_constant by blast
  have eval0: "\<forall>m p. [m, p] \<turnstile> ConstantExpr (IntVal32 0) \<mapsto> (IntVal32 0)"
    using ConstantExpr vvx by blast
  have eval_add: "\<forall>ex. isIntExpr ex \<longrightarrow> 
    (\<forall>m p vx. ([m, p] \<turnstile> ex \<mapsto> IntVal32 vx) \<longrightarrow> 
      ([m, p] \<turnstile> BinaryExpr BinAdd ex (ConstantExpr (IntVal32 0)) \<mapsto> (IntVal32 vx)))"
    by (metis BinaryExpr Value.distinct(1) bin_eval.simps(1) eval0 pv)
  have add_eval: "\<forall>ex. isIntExpr ex \<longrightarrow>
      (\<forall>m p v. ([m, p] \<turnstile> BinaryExpr BinAdd ex (ConstantExpr (IntVal32 0)) \<mapsto> v) \<longrightarrow> 
               [m, p] \<turnstile> ex \<mapsto> v)"
    using eval_add evalDet by (metis BinaryExprE isIntExpr_def is_IntVal32_def) 
  have add_refine: "\<forall>ex. isIntExpr ex \<longrightarrow>
      BinaryExpr BinAdd ex (ConstantExpr (IntVal32 0)) \<ge> ex"
    unfolding le_expr_def
    using add_eval by blast
  have add_refine_substit: "\<forall>\<sigma> ex. \<sigma> ''x'' = SubExpr ex \<and> isIntExpr ex \<longrightarrow>
        BinaryExpr BinAdd ex (ConstantExpr (IntVal32 0)) \<ge> ex"
    using add_refine by blast
  have add_substit: "\<forall>\<sigma> ex. \<sigma> ''x'' = SubExpr ex \<and> isIntExpr ex \<longrightarrow>
        \<sigma> $ (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))) \<ge> ex"
    using add_refine_substit by fastforce
  have match_e: "\<forall>e \<sigma>. match (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))) e = (Some \<sigma>) \<longrightarrow>
         (e = \<sigma> $ (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))))"
    using match_succeeds match.simps(7) by presburger
  have v: " vars (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))) \<subseteq> vars (VariableExpr ''x'' IntStamp32)"
    using vars.simps  by simp
  have "\<forall>\<sigma> e. vars (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))) \<subseteq> vars (VariableExpr ''x'' IntStamp32) \<longrightarrow>
        match (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))) e = Some \<sigma> \<longrightarrow>
        \<sigma> $ VariableExpr ''x'' IntStamp32 \<le> e"
    apply simp
    using match_e add_substit  sorry
  have dom: "\<forall>e \<sigma>. match (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))) e = Some \<sigma> \<longrightarrow> 
            vars (BinaryExpr BinAdd (VariableExpr ''x'' IntStamp32) (ConstantExpr (IntVal32 0))) \<subseteq> dom \<sigma>"
    using match_succeeds by (metis dual_order.refl)

  show ?thesis 
    unfolding rewrite_valid_rep_def
    sorry
qed

end
