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

fun expr_at_node :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRExpr"
  (infix "@@" 50) where
  "expr_at_node g n = (SOME e . (g \<turnstile> n \<simeq> e))"
                          
lemma expr_at_node: "g \<turnstile> n \<simeq> e \<Longrightarrow> g \<turnstile> n \<simeq> (g @@ n)"
  using expr_at_node.simps repDet 
  by (simp add: someI)

lemma graph_refinement:
  "graph_refinement g1 g2 \<Longrightarrow> (\<forall>n m p v. n \<in> ids g1 \<longrightarrow> ([g1, m, p] \<turnstile> n \<mapsto> v) \<longrightarrow> ([g2, m, p] \<turnstile> n \<mapsto> v))"
  unfolding graph_refinement_def expr_at_node.simps
  apply auto[1]
  using expr_at_node.simps encodeeval_def graph_refinement_def le_expr_def 
  by (meson term_graph_evaluation)

datatype SubValue = SubExpr(s_expr: IRExpr) | SubConst(s_val: Value)

typedef Substitution = "{s :: String.literal \<rightharpoonup> SubValue . finite (dom s)}"
  using finite_dom_map_of by blast

setup_lifting type_definition_Substitution

lift_definition subst :: "(String.literal \<times> SubValue) list \<Rightarrow> Substitution"
  is "map_of"
  by (simp add: finite_dom_map_of)

lift_definition subst_set :: "Substitution \<Rightarrow> (String.literal \<times> SubValue) set"
  is "Map.graph" .

lemma subst_reconstruct:
  "distinct (map fst x) \<Longrightarrow> set x = subst_set (subst x)"
  by (simp add: graph_map_of_if_distinct_dom subst.rep_eq subst_set.rep_eq)

lift_definition dom :: "Substitution \<Rightarrow> String.literal set"
  is Map.dom .

lift_definition maps_to :: "Substitution \<Rightarrow> String.literal \<Rightarrow> SubValue option"
  is "\<lambda> \<sigma> x . \<sigma> x" .

code_datatype subst Abs_Substitution

lemma [code]: "Rep_Substitution (subst m) = map_of m"
  using Abs_Substitution_inverse
  using subst.rep_eq by blast

lemma dom_code[code]: "dom (subst m) = set (map fst m)"
  by (simp add: dom.rep_eq dom_map_of_conv_image_fst subst.rep_eq)

lemma in_dom: "x \<in> dom \<sigma> \<Longrightarrow> maps_to \<sigma> x \<noteq> None"
  by (simp add: dom.rep_eq domIff maps_to.rep_eq)
  
fun substitute :: "Substitution \<Rightarrow> IRExpr \<Rightarrow> IRExpr" (infix "$" 60) where
  "substitute \<sigma> (UnaryExpr op e) = UnaryExpr op (\<sigma> $ e)" |
  "substitute \<sigma> (BinaryExpr op e1 e2) = BinaryExpr op (\<sigma> $ e1) (\<sigma> $ e2)" |
  "substitute \<sigma> (ConditionalExpr b e1 e2) = ConditionalExpr (\<sigma> $ b) (\<sigma> $ e1) (\<sigma> $ e2)" |
  "substitute \<sigma> (ParameterExpr i s) = ParameterExpr i s" |
  "substitute \<sigma> (LeafExpr n s) = LeafExpr n s" |
  "substitute \<sigma> (ConstantExpr v) = ConstantExpr v" |
  "substitute \<sigma> (ConstantVar x) = 
      (case maps_to \<sigma> x of Some (SubConst v) \<Rightarrow> ConstantExpr v | _ \<Rightarrow> ConstantVar x)" |
  "substitute \<sigma> (VariableExpr x s) = 
      (case maps_to \<sigma> x of None \<Rightarrow> (VariableExpr x s) | Some (SubExpr y) \<Rightarrow> y)"

lift_definition union :: "Substitution \<Rightarrow> Substitution \<Rightarrow> Substitution"
  is "\<lambda>\<sigma>1 \<sigma>2. \<sigma>1 ++ \<sigma>2"
  by simp

(*fun union :: "Substitution \<Rightarrow> Substitution \<Rightarrow> Substitution" where
  "union \<sigma>1 \<sigma>2 = Abs_Substitution (\<lambda>name. if maps_to \<sigma>1 name = None then maps_to \<sigma>2 name else maps_to \<sigma>1 name)"
*)

lemma not_empty_has_member:
  assumes "xs \<noteq> []"
  shows "\<exists> k v. List.member xs (k, v)"
  using assms apply (cases xs; auto)
  by (meson member_rec(1))

value "map_of ([(x, xv1), (y, yv)] @ [(z, zv), (x, xv2)]) x"

lemma equal_mapping_implies_equal:
  assumes "\<forall>k. maps_to \<sigma>1 k = maps_to \<sigma>2 k"
  shows "\<sigma>1 = \<sigma>2"
  using assms unfolding maps_to_def using Rep_Substitution
  by (metis Rep_Substitution_inverse ext id_def map_fun_apply)

(*
lemma 
  "maps_to (union (subst \<sigma>1) (subst \<sigma>2)) k = maps_to (subst (\<sigma>1 @ \<sigma>2)) k"
  (is "maps_to ?union k = maps_to ?add k")
proof (cases "\<exists> v. List.member \<sigma>1 (k, v)"; cases "\<exists> v. List.member \<sigma>2 (k, v)")
  case True \<comment>\<open>key has mapping in both\<close>
  then show ?thesis sorry
next
  case False \<comment>\<open>key in \<sigma>1 but not \<sigma>2\<close>
  then show ?thesis sorry
next
  \<comment>\<open>key in \<sigma>2 but not \<sigma>1\<close>
  assume a1: "\<nexists>v. List.member \<sigma>1 (k, v)"
  assume a2: "\<exists>v. List.member \<sigma>2 (k, v)"
  obtain v where v: "List.member \<sigma>2 (k, v)"
    using a2 by auto
  from a1 v have "maps_to ?add k = Some v"
    unfolding maps_to_def subst_def using map_of_append sledgehammer
  then show ?thesis sorry
next
  \<comment>\<open>key in neither\<close>
  assume a1: "\<nexists>v. List.member \<sigma>1 (k, v)"
  assume a2: "\<nexists>v. List.member \<sigma>2 (k, v)"
  from a1 a2 have "maps_to ?add k = None"
    by (metis domD in_set_member map_add_dom_app_simps(2) map_of_SomeD map_of_append maps_to.rep_eq opt_to_list.cases option.discI subst.rep_eq)
  then show ?thesis
    by (metis map_add_None map_of_append maps_to.rep_eq subst.rep_eq union.rep_eq)
qed
*)

lemma union_code[code]:
  "union (subst \<sigma>1) (subst \<sigma>2) = (subst (\<sigma>2 @ \<sigma>1))"
  (is "?union = ?add")
  using map_of_append unfolding subst_def union_def
  using subst.abs_eq subst.rep_eq by auto

(*
proof (cases "\<sigma>1 = []")
  case True
  then show ?thesis
    by (metis Rep_Substitution_inverse append.right_neutral append_Nil map_of_append subst.rep_eq union.rep_eq)
next
  case False
  then obtain k v where v: "List.member \<sigma>1 (k, v)"
    using not_empty_has_member by blast
  show ?thesis
  proof (cases "\<exists>v. List.member \<sigma>2 (k, v)")
    case True
    obtain v' where v': "List.member \<sigma>2 (k, v')"
      using True
      by blast
    have rhs: "maps_to (?add) k = Some v"
      using v v' unfolding maps_to_def subst_def sorry
    have lhs: "maps_to (?union) k = Some v"
      sorry
    from lhs rhs have "maps_to (?add) k = maps_to (?union) k"
      sorry
    then show ?thesis using equal_mapping_implies_equal sorry
  next
    case False
    then show ?thesis
      by simp
  qed
qed
  
  apply (induction \<sigma>1; induction \<sigma>2; auto)
  apply (metis append_Nil map_of_append subst.abs_eq subst.rep_eq)
  apply (metis map_of_append self_append_conv subst.abs_eq subst.rep_eq)
   apply (metis append_Nil map_of_append subst.abs_eq subst.rep_eq)
  sorry
*)

fun compatible :: "Substitution \<Rightarrow> Substitution \<Rightarrow> bool" where
  "compatible \<sigma>1 \<sigma>2 = (\<forall>x \<in> dom \<sigma>1. maps_to \<sigma>2 x \<noteq> None \<longrightarrow> maps_to \<sigma>1 x = maps_to \<sigma>2 x)"

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

(*lemma "sup x y = x"*)

definition EmptySubstitution :: "Substitution" where 
  "EmptySubstitution = subst []"

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
      Some (subst [(name, (SubConst v))])" |
  "match (VariableExpr name s) e = 
      Some (subst [(name, (SubExpr e))])" |
  "match _ _ = None"


fun vars :: "IRExpr \<Rightarrow> String.literal fset" where
  "vars (UnaryExpr op e) = vars e" |
  "vars (BinaryExpr op e1 e2) = vars e1 |\<union>| vars e2" |
  "vars (ConditionalExpr b e1 e2) = vars b |\<union>| vars e1 |\<union>| vars e2" |
  "vars (ParameterExpr i s) = {||}" |
  "vars (LeafExpr n s) = {||}" |
  "vars (ConstantExpr v) = {||}" |
  "vars (ConstantVar x) = {|x|}" |
  "vars (VariableExpr x s) = {|x|}"

typedef Rewrite = "{ (e1,e2,cond) :: IRExpr \<times> IRExpr \<times> (Substitution \<Rightarrow> bool) | e1 e2 cond . vars e2 |\<subseteq>| vars e1 }" 
proof -
  have "\<exists>v. vars (ConstantExpr v) |\<subseteq>| vars (ConstantExpr v)" by simp
  then show ?thesis
    by blast
qed

setup_lifting type_definition_Rewrite


fun construct_rewrite :: "IRExpr \<times> IRExpr \<times> (Substitution \<Rightarrow> bool) \<Rightarrow> Rewrite option" where
  "construct_rewrite (e1, e2, cond) =
    (if vars e2 |\<subseteq>| vars e1 then Some (Abs_Rewrite (e1, e2, cond)) else None)"

code_datatype Abs_Rewrite

lemma "Abs_Rewrite (Rep_Rewrite r) = r"
  by (simp add: Rep_Rewrite_inverse)

lemma [code]: "Rep_Rewrite (Abs_Rewrite (e1, e2)) = (e1, e2)"
  sorry

fun rewrite :: "Rewrite \<Rightarrow> IRExpr \<Rightarrow> IRExpr option" where
  "rewrite r e = (let (e1,e2,cond) = Rep_Rewrite r in 
                   (case match e1 e of
                    Some \<sigma> \<Rightarrow> 
                      (if cond \<sigma> then Some (\<sigma> $ e2) else None) |
                    None \<Rightarrow> None))"

definition rewrite_valid :: "Rewrite \<Rightarrow> bool" where
  "rewrite_valid r = (let (e1,e2,cond) = Rep_Rewrite r in
    (\<forall>\<sigma> e. is_ground e \<longrightarrow> match e1 e = Some \<sigma> \<longrightarrow> (e \<ge> (\<sigma> $ e2))))"

definition rewrite_valid_rep :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "rewrite_valid_rep e1 e2 = (vars e1 |\<subseteq>| vars e2 \<longrightarrow> (\<forall>\<sigma> e.  match e1 e = Some \<sigma> \<longrightarrow> (e \<ge> (\<sigma> $ e2))))"

definition IntStamp32 :: Stamp where 
  "IntStamp32 = IntegerStamp 32 (fst (bit_bounds 32)) (snd (bit_bounds 32))"

fun pattern_depth :: "IRExpr \<Rightarrow> nat" where
  "pattern_depth (UnaryExpr op e) = 1 + pattern_depth e" |
  "pattern_depth (BinaryExpr op e1 e2) = 1 + max (pattern_depth e1) (pattern_depth e2)" |
  "pattern_depth (ConditionalExpr b e1 e2) = 1 + max (pattern_depth b) (max (pattern_depth e1) (pattern_depth e2))" |
  "pattern_depth (ParameterExpr i s) = 1" |
  "pattern_depth (LeafExpr n s) = 1" |
  "pattern_depth (ConstantExpr v) = 1" |
  "pattern_depth (ConstantVar x) = 0" |
  "pattern_depth (VariableExpr x s) = 0"

value "pattern_depth (ConstantExpr (IntVal 32 0))"
value "pattern_depth (VariableExpr (STR ''x'') VoidStamp)"
value "pattern_depth (UnaryExpr UnaryAbs (ConstantExpr (IntVal 32 0)))"
value "pattern_depth (UnaryExpr UnaryAbs (VariableExpr (STR ''x'') VoidStamp))"
value "pattern_depth (UnaryExpr UnaryAbs (UnaryExpr UnaryNot (VariableExpr (STR ''x'') VoidStamp)))"
value "pattern_depth (BinaryExpr BinAdd (UnaryExpr UnaryNot (VariableExpr (STR ''x'') VoidStamp)) (VariableExpr (STR ''x'') VoidStamp))"
value "pattern_depth (BinaryExpr BinAdd (UnaryExpr UnaryNot (ConstantExpr (IntVal 32 0))) (VariableExpr (STR ''x'') VoidStamp))"
value "pattern_depth (BinaryExpr BinAdd (VariableExpr (STR ''x'') VoidStamp) (VariableExpr (STR ''x'') VoidStamp))"

(*fun fresh :: "String.literal \<Rightarrow> IRExpr \<Rightarrow> String.literal" where
  "fresh var e = var"*)

type_synonym VarName = "String.literal"

datatype PatternExpr =
    UnaryPattern IRUnaryOp VarName
  | BinaryPattern IRBinaryOp VarName VarName
  | ConditionalPattern VarName VarName VarName
  | VariablePattern VarName

type_synonym Vars = "VarName fset"

(*
function fresh :: "VarName \<Rightarrow> Vars \<Rightarrow> VarName" where
  "fresh var s = (if var |\<in>| s then fresh (var + (STR ''z'')) s else var)"
   apply force
  by fastforce

lemma fresh_var_code [code]:
  "fresh var s = (if var |\<in>| s then fresh (var + (STR ''z'')) s else (var))"
  sorry
*)

type_synonym Scope = "Vars \<times> (VarName \<Rightarrow> VarName option)"

function fresh :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope \<times> VarName" where
  "fresh var s = 
    (if var |\<in>| (fst s) then fresh (var + (STR ''z'')) s else (((fst s) |\<union>| {|var|}, snd s), var))"
   apply force
  by fastforce

lemma fresh_var_code [code]:
  "fresh var s = (if var |\<in>| (fst s) then fresh (var + (STR ''z'')) s else (((fst s) |\<union>| {|var|}, snd s), var))"
  sorry

(*
typedef PatternExpr = "{ e :: IRExpr . pattern_depth e \<le> 1 }"
  by (metis mem_Collect_eq pattern_depth.simps(8) zero_le)

code_datatype Abs_PatternExpr
*)

datatype MATCH =
    match VarName PatternExpr |
    equality VarName VarName ("_ == _") |
    seq MATCH MATCH ("_; _") |
    noop

datatype CODE =
    code MATCH IRExpr ("_ ? _")

type_synonym VariablePairs = "(VarName \<times> VarName) list"

type_synonym Symbols = "VariablePairs \<times> Vars"

value
  "(match (STR ''e'') (BinaryPattern BinAdd (STR ''ea'') (STR ''eb''));
   (match (STR ''ea'') (BinaryPattern BinSub (STR ''eaa'') (STR ''eab''));
   ((STR ''eab'') == (STR ''eb'')))) ? (VariableExpr (STR ''ea'') default_stamp)"

definition var :: "string \<Rightarrow> IRExpr" where
  "var v = (VariableExpr (String.implode v) VoidStamp)"

(*
definition la :: "(VarName \<Rightarrow> 'a) \<Rightarrow> (Vars \<Rightarrow> VarName \<times> Vars) \<Rightarrow> (Vars \<Rightarrow> 'a \<times> Vars)" (infix "\<langle>" 65)
  where
  "la f f' s = (f (fst (f' s)), snd (f' s))"

definition ra :: "(Vars \<Rightarrow> ('b \<Rightarrow> 'a) \<times> Vars) \<Rightarrow> (Vars \<Rightarrow> ('b \<times> Vars)) \<Rightarrow> (Vars \<Rightarrow> 'a \<times> Vars)" (infix "\<rangle>" 60)
  where
  "ra f f' s = ((fst (f s)) (fst (f' s)), snd (f s))"

fun test :: "IRExpr \<Rightarrow> Vars \<Rightarrow> MATCH \<times> Vars" where
  "test (UnaryExpr op e) =
    match \<langle> fresh STR ''e'' \<rangle>
      UnaryPattern op \<langle> fresh STR ''ea''" |
  "test (BinaryExpr op e1 e2) =
    match \<langle> fresh STR ''e'' \<rangle>
      (BinaryPattern op \<langle> fresh STR ''ea'' \<rangle> (fresh STR ''eb''))" |
  "test (ConditionalExpr b e1 e2) =
    match \<langle> fresh STR ''e'' \<rangle>
      ((ConditionalPattern \<langle> fresh STR ''ea'' \<rangle> (fresh STR ''eb'')) \<rangle> (fresh STR ''ec''))"
*)

definition la :: "('b \<Rightarrow> 'a) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'b) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'a)" (infix "\<langle>" 65)
  where
  "la f f' s = (fst (f' s), f (snd (f' s)))"

(*
definition ra :: "('b \<Rightarrow> 'a) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'b) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'a)" (infix "\<rangle>" 54)
  where
  "ra f f' s = ((fst (f' (s))), f (snd (f' s)))"
*)

definition ra :: "(Scope \<Rightarrow> Scope \<times> ('b \<Rightarrow> 'a)) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'b) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'a)" (infix "\<rangle>" 54)
  where
  "ra f f' s = ((fst (f' (fst (f s)))), (snd (f s)) (snd (f' (fst (f s)))))"

definition join :: "('b \<Rightarrow> 'c \<times> MATCH) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a \<times> MATCH) \<Rightarrow> 'b \<Rightarrow> 'a \<times> MATCH" (infix "|>" 53) where
  "join x y s = 
    (let (lhs_scope, lhs_match) = x s in
    (let (rhs_scope, rhs_match) = (y s lhs_scope) in
    (rhs_scope, (lhs_match; rhs_match))))"

abbreviation decend where
  "decend f e v \<equiv> (\<lambda>s s'. f e (snd (fresh v s)) s')"

value "match \<langle> fresh STR ''e''"

fun register_name where
  "register_name (s, m) vn v = (s, m(vn:=Some v))"

fun match_pattern :: "IRExpr \<Rightarrow> VarName \<Rightarrow> Scope \<Rightarrow> Scope \<times> MATCH" where
  "match_pattern (UnaryExpr op e) v =
    match v \<langle>
      (UnaryPattern op \<langle> fresh STR ''a'')
    |> decend match_pattern e STR ''a''
    " |
  "match_pattern (BinaryExpr op e1 e2) v =
    (match v \<langle> 
      (BinaryPattern op \<langle> fresh STR ''a'' \<rangle> fresh STR ''b'')
    |> decend match_pattern e1 STR ''a'')
    |> decend match_pattern e2 STR ''b''" |
  "match_pattern (ConditionalExpr b e1 e2) v =
    ((match v \<langle>
      ((ConditionalPattern \<langle> fresh STR ''a'' \<rangle> fresh STR ''b'') \<rangle> fresh STR ''c'')
    |> decend match_pattern b STR ''a'')
    |> decend match_pattern e1 STR ''b'')
    |> decend match_pattern e2 STR ''c''" |
  "match_pattern (VariableExpr vn st) v = 
    (\<lambda>s. (case (snd s) vn of 
      None \<Rightarrow> (register_name s vn v, noop) |
      Some v' \<Rightarrow> (register_name s vn v, v' == v)))"

fun expr_result :: "IRExpr \<Rightarrow> Scope \<Rightarrow> IRExpr" where
  "expr_result (UnaryExpr op e) s = 
    UnaryExpr op (expr_result e s)" |
  "expr_result (BinaryExpr op e1 e2) s = 
    BinaryExpr op (expr_result e1 s) (expr_result e2 s)" |
  "expr_result (ConditionalExpr b e1 e2) s = 
    ConditionalExpr (expr_result b s) (expr_result e1 s) (expr_result e2 s)" |
  "expr_result (VariableExpr vn st) (s, m) = 
    (case m vn of None \<Rightarrow> VariableExpr vn st 
                | Some v' \<Rightarrow> VariableExpr v' st)" |
  "expr_result e v = e"

fun generate :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> MATCH \<times> IRExpr" where
  "generate p r = 
    (let (s, m) = match_pattern p STR ''e'' ({||}, (\<lambda>x. None))
     in (m, expr_result r s))"

value
  "generate 
    (UnaryExpr UnaryNot
      (UnaryExpr UnaryNot (var ''x'')))
    (var ''x'')"

value
  "generate 
    (BinaryExpr BinAdd
      (BinaryExpr BinSub (var ''x'') (var ''y''))
      (var ''y''))
    (var ''x'')"

code_printing
  type_constructor MATCH \<rightharpoonup> (Scala) "MATCH"
  | constant match \<rightharpoonup> (Scala) "match"
  | constant seq \<rightharpoonup> (Scala) "seq"
  | constant noop \<rightharpoonup> (Scala) "noop"
  | constant equality \<rightharpoonup> (Scala) "=="

definition redundant_sub where
  "redundant_sub = generate 
    (BinaryExpr BinAdd
      (BinaryExpr BinSub (var ''x'') (var ''y''))
      (var ''y''))
    (var ''x'')"

definition redundant_sub_gen where
  "redundant_sub_gen = ((((MATCH.match STR ''e''
   (BinaryPattern BinAdd STR ''a''
     STR ''b''); MATCH.match STR ''a''
                  (BinaryPattern BinSub STR ''az'' STR ''bz'')); noop); noop); STR ''bz'' == STR ''b'',
  VariableExpr STR ''az'' VoidStamp)"

export_code redundant_sub in Scala
export_code redundant_sub_gen in Scala

(*
fun generate :: "Vars \<Rightarrow> IRExpr \<times> IRExpr \<times> (Substitution \<Rightarrow> bool) \<Rightarrow> MATCH" where
  "generate s (UnaryExpr op e, e', f) =
    (let
      used = s |\<union>| {|(fresh (STR ''e'') s), (fresh (STR ''ea'') s)|}
     in
        ((match (fresh (STR ''e'') s) (UnaryPattern op (fresh (STR ''ea'') s)));
        (generate used (e, e', f))))" |
  "generate s (BinaryExpr op e1 e2, e', f) = 
    (let 
      used = (s |\<union>| {|(fresh STR ''e'' s), (fresh STR ''ea'' s), (fresh STR ''eb'' s)|})
     in
        (((match (fresh STR ''e'' s)
            (BinaryPattern op (fresh (STR ''ea'') s) (fresh (STR ''eb'') s)));
        (generate used (e1, e', f)));
        (generate used (e2, e', f))))" |
  "generate s (ConditionalExpr b e1 e2, e', f) = 
    (let
      used = (s |\<union>| {|(fresh STR ''e'' s), (fresh STR ''ea'' s), (fresh STR ''eb'' s), (fresh STR ''ec'' s)|})
     in
        (((match (fresh STR ''e'' s)
              (ConditionalPattern (fresh (STR ''ea'') s) (fresh (STR ''eb'') s) (fresh (STR ''ec'') s)));
          ((generate used (b, e', f));
          ((generate used (e1, e', f));
           (generate used (e2, e', f)))))))" |
  "generate s (e, e', f) = match (fresh STR ''e'' s) (VariablePattern STR ''e'')"

value "generate {||} (BinaryExpr BinAdd (var ''x'') (var ''y''), var ''x'', \<lambda>x. True)"

value
  "generate {||} 
    (BinaryExpr BinAdd
      (BinaryExpr BinSub x y)
       y,
     x, \<lambda>x. True)"

value
  "generate {||} 
    (BinaryExpr BinAdd
      (BinaryExpr BinSub (var ''x'') (var ''y''))
      (var ''y''),
     (var ''x''), \<lambda>x. True)"

fun replace :: "MatchRules \<Rightarrow> IRExpr \<Rightarrow> IRExpr option" where
  "replace (match_pattern p) e = (if (match (Rep_PatternExpr p) e \<noteq> None) then Some e else None) " |
  "replace (ground g) e = Some g" |
  "replace (conditional c t f) e = (if (replace c e) \<noteq> None then (replace t e) else (replace f e))" |
  "replace (fail) e = None"

(*
  "generate (ConditionalExpr b e1 e2) = 1 + max (pattern_depth b) (max (pattern_depth e1) (pattern_depth e2))" |
  "generate (ParameterExpr i s) = 1" |
  "generate (LeafExpr n s) = 1" |
  "generate (ConstantExpr v) = 1" |
  "generate (ConstantVar x) = 0" |
  "generate (VariableExpr x s) = 0"*)
code_datatype Abs_PatternExpr
code_datatype Abs_GroundExpr

value "generate {} ( (VariableExpr (STR ''x'') VoidStamp), (ConstantExpr (IntVal 32 0)), \<lambda>_.True)"
(*
value "replace (generate ( (VariableExpr (STR ''x'') VoidStamp), (ConstantExpr (IntVal32 0)), \<lambda>_.True)) (ConstantExpr (IntVal32 0))"
*)

value "generate ((ConstantExpr (IntVal 32 0)), (ConstantExpr (IntVal 32 0)), \<lambda>_.True)"
value "generate ((UnaryExpr UnaryAbs (ConstantExpr (IntVal 32 0))), (ConstantExpr (IntVal 32 0)), \<lambda>_.True)"
value "generate ((UnaryExpr UnaryAbs (VariableExpr (STR ''x'') VoidStamp)), (ConstantExpr (IntVal 32 0)), \<lambda>_.True)"


(*
definition f where "f = generate ((BinaryExpr BinAnd
    (BinaryExpr BinOr (VariableExpr STR ''x'' (IntegerStamp 1 (fst (bit_bounds 1)) (snd (bit_bounds 1))))
      (VariableExpr STR ''y'' (IntegerStamp 1 (fst (bit_bounds 1)) (snd (bit_bounds 1)))))
    (VariableExpr STR ''z'' (IntegerStamp 1 (fst (bit_bounds 1)) (snd (bit_bounds 1))))),
   (BinaryExpr BinAnd (VariableExpr STR ''x'' (IntegerStamp 1 (fst (bit_bounds 1)) (snd (bit_bounds 1))))
    (VariableExpr STR ''z'' (IntegerStamp 1 (fst (bit_bounds 1)) (snd (bit_bounds 1))))), (\<lambda>_.True))"

export_code f in SML
value "f"*)

definition example_rewrite :: Rewrite where
  "example_rewrite = TermRewrites.Rewrite.Abs_Rewrite
  (BinaryExpr BinAnd
    (BinaryExpr BinOr (VariableExpr STR ''x'' (IntegerStamp 1 (fst (bit_bounds 1)) (snd (bit_bounds 1))))
      (VariableExpr STR ''y'' (IntegerStamp 1 (fst (bit_bounds 1)) (snd (bit_bounds 1)))))
    (VariableExpr STR ''z'' (IntegerStamp 1 (fst (bit_bounds 1)) (snd (bit_bounds 1)))),
   BinaryExpr BinAnd (VariableExpr STR ''x'' (IntegerStamp 1 (fst (bit_bounds 1)) (snd (bit_bounds 1))))
    (VariableExpr STR ''z'' (IntegerStamp 1 (fst (bit_bounds 1)) (snd (bit_bounds 1)))),
   \<lambda>x. True)"

lift_definition generate_rewrite :: "Rewrite \<Rightarrow> MatchRules"
  is generate .




value "generate_rewrite example_rewrite"

experiment begin
lemma match_succeeds:
  assumes "match e1 e = Some \<sigma>"
  shows "\<sigma> $ e1 = e"
  and "fset (vars e1) = dom \<sigma>"
  using assms
   apply (induct e1 e arbitrary: \<sigma> rule: match.induct; auto)
                 apply (meson option.distinct(1))+
  sorry


definition isIntExpr :: "IRExpr \<Rightarrow> bool" where
  "isIntExpr e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> is_IntVal v)"

lemma int_add_preserve:
  assumes "isIntExpr ex"
  assumes "isIntExpr ey"
  shows "isIntExpr (BinaryExpr BinAdd ex ey)"
  sorry

lemma valid_constant: "valid_value (IntVal 32 v) (constantAsStamp (IntVal 32 v))"
  sorry

lemma int_constant: "isIntExpr (ConstantExpr (IntVal 32 v))"
  sorry

lemma "isIntExpr e \<Longrightarrow> (\<exists>v. \<forall>m p. [m, p] \<turnstile> e \<mapsto> IntVal 32 v)"
  sorry

lemma var_x: 
  assumes "\<forall>e \<sigma>. match (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0))) e = Some \<sigma>"
  shows "STR ''x'' |\<in>| vars (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0)))"
    using vars.simps by simp

lemma domx: 
  assumes "match (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0))) e = Some \<sigma>" 
  shows "STR ''x'' \<in> dom \<sigma>"
    using match_succeeds(2) var_x sorry(*
    by (metis assms insertI1 insert_is_Un vars.simps(2) vars.simps(8))*)

lemma zero_helper_x:
  assumes "match (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0))) e = Some \<sigma>"
  shows "maps_to \<sigma> STR ''x'' \<noteq> None"
  using domx in_dom assms by presburger

lemma zero_identity: 
  "rewrite_valid_rep (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0))) 
                     (VariableExpr STR ''x'' IntStamp32)"
proof -
  have pv: "\<forall>vx. intval_add (IntVal 32 vx) (IntVal 32 0) = IntVal 32 vx" 
    using intval_add.simps
    using valid_constant by auto
  have vvx: "valid_value (IntVal 32 0) (constantAsStamp (IntVal 32 0))"
    using valid_constant by blast
  have eval0: "\<forall>m p. [m, p] \<turnstile> ConstantExpr (IntVal 32 0) \<mapsto> (IntVal 32 0)"
    using ConstantExpr vvx
    using wf_value_def by blast
  have eval_add: "\<forall>ex. isIntExpr ex \<longrightarrow> 
    (\<forall>m p vx. ([m, p] \<turnstile> ex \<mapsto> IntVal 32 vx) \<longrightarrow> 
      ([m, p] \<turnstile> BinaryExpr BinAdd ex (ConstantExpr (IntVal 32 0)) \<mapsto> (IntVal 32 vx)))"
    by (metis BinaryExpr Value.distinct(1) bin_eval.simps(1) eval0 pv)
  have add_eval: "\<forall>ex. isIntExpr ex \<longrightarrow>
      (\<forall>m p v. ([m, p] \<turnstile> BinaryExpr BinAdd ex (ConstantExpr (IntVal 32 0)) \<mapsto> v) \<longrightarrow> 
               [m, p] \<turnstile> ex \<mapsto> v)"
    using eval_add evalDet sorry
  have add_refine: "\<forall>ex. isIntExpr ex \<longrightarrow>
      BinaryExpr BinAdd ex (ConstantExpr (IntVal 32 0)) \<ge> ex"
    unfolding le_expr_def
    using add_eval by blast
  have add_refine_substit: "\<forall>\<sigma> ex. \<sigma> STR ''x'' = SubExpr ex \<and> isIntExpr ex \<longrightarrow>
        BinaryExpr BinAdd ex (ConstantExpr (IntVal 32 0)) \<ge> ex"
    using add_refine by blast
  have add_substit: "\<forall>\<sigma> ex. maps_to \<sigma> STR ''x'' = Some (SubExpr ex) \<and> isIntExpr ex \<longrightarrow>
        \<sigma> $ (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0))) \<ge> ex"
    using add_refine_substit by fastforce
  have match_e: "\<forall>e \<sigma>. match (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0))) e = (Some \<sigma>) \<longrightarrow>
         (e = \<sigma> $ (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0))))"
    using match_succeeds match.simps(7) by presburger
  have v: " vars (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0))) |\<subseteq>| vars (VariableExpr STR ''x'' IntStamp32)"
    using vars.simps  by simp
  have "\<forall>\<sigma> e. vars (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0))) |\<subseteq>| vars (VariableExpr STR ''x'' IntStamp32) \<longrightarrow>
        match (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0))) e = Some \<sigma> \<longrightarrow>
        \<sigma> $ VariableExpr STR ''x'' IntStamp32 \<le> e"
    apply simp
    using match_e add_substit  sorry
  have dom: "\<forall>e \<sigma>. match (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0))) e = Some \<sigma> \<longrightarrow> 
            fset (vars (BinaryExpr BinAdd (VariableExpr STR ''x'' IntStamp32) (ConstantExpr (IntVal 32 0)))) \<subseteq> dom \<sigma>"
    using match_succeeds by (metis dual_order.refl)

  show ?thesis 
    unfolding rewrite_valid_rep_def
    sorry
qed
end
*)

end
