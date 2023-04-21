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

(*
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

*)




section \<open>Code Generation via Match Primitives\<close>

subsection \<open>Pattern Expressions\<close>
text \<open>
A pattern expression corresponds to an @{typ IRExpr} without nesting.
Nested expressions are replaced with a string placeholder.

This restricts match primitives to match just one node.
\<close>
type_synonym VarName = "String.literal"
type_synonym Vars = "VarName fset"

datatype PatternExpr =
    UnaryPattern IRUnaryOp VarName
  | BinaryPattern IRBinaryOp VarName VarName
  | ConditionalPattern VarName VarName VarName
  | VariablePattern VarName
  | ConstantPattern Value


subsection \<open>Variable Generation\<close>
text \<open>
Variable scoping in match primitives is handled by the Scope type.
Scope is a pair of;
\begin{enumerate}
\item the set of used variable names, and
\item a mapping of the @{emph \<open>real\<close>} variable names to the most recent @{emph \<open>alias\<close>} for the real variable.
\end{enumerate}

A rewriting rule consists of @{emph \<open>real\<close>} variable names which can overlap.
A match primitive has @{emph \<open>alias\<close>} variable names to the real names.
Aliases must be unique.
\<close>
type_synonym Scope = "Vars \<times> (VarName \<rightharpoonup> VarName)"

fun remove_var :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope" where
  "remove_var v (vs, m) = (vs - {|v|}, m)"
fun add_var :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope" where
  "add_var v (vs, m) = (vs |\<union>| {|v|}, m)"


function fresh_var :: "VarName \<Rightarrow> Scope \<Rightarrow> VarName" where
  "fresh_var var s = 
    (if var |\<in>| (fst s) 
      then fresh_var (var + STR ''z'') (remove_var var s)
      else var)"
  by fastforce+
(*(* For some reason, by proving that this function terminates the definition of match_pattern
   no longer terminates. *)
termination
  apply (relation "measure (\<lambda>(v, s). (fcard (fst s)))")
  apply simp
  using fcard_fminus1_less by force*)

fun fresh :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope \<times> VarName" where
  "fresh var s = (let v = fresh_var var s in (add_var v s, v))"


lemma fresh [code]:
  "fresh_var var s = 
    (if var |\<in>| (fst s) 
      then fresh_var (var + STR ''z'') (remove_var var s)
      else var)"
  sorry (* This will not be required when termination is proved *)



subsection \<open>Match Primitives\<close>
datatype MATCH =
  match VarName PatternExpr |
  equality VarName VarName (infixl "==" 52) |
  seq MATCH MATCH (infixl "&&" 50) |
  either MATCH MATCH (infixl "||" 49) |
  noop

text \<open>The definitions of la and ra help to feed the scope through when generating a match pattern.\<close>
definition la :: "('b \<Rightarrow> 'a) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'b) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'a)"
  (infix "\<langle>" 65)
  where
  "la f f' s = (fst (f' s), f (snd (f' s)))"

definition ra :: "(Scope \<Rightarrow> Scope \<times> ('b \<Rightarrow> 'a)) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'b) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'a)"
  (infixl "\<rangle>" 54)
  where
  "ra f f' s = ((fst (f' (fst (f s)))), (snd (f s)) (snd (f' (fst (f s)))))"

text \<open>Join generates the lhs and feeds the scope through to then generate the rhs.
      The resulting match pattern is an sequential match of the lhs and rhs, @{term "lhs && rhs"}.
      The resulting scope is the result of generating the rhs after the lhs.\<close>
definition join :: "('b \<Rightarrow> 'c \<times> MATCH) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a \<times> MATCH) \<Rightarrow> 'b \<Rightarrow> 'a \<times> MATCH" (infixl "|>" 53) where
  "join x y s = 
    (let (lhs_scope, lhs_match) = x s in
    (let (rhs_scope, rhs_match) = (y s lhs_scope) in
    (rhs_scope, (lhs_match && rhs_match))))"

abbreviation descend where
  "descend f e v \<equiv> (\<lambda>s s'. f e (snd (fresh v s)) s')"

fun register_name where
  "register_name (s, m) vn v = (s, m(vn\<mapsto>v))"

fun match_pattern :: "IRExpr \<Rightarrow> VarName \<Rightarrow> Scope \<Rightarrow> Scope \<times> MATCH" where
  "match_pattern (UnaryExpr op e) v =
    match v \<langle>
      (UnaryPattern op \<langle> fresh STR ''a'')
    |> descend match_pattern e STR ''a''" |
  "match_pattern (BinaryExpr op e1 e2) v =
    match v \<langle> 
      (BinaryPattern op \<langle> fresh STR ''a'' \<rangle> fresh STR ''b'')
    |> descend match_pattern e1 STR ''a''
    |> descend match_pattern e2 STR ''b''" |
  "match_pattern (ConditionalExpr b e1 e2) v =
    match v \<langle>
      (ConditionalPattern \<langle> fresh STR ''a'' \<rangle> fresh STR ''b'' \<rangle> fresh STR ''c'')
    |> descend match_pattern b STR ''a''
    |> descend match_pattern e1 STR ''b''
    |> descend match_pattern e2 STR ''c''" |
  \<comment> \<open>If a variable is reused, generate an equality check, else, generate a noop.\<close>
  "match_pattern (VariableExpr vn st) v = 
    (\<lambda>s. case (snd s) vn of 
      None \<Rightarrow> (register_name s vn v, noop) |
      Some v' \<Rightarrow> (register_name s vn v, equality v' v))" |
  "match_pattern (ConstantExpr c) v =
    (\<lambda>s. (s, match v (ConstantPattern c)))"


subsubsection \<open>Match Primitive Semantics\<close>
type_synonym Subst = "VarName \<Rightarrow> IRExpr option"

fun eval_match :: "MATCH \<Rightarrow> Subst \<Rightarrow> Subst option" where
  "eval_match (match v (UnaryPattern op1 x)) s =
    (case s v of 
      Some (UnaryExpr op2 xe) \<Rightarrow>
        (if op1 = op2 then Some (s(x\<mapsto>xe)) else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (BinaryPattern op1 x y)) s =
    (case s v of
      Some (BinaryExpr op2 xe ye) \<Rightarrow>
        (if op1 = op2 
          then Some (s(x\<mapsto>xe) ++ s(y\<mapsto>ye))
          else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (ConditionalPattern c tb fb)) s =
    (case s v of
      Some (ConditionalExpr ce te fe) \<Rightarrow>
        (Some (s(c\<mapsto>ce) ++ s(tb\<mapsto>te) ++ s(fb\<mapsto>fe))) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (ConstantPattern c1)) s =
    (case s v of 
      Some (ConstantExpr c2) \<Rightarrow>
        (if c1 = c2 then Some s else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (equality v1 v2) s =
    (if s v1 = s v2 then Some s else None)" |
  "eval_match (seq m1 m2) s =
      (case eval_match m1 s of 
        None \<Rightarrow> None |
        Some s' \<Rightarrow> eval_match m2 s')" |
  "eval_match (either m1 m2) s =
      (case eval_match m1 s of
        None \<Rightarrow> eval_match m2 s |
        Some s' \<Rightarrow> Some s')" |
  "eval_match noop s = Some s" |
  "eval_match _ s = None"


subsection \<open>Combining Rules\<close>

datatype Rules =
  base IRExpr |
  cond MATCH Rules (infixl "?" 52) |
  else Rules Rules (infixl "else" 50)

text \<open>Use the scope of a generated match to replace real variable names with aliases in the rewrite result.\<close>
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

fun generate :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> Rules" where
  "generate p r = 
    (let (s, m) = match_pattern p STR ''e'' ({||}, (\<lambda>x. None))
     in (m ? (base (expr_result r s))))"


subsubsection \<open>Rules Semantics\<close>
definition start_unification where
  "start_unification e = ((\<lambda>x. None)(STR ''e'' := Some e))"

text \<open>Replace any variable expressions with value in a substitution.\<close>
fun ground_expr :: "IRExpr \<Rightarrow> Subst \<Rightarrow> IRExpr option" where
  "ground_expr (VariableExpr v s) u = u v" |
  "ground_expr (UnaryExpr op e) u = (case (ground_expr e u)
    of None \<Rightarrow> None | Some e' \<Rightarrow> Some (UnaryExpr op e'))" |
  "ground_expr (BinaryExpr op e1 e2) u = (case (ground_expr e1 u)
    of None \<Rightarrow> None | Some e1' \<Rightarrow> 
    (case (ground_expr e2 u)
      of None \<Rightarrow> None | Some e2' \<Rightarrow> Some (BinaryExpr op e1' e2')))" |
  "ground_expr (ConditionalExpr e1 e2 e3) u = (case (ground_expr e1 u)
    of None \<Rightarrow> None | Some e1' \<Rightarrow>
    (case (ground_expr e2 u)
      of None \<Rightarrow> None | Some e2' \<Rightarrow>
        (case (ground_expr e2 u)
          of None \<Rightarrow> None | Some e3' \<Rightarrow> Some (ConditionalExpr e1' e2' e3'))))" |
  "ground_expr e u = Some e"

fun eval_rules :: "Rules \<Rightarrow> Subst \<Rightarrow> IRExpr option" where
  "eval_rules (base e) u = ground_expr e u" |
  "eval_rules (cond m r) u = (case (eval_match m u) of
    None \<Rightarrow> None |
    Some u' \<Rightarrow> eval_rules r u')" |
  "eval_rules (r1 else r2) u = (case (eval_rules r1 u) of
    None \<Rightarrow> (eval_rules r2 u) |
    Some r \<Rightarrow> Some r)"



experiment begin
fun rules_bases :: "Rules \<Rightarrow> IRExpr set" where
  "rules_bases (base e) = {e}" |
  "rules_bases (cond m r) = rules_bases r" |
  "rules_bases (r1 else r2) = rules_bases r1 \<union> rules_bases r2"

fun rules_vars :: "Rules \<Rightarrow> VarName fset" where
  "rules_vars (base e) = vars e" |
  "rules_vars (cond m r) = rules_vars r" |
  "rules_vars (r1 else r2) = rules_vars r1 |\<union>| rules_vars r2"

fun pattern_vars :: "PatternExpr \<Rightarrow> String.literal fset" where
  "pattern_vars (UnaryPattern op v1) = {|v1|}" |
  "pattern_vars (BinaryPattern op v1 v2) = {|v1, v2|}" |
  "pattern_vars (ConditionalPattern v1 v2 v3) = {|v1, v2, v3|}" |
  "pattern_vars (VariablePattern v1) = {|v1|}" |
  "pattern_vars (ConstantPattern c) = {||}"

fun match_vars :: "MATCH \<Rightarrow> String.literal fset" where
  "match_vars (match v p) = pattern_vars p" |
  "match_vars (seq m1 m2) = match_vars m1 |\<union>| match_vars m2" |
  "match_vars (either m1 m2) = match_vars m1 |\<union>| match_vars m2" |
  "match_vars _ = {||}"

fun valid_rule :: "Rules \<Rightarrow> bool" where
  "valid_rule (cond m e) = (rules_vars e |\<subseteq>| match_vars m)" |
  "valid_rule (e1 else e2) = (valid_rule e1 \<and> valid_rule e2)"

lemma unification_vars:
  assumes "eval_match m e = Some u"
  shows "\<forall>v . v |\<in>| match_vars m \<longrightarrow> (\<exists>e'. u v = Some e')"
using assms proof (induction m)
  case (match v p)
  then show ?case apply simp 
    apply (cases p) apply simp sorry
next
  case (equality x1 x2)
  then show ?case sorry
next
  case (seq m1 m2)
  then show ?case sorry
next
  case (either m1 m2)
  then show ?case sorry
next
  case noop
  then show ?case sorry
qed

lemma match_has_ground:
  assumes "valid_rule (rule m e)"
  shows "eval_match m (start_unification e') = Some u \<Longrightarrow> \<exists>e''. ground_expr e u = Some e''"
  using assms unfolding valid_rule.simps
proof -
  have u_pop: "\<forall>v. v |\<in>| vars e \<longrightarrow> (\<exists>e'. u v = Some e')"
    using assms unfolding valid_rule.simps sorry
  show ?thesis
  proof (induction e)
    case (UnaryExpr x1 e)
    then show ?case by fastforce
  next
    case (BinaryExpr x1 e1 e2)
    then show ?case by fastforce
  next
    case (ConditionalExpr e1 e2 e3)
    then show ?case by fastforce
  next
    case (ParameterExpr x1 x2)
    then show ?case by fastforce
  next
    case (LeafExpr x1 x2)
    then show ?case by fastforce
  next
    case (ConstantExpr x)
    then show ?case by fastforce
  next
    case (ConstantVar x)
    then show ?case by fastforce
  next
    case (VariableExpr x1 x2)
    have "x1 |\<in>| vars e"
      sorry
    then show ?case using u_pop by simp
  qed
qed

lemma rule_12:
  assumes "valid_rule ((c1 ? e) else (c2 ? e))"
  assumes "valid_rule ((c1 || c2) ? e)"
  shows "eval_rules ((c1 ? e) else (c2 ? e)) u = eval_rules ((c1 || c2) ? e) u"
proof (cases "eval_match c1 u")
  case None
  then show ?thesis 
    unfolding eval_rules.simps
    by force
next
  case a: (Some c1u)
  then show ?thesis
  proof (cases "eval_match c2 u")
    case None
    then show ?thesis unfolding eval_rules.simps
      by (metis eval_match.simps(7) option.case_eq_if option.collapse)
  next
    case b: (Some c2u)
    then show ?thesis using a unfolding eval_rules.simps eval_match.simps 
      apply auto[1] using assms sorry
  qed
qed
end



subsection \<open>Rule Optimization\<close>

fun elim_noop :: "MATCH \<Rightarrow> MATCH" where
  "elim_noop (lhs && noop) = elim_noop lhs" |
  "elim_noop (noop && rhs) = elim_noop rhs" |
  "elim_noop (lhs && rhs) = ((elim_noop lhs) && (elim_noop rhs))" |
  "elim_noop m = m"

lemma noop_semantics_rhs:
  "eval_match (lhs && noop) s = eval_match lhs s"
  by (simp add: option.case_eq_if)

lemma noop_semantics_lhs:
  "eval_match (noop && rhs) s = eval_match rhs s"
  by simp

lemma seq_det_lhs:
  assumes "\<forall>s. eval_match lhs1 s = eval_match lhs2 s"
  shows "eval_match (lhs1 && rhs) s = eval_match (lhs2 && rhs) s"
  using assms by simp

lemma seq_det_rhs:
  assumes "\<forall>s. eval_match rhs1 s = eval_match rhs2 s"
  shows "eval_match (lhs && rhs1) s = eval_match (lhs && rhs2) s"
proof (cases "eval_match lhs s")
  case None
  then show ?thesis by simp
next
  case (Some a)
  then obtain s' where s': "eval_match lhs s = Some s'"
    by simp
  then have lhs: "eval_match (lhs && rhs1) s = eval_match rhs1 s'"
    by simp
  from s' have rhs: "eval_match (lhs && rhs2) s = eval_match rhs2 s'"
    by simp
  from lhs rhs show ?thesis using assms
    by simp
qed

lemma sound_optimize_noop:
  "eval_match m s = eval_match (elim_noop m) s"
  apply (induction m arbitrary: s rule: elim_noop.induct)
  using noop_semantics_rhs apply force+
  using seq_det_rhs apply force+
  using elim_noop.simps(17) elim_noop.simps(24) seq_det_rhs apply presburger
  by force+

fun eliminate_noop :: "Rules \<Rightarrow> Rules" where
  "eliminate_noop (base e) = base e" |
  "eliminate_noop (m ? r) = elim_noop m ? eliminate_noop r" |
  "eliminate_noop (r1 else r2) = (eliminate_noop r1 else eliminate_noop r2)"

lemma eliminate_noop_valid:
  "eval_rules r u = eval_rules (eliminate_noop r) u"
  apply (induction r arbitrary: u rule: eliminate_noop.induct)
  apply simp
  using eliminate_noop.simps(2) eval_rules.simps(2) sound_optimize_noop apply presburger
  using eliminate_noop.simps(3) eval_rules.simps(3) by presburger

fun combined_size :: "Rules \<Rightarrow> nat" where
  "combined_size (m ? r) = (2 * size m) + combined_size r" |
  "combined_size (base e) = 0" |
  "combined_size (r1 else r2) = combined_size r1 + combined_size r2"

function (sequential) lift_match :: "Rules \<Rightarrow> Rules" where
  "lift_match (r1 else r2) = ((lift_match r1) else (lift_match r2))" |
  "lift_match ((m1 && m2) ? r) = (lift_match (m1 ? (m2 ? r)))" |
  "lift_match (m ? r) = m ? (lift_match r)" |
  "lift_match r = r"
  by pat_completeness auto
termination lift_match
  apply (relation "measures [combined_size, size]") apply auto[1]
  apply auto[1] apply auto[1] apply simp
  apply simp subgoal for m2 r apply (cases m2) by (simp add: lift_match.psimps(4))
  apply simp
  by simp

lemma chain_equiv:
  "eval_rules (m1 ? (m2 ? r)) u = eval_rules ((m1 && m2) ? r) u"
  by (metis eval_match.simps(6) eval_rules.simps(2) option.case_eq_if)

lemma lift_match_valid:
  "eval_rules r u = eval_rules (lift_match r) u"
  apply (induction r arbitrary: u rule: lift_match.induct) 
  using eval_rules.simps(3) lift_match.simps(1) apply presburger
  using chain_equiv apply force
  using eval_rules.simps(2) lift_match.simps(3) apply presburger
  apply simp
  using eval_rules.simps(2) lift_match.simps(5) apply presburger
  apply simp
  by simp

(*
fun lift_common :: "Rules \<Rightarrow> Rules" where
  "lift_common (m1 ? r1 else m2 ? r2) = 
    (if m1 = m2
      then m1 ? (lift_common (r1 else r2))
      else (lift_common (m1 ? r1) else lift_common (m2 ? r2)))" |
  "lift_common (r1 else r2) = ((lift_common r1) else (lift_common r2))" |
  "lift_common (m ? r) = (m ? (lift_common r))" |
  "lift_common (base e) = base e"*)

fun join_conditions :: "Rules \<Rightarrow> Rules option" where
  "join_conditions (m1 ? r1 else m2 ? r2) = 
    (if m1 = m2
      then Some (m1 ? (r1 else r2)) else None)" |
  "join_conditions (m1 ? (m2 ? r1)) = 
    (if m1 = m2
      then Some ((m1 ? r1)) else None)" |
  "join_conditions r = None"

lemma join_conditions_shrinks:
  "join_conditions r = Some r' \<Longrightarrow> size r' < size r"
  apply (induction r rule: join_conditions.induct)
  apply (metis One_nat_def Rules.size(5) Rules.size(6) add.commute add_Suc_right join_conditions.simps(1) lessI option.distinct(1) option.inject plus_1_eq_Suc)
  apply (metis One_nat_def Rules.size(5) join_conditions.simps(2) less_add_same_cancel1 less_numeral_extra(1) option.discI option.inject)
  by simp+

function lift_common :: "Rules \<Rightarrow> Rules" where
  "lift_common (r1 else r2) = (
    case join_conditions (r1 else r2) 
    of Some r \<Rightarrow> lift_common r |
       None \<Rightarrow> (lift_common r1 else lift_common r2))" |
  "lift_common (m ? r) = (
    case join_conditions r 
    of Some r' \<Rightarrow> lift_common (m ? r') |
       None \<Rightarrow> (m ? lift_common r))" |
  "lift_common (base e) = base e"
  using combined_size.cases apply blast
  by simp+
termination
  apply (relation "measures [size]") apply auto[1]
    apply simp subgoal for r1 r2 apply (induction r1 rule: join_conditions.induct) by simp+
   apply auto[2]
  using join_conditions_shrinks apply fastforce
  by (simp add: join_conditions_shrinks)

  

(*lemma lift_common_valid:
  "eval_rules r u = eval_rules (lift_common r) u"
  apply (induction r arbitrary: u rule: lift_common.induct)
  using eval_rules.simps(2) eval_rules.simps(3) lift_common.simps(1) option.case_eq_if
  sledgehammer
  apply (smt (verit, del_insts))
  using eval_rules.simps(3) lift_common.simps(2) apply presburger
  apply (metis eval_rules.simps(3) lift_common.simps(3))
  apply simp
  apply (metis eval_rules.simps(3) lift_common.simps(5))
  using eval_rules.simps(2) lift_common.simps(6) apply presburger
  by simp*)

definition optimized_export where
  "optimized_export = lift_common o lift_match o eliminate_noop"

(*lemma optimized_export_valid:
  "eval_rules r u = eval_rules (optimized_export r) u"
  unfolding optimized_export_def comp_def
  using lift_common_valid lift_match_valid eliminate_noop_valid by simp*)


subsection \<open>Java Generation\<close>

fun unary_op_class :: "IRUnaryOp \<Rightarrow> string" where
  "unary_op_class UnaryAbs = ''AbsNode''" |
  "unary_op_class UnaryNeg = ''NegNode''" |
  "unary_op_class UnaryNot = ''NotNode''" |
  "unary_op_class UnaryLogicNegation = ''LogicNegationNode''" |
  "unary_op_class (UnaryNarrow _ _) = ''NarrowNode''" |
  "unary_op_class (UnarySignExtend _ _) = ''SignExtendNode''" |
  "unary_op_class (UnaryZeroExtend _ _) = ''ZeroExtendNode''"

fun binary_op_class :: "IRBinaryOp \<Rightarrow> string" where
  "binary_op_class BinAdd = ''AddNode''" |
  "binary_op_class BinMul = ''MulNode''" |
  "binary_op_class BinSub = ''SubNode''" |
  "binary_op_class BinAnd = ''AndNode''" |
  "binary_op_class BinOr = ''OrNode''" |
  "binary_op_class BinXor = ''XorNode''" |
  "binary_op_class BinShortCircuitOr = ''ShortCircuitOrNode''" |
  "binary_op_class BinLeftShift = ''LeftShiftNode''" |
  "binary_op_class BinRightShift = ''RightShiftNode''" |
  "binary_op_class BinURightShift = ''UnaryRightShiftNode''" |
  "binary_op_class BinIntegerEquals = ''IntegerEqualsNode''" |
  "binary_op_class BinIntegerLessThan = ''IntegerLessThanNode''" |
  "binary_op_class BinIntegerBelow = ''IntegerBelowNode''"

fun export_pattern :: "PatternExpr \<Rightarrow> string" where
  "export_pattern (UnaryPattern op v) = unary_op_class op" |
  "export_pattern (BinaryPattern op v1 v2) = binary_op_class op" |
  "export_pattern (ConditionalPattern v1 v2 v3) = ''ConditionalNode''" |
  "export_pattern (ConstantPattern v) = ''ConstantNode''" |
  "export_pattern (VariablePattern v) = ''ERROR: Variable should not occur on LHS''"

(* https://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle *)
fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of (48 + n)] else 
     string_of_nat (n div 10) @ [char_of (48 + (n mod 10))])"

definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else 
     string_of_nat (nat i))"

fun export_value :: "Value \<Rightarrow> string" where
  "export_value (IntVal s v) = string_of_int (sint v)" |
  "export_value _ = ''ERROR: unsupported Value''"

fun export_assignments :: "VarName \<Rightarrow> PatternExpr \<Rightarrow> string" where
  "export_assignments v (UnaryPattern op v1) = 
    ''var '' @ String.explode v1 @ '' = '' @ String.explode v @ ''.getX();
''" |
  "export_assignments v (BinaryPattern op v1 v2) = 
    ''var '' @ String.explode v1 @ '' = '' @ String.explode v @ ''.getX();
var '' @ String.explode v2 @ '' = '' @ String.explode v @ ''.getY();
''" |
  "export_assignments v (ConditionalPattern v1 v2 v3) =
    ''var '' @ String.explode v1 @ '' = '' @ String.explode v @ ''.condition();
var '' @ String.explode v2 @ '' = '' @ String.explode v @ ''.trueValue();
var '' @ String.explode v3 @ '' = '' @ String.explode v @ ''.falseValue();
''" |
  "export_assignments v (ConstantPattern val) =
    ''if ('' @ String.explode v @ ''.getValue() == '' @ export_value val @ '') {''"

fun export_match :: "MATCH \<Rightarrow> string" where
  "export_match (match v p) = ''if ('' @ String.explode v @ '' instanceof '' @ export_pattern p @ '') {
'' @ export_assignments v p" |
  "export_match (seq m1 m2) = export_match m1 @ '''' @ export_match m2" |
  "export_match (equality v1 v2) = ''if ('' @ String.explode v1 @ '' == '' @ String.explode v2 @ '') {
''" |
  "export_match noop = ''''"

fun export_irexpr :: "IRExpr \<Rightarrow> string" where
  "export_irexpr (UnaryExpr op e1) =
    ''new '' @ unary_op_class op @ ''('' @ export_irexpr e1 @ '')''" |
  "export_irexpr (BinaryExpr op e1 e2) =
    ''new '' @ binary_op_class op @ ''('' @ export_irexpr e1 @ '', '' @ export_irexpr e2 @ '')''" |
  "export_irexpr (ConditionalExpr e1 e2 e3) =
    ''new ConditionalNode('' @ export_irexpr e1 @ '', '' @ export_irexpr e2 @ '', '' @ export_irexpr e3 @ '')''" |
  "export_irexpr (ConstantExpr val) =
    ''new ConstantNode('' @ export_value val @ '')''" |
  "export_irexpr (VariableExpr v s) = String.explode v"

fun close :: "MATCH \<Rightarrow> string" where
  "close (match v (ConstantPattern val)) = ''
}
}''" |
  "close (match v p) = ''
}''" |
  "close (seq m1 m2) = close m1 @ close m2" |
  "close (equality v1 v2) = ''
}''" |
  "close noop = ''''"

fun export_rules :: "Rules \<Rightarrow> string" where
  "export_rules (base e) = ''return '' @ export_irexpr e @ '';''" |
  "export_rules (cond m r) = export_match m @ export_rules r @ close m" |
  "export_rules (r1 else r2) = export_rules r1 @ ''
'' @ export_rules r2"

subsection \<open>Experiments\<close>

definition var :: "string \<Rightarrow> IRExpr" where
  "var v = (VariableExpr (String.implode v) VoidStamp)"

subsubsection \<open>Generated Rules\<close>

text \<open>@{text "\<not>(\<not>x) \<longrightarrow> x"}\<close>
definition NestedNot where
  "NestedNot = generate
    (UnaryExpr UnaryNot (UnaryExpr UnaryNot (var ''x'')))
    (var ''x'')"

text \<open>@{text "(x - y) + y \<longrightarrow> x"}\<close>
definition RedundantSub where
  "RedundantSub = generate 
    (BinaryExpr BinAdd
      (BinaryExpr BinSub (var ''x'') (var ''y''))
      (var ''y''))
    (var ''x'')"

text \<open>@{text "x + -e \<longmapsto> x - e"}\<close>
definition AddLeftNegateToSub where
  "AddLeftNegateToSub = generate 
    (BinaryExpr BinAdd
      (var ''x'')
      (UnaryExpr UnaryNeg (var ''e'')))
    (BinaryExpr BinSub (var ''x'') (var ''e''))"

corollary
  "NestedNot =
   (MATCH.match STR ''e'' (UnaryPattern UnaryNot STR ''a'') &&
    (MATCH.match STR ''a'' (UnaryPattern UnaryNot STR ''az'') && noop)) ?
      base (VariableExpr STR ''az'' VoidStamp)"
  by eval

corollary
  "RedundantSub =
   (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') &&
    (MATCH.match STR ''a'' (BinaryPattern BinSub STR ''az'' STR ''bz'') && noop && noop) &&
      STR ''bz'' == STR ''b'') ?
        base (VariableExpr STR ''az'' VoidStamp)"
  by eval

corollary
  "AddLeftNegateToSub =
   (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') && noop &&
    (MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') && noop)) ?
      base (BinaryExpr BinSub 
            (VariableExpr STR ''a'' VoidStamp)
            (VariableExpr STR ''az'' VoidStamp))"
  by eval


subsubsection \<open>Rule Application\<close>
text \<open>@{text "\<not>(\<not>1)"}\<close>
definition NestedNot_ground where
  "NestedNot_ground = (UnaryExpr UnaryNot (UnaryExpr UnaryNot (ConstantExpr (IntVal 32 1))))"

text "1"
definition NestedNot_result where
  "NestedNot_result = (ConstantExpr (IntVal 32 1))"

text "(15 - 10) + 10"
definition RedundantSub_ground where
  "RedundantSub_ground = (BinaryExpr BinAdd 
          (BinaryExpr BinSub (ConstantExpr (IntVal 32 15)) (ConstantExpr (IntVal 32 10)))
          (ConstantExpr (IntVal 32 10)))"

text "15"
definition RedundantSub_result where
  "RedundantSub_result = (ConstantExpr (IntVal 32 15))"

text "10 - (-15)"
definition AddLeftNegateToSub_ground where
  "AddLeftNegateToSub_ground = (BinaryExpr BinAdd 
          (ConstantExpr (IntVal 32 10))
          (UnaryExpr UnaryNeg (ConstantExpr (IntVal 32 15))))"

text "10 + 15"
definition AddLeftNegateToSub_result where
  "AddLeftNegateToSub_result = (BinaryExpr BinSub
          (ConstantExpr (IntVal 32 10))
          (ConstantExpr (IntVal 32 15)))"

corollary
  "eval_rules NestedNot (start_unification NestedNot_ground)
    = Some NestedNot_result"
  by eval

corollary
  "eval_rules RedundantSub (start_unification RedundantSub_ground)
    = Some RedundantSub_result"
  by eval

corollary
  "eval_rules AddLeftNegateToSub (start_unification RedundantSub_ground) = None"
  by eval

corollary
  "eval_rules AddLeftNegateToSub (start_unification AddLeftNegateToSub_ground)
    = Some AddLeftNegateToSub_result"
  by eval

subsubsection \<open>Rule Combinations\<close>

corollary
  "eval_rules (RedundantSub else AddLeftNegateToSub) (start_unification RedundantSub_ground)
    = Some RedundantSub_result"
  by eval

corollary
  "eval_rules (RedundantSub else AddLeftNegateToSub) (start_unification AddLeftNegateToSub_ground)
    = Some AddLeftNegateToSub_result"
  by eval

corollary
  "eval_rules (AddLeftNegateToSub else RedundantSub) (start_unification RedundantSub_ground)
    = Some RedundantSub_result"
  by eval

corollary
  "eval_rules (AddLeftNegateToSub else RedundantSub) (start_unification AddLeftNegateToSub_ground)
    = Some AddLeftNegateToSub_result"
  by eval

subsubsection \<open>Rule Optimization\<close>

corollary
  "lift_match (RedundantSub else AddLeftNegateToSub) =
  (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') ?
  (MATCH.match STR ''a'' (BinaryPattern BinSub STR ''az'' STR ''bz'') ?
  (noop ? (noop ? 
  (STR ''bz'' == STR ''b'' ?
    base (VariableExpr STR ''az'' VoidStamp)))))
    else
  MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') ?
  (noop ?
  (MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') ?
  (noop ?
    base (BinaryExpr BinSub (VariableExpr STR ''a'' VoidStamp) (VariableExpr STR ''az'' VoidStamp))))))"
  by eval

corollary
  "lift_common (lift_match (RedundantSub else AddLeftNegateToSub)) =
   MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') ?
    (MATCH.match STR ''a'' (BinaryPattern BinSub STR ''az'' STR ''bz'') ?
    (noop ? ((STR ''bz'' == STR ''b'' ? base (VariableExpr STR ''az'' VoidStamp))))
    else
    noop ?
    (MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') ?
    (noop ? base (BinaryExpr BinSub (VariableExpr STR ''a'' VoidStamp) (VariableExpr STR ''az'' VoidStamp)))))"
  by eval

corollary
  "optimized_export (RedundantSub else AddLeftNegateToSub) =
   MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') ?
    (MATCH.match STR ''a'' (BinaryPattern BinSub STR ''az'' STR ''bz'') ?
     (STR ''bz'' == STR ''b'' ?
      base (VariableExpr STR ''az'' VoidStamp))
    else
    MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') ?
     base (BinaryExpr BinSub (VariableExpr STR ''a'' VoidStamp) (VariableExpr STR ''az'' VoidStamp)))"
  by eval

subsubsection \<open>Java Generation\<close>

value "export_rules RedundantSub"
value "export_rules AddLeftNegateToSub"
value "export_rules (RedundantSub else AddLeftNegateToSub)"

value "export_rules (lift_common (lift_match (RedundantSub else AddLeftNegateToSub)))"
value "export_rules (optimized_export (RedundantSub else AddLeftNegateToSub))"

value "lift_match (eliminate_noop (NestedNot else RedundantSub else AddLeftNegateToSub))"
value "export_rules (optimized_export ((RedundantSub else AddLeftNegateToSub) else NestedNot))"
value "export_rules (optimized_export (NestedNot else RedundantSub else AddLeftNegateToSub))"

no_notation cond (infixl "?" 52)

end
