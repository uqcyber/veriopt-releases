theory MatchPrims
  imports Main
begin

datatype 'a MatchPrims =
  id | fail |
  extract_ string "'a \<Rightarrow> 'a" (infixr "\<leftarrow>" 75) |
  eq_ string string (infix "=?" 70) |
  typeis "'a \<Rightarrow> bool" |
  replace 'a |
  seq "'a MatchPrims" "'a MatchPrims" (infixl ";" 45) |
  cond "'a MatchPrims" "'a MatchPrims" (infixl "?" 45) |
  scope_ "'a MatchPrims" ("\<lbrace>_\<rbrace>")

type_synonym 'a binding = "(string, 'a) map"

class groundable =
  fixes ground :: "'a \<Rightarrow> 'a binding \<Rightarrow> 'a"

fun eval :: "('a::groundable) MatchPrims \<Rightarrow> 'a \<Rightarrow> 'a binding \<Rightarrow> ('a \<times> 'a binding \<times> bool)" where
  "eval id C \<sigma> = (C, \<sigma>, True)" |
  "eval fail C \<sigma> = (C, \<sigma>, False)" |
  "eval (v \<leftarrow> f) C \<sigma> = (C, \<sigma>(v \<mapsto> f C), True)" |
  "eval (a =? b) C \<sigma> = (C, \<sigma>, \<sigma> a = \<sigma> b)" |
  "eval (typeis T) C \<sigma> = (C, \<sigma>, T C)" |
  "eval (replace e) C \<sigma> = (ground e \<sigma>, \<sigma>, True)" |
  "eval (a; b) C \<sigma> = (
    let (C', \<sigma>', \<beta>) = eval a C \<sigma>
    in eval b C' \<sigma>')" |
  "eval (a ? b) C \<sigma> = (
    let (C', \<sigma>', \<beta>) = eval a C \<sigma>
    in (if \<beta> then eval b C' \<sigma>' else (C', \<sigma>', False)))" |
  "eval \<lbrace>a\<rbrace> C \<sigma> = (
    let (C', \<sigma>', \<beta>) = eval a C \<sigma>
    in (C, \<sigma>', \<beta>))"

(*
inductive eval :: "('a::groundable) MatchPrims \<Rightarrow> 'a \<Rightarrow> 'a binding \<Rightarrow> 'a \<Rightarrow> 'a binding \<Rightarrow> bool \<Rightarrow> bool"
  ("_'(_,_') \<rightarrow> '(_,_,_')") where
  "id(C, \<sigma>) \<rightarrow> (C, \<sigma>, True)" |
  "fail(C, \<sigma>) \<rightarrow> (C, \<sigma>, False)" |
  "(v \<leftarrow> f)(C, \<sigma>) \<rightarrow> (C, \<sigma>(v \<mapsto> f C), True)" |
  "(a == b)(C, \<sigma>) \<rightarrow> (C, \<sigma>, \<sigma> a = \<sigma> b)" |
  "(typeis T)(C, \<sigma>) \<rightarrow> (C, \<sigma>, T C)" |
  "(replace e)(C, \<sigma>) \<rightarrow> (ground e \<sigma>, \<sigma>, True)" |

  "\<lbrakk>(a(C, \<sigma>) \<rightarrow> (C', \<sigma>', \<beta>)); (b(C', \<sigma>') \<rightarrow> (C'', \<sigma>'', \<beta>'))\<rbrakk>
    \<Longrightarrow> (a; b)(C, \<sigma>) \<rightarrow> (C'', \<sigma>'', \<beta>')" |
  "\<lbrakk>(a(C, \<sigma>) \<rightarrow> (C', \<sigma>', True)); (b(C', \<sigma>') \<rightarrow> (C'', \<sigma>'', \<beta>'))\<rbrakk>
    \<Longrightarrow> (a ? b)(C, \<sigma>) \<rightarrow> (C'', \<sigma>'', \<beta>')" |
  "\<lbrakk>(a(C, \<sigma>) \<rightarrow> (C', \<sigma>', False))\<rbrakk>
    \<Longrightarrow> (a ? b)(C, \<sigma>) \<rightarrow> (C', \<sigma>', False)" |
  "a(C, \<sigma>) \<rightarrow> (C', \<sigma>', \<beta>) \<Longrightarrow> {a}(C, \<sigma>) \<rightarrow> (C, \<sigma>', \<beta>)"

inductive eval_top :: "('a::groundable) MatchPrims \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  ("[[_]]_ = _") where
  "r(C, Map.empty) \<rightarrow> (C', \<sigma>, \<beta>) \<Longrightarrow> [[r]]C = C'"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) eval .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) eval_top .
*)

definition eval_top :: "('a::groundable) MatchPrims \<Rightarrow> 'a \<Rightarrow> 'a"
  ("\<lbrakk>_\<rbrakk>_" [65,65] 66) where
  "\<lbrakk>r\<rbrakk>C = fst (eval r C Map.empty)"


datatype (discs_sels) Arith = Add (x: Arith) (y: Arith) | Sub (x: Arith) (y: Arith) | Const int | Var string

instantiation Arith :: groundable
begin
fun ground_Arith :: "Arith \<Rightarrow> Arith binding \<Rightarrow> Arith" where
  "ground_Arith (Add a b) \<sigma> = Add (ground_Arith a \<sigma>) (ground_Arith b \<sigma>)" |
  "ground_Arith (Sub a b) \<sigma> = Sub (ground_Arith a \<sigma>) (ground_Arith b \<sigma>)" |
  "ground_Arith (Const n) \<sigma> = Const n" |
  "ground_Arith (Var v) \<sigma> = (case \<sigma> v of None \<Rightarrow> Var v | Some v' \<Rightarrow> v')"

instance by standard
end


definition subopt :: "Arith MatchPrims" where
  "subopt = (typeis is_Sub ? ''u'' \<leftarrow> x ? ''v'' \<leftarrow> y ? \<lbrace>replace (Var ''u'') ? typeis is_Add ? ''a'' \<leftarrow> x ? ''b'' \<leftarrow> y\<rbrace> ? ''b'' =? ''v'' ? replace (Var ''a''))"

value "eval subopt (Sub (Add (Const 2) (Const 1)) (Const 1)) Map.empty"
value "eval subopt (Sub (Add (Const 2) (Const 2)) (Const 1)) Map.empty"
value "eval subopt (Sub (Sub (Const 2) (Const 1)) (Const 1)) Map.empty"

value "\<lbrakk>subopt\<rbrakk>(Sub (Add (Const 2) (Const 1)) (Const 1))"

(*
values "{(C', \<sigma>', \<beta>). subopt(Sub (Add (Const 2) (Const 1)) (Const 1), Map.empty) \<rightarrow> (C', \<sigma>', \<beta>)}"
values "{(C', \<sigma>', \<beta>). subopt(Sub (Add (Const 2) (Const 2)) (Const 1), Map.empty) \<rightarrow> (C', \<sigma>', \<beta>)}"
values "{(C', \<sigma>', \<beta>). subopt(Sub (Sub (Const 2) (Const 1)) (Const 1), Map.empty) \<rightarrow> (C', \<sigma>', \<beta>)}"

values "{(C'). [[subopt]](Sub (Add (Const 2) (Const 1)) (Const 1)) = C'}"
*)

lemma "\<lbrakk>fail\<rbrakk>C = C"
  by (simp add: eval_top_def)
lemma "\<lbrakk>id\<rbrakk>C = C"
  by (simp add: eval_top_def)


abbreviation "match T a b \<equiv> (typeis T ? (a \<leftarrow> x) ? (b \<leftarrow> y))"

definition subopt' :: "Arith MatchPrims" where
  "subopt' = (match is_Sub ''u'' ''v'' ? \<lbrace>replace (Var ''u'') ? match is_Add ''a'' ''b''\<rbrace> ? ''b'' =? ''v'' ? replace (Var ''a''))"

value "\<lbrakk>subopt'\<rbrakk>(Sub (Add (Const 2) (Const 1)) (Const 1))"
(*values "{(C'). [[subopt']](Sub (Add (Const 2) (Const 2)) (Const 1)) = C'}"*)

abbreviation focus :: "'a \<Rightarrow> 'a MatchPrims \<Rightarrow> 'a MatchPrims" 
  (infix ">>" 66) where
  "p >> q \<equiv> \<lbrace>replace p ? q\<rbrace>"

definition subopt'' :: "Arith MatchPrims" where
  "subopt'' = (match is_Sub ''u'' ''v'' ? (Var ''u'') >> (match is_Add ''a'' ''b'') ? ''b'' =? ''v'' ? replace (Var ''a''))"

value "\<lbrakk>subopt''\<rbrakk>(Sub (Add (Const 2) (Const 1)) (Const 1))"
(*values "{(C'). [[subopt']](Sub (Add (Const 2) (Const 1)) (Const 1)) = C'}"*)

definition strong_equiv :: "'a::groundable MatchPrims \<Rightarrow> 'a MatchPrims \<Rightarrow> bool"
  (infix "\<doteq>" 40) where
  "strong_equiv a b = (\<forall>C \<sigma>. (eval a C \<sigma> = eval b C \<sigma>))"

definition weak_equiv :: "'a::groundable MatchPrims \<Rightarrow> 'a MatchPrims \<Rightarrow> bool"
  (infix "\<triangleq>" 40) where
  "weak_equiv a b = (\<forall>C \<sigma>. (fst (eval a C \<sigma>) = fst (eval b C \<sigma>)))"

lemma strong_implies_weak:
  "a \<doteq> b \<Longrightarrow> a \<triangleq> b"
  by (simp add: eval_top_def strong_equiv_def weak_equiv_def)

lemma weak_equiv_comm:
  "(a \<triangleq> b) = (b \<triangleq> a)"
  using MatchPrims.weak_equiv_def by metis

lemma strong_equiv_comm:
  "(a \<doteq> b) = (b \<doteq> a)"
  using MatchPrims.strong_equiv_def by metis

lemma weak_equiv_trans:
  "(\<exists>b. a \<triangleq> b \<and> b \<triangleq> c) = (a \<triangleq> c)"
  using MatchPrims.weak_equiv_def by auto

lemma strong_equiv_trans:
  "(\<exists>b. a \<doteq> b \<and> b \<doteq> c) = (a \<doteq> c)"
  using MatchPrims.strong_equiv_def by auto

lemma "id \<triangleq> fail"
  by (simp add: MatchPrims.weak_equiv_def eval_top_def)

lemma "\<not>(id \<doteq> fail)"
  by (simp add: strong_equiv_def)

lemma "id ? a \<triangleq> a"
  by (simp add: MatchPrims.weak_equiv_def eval_top_def)

lemma "id ? a \<doteq> a"
  by (simp add: strong_equiv_def)

lemma "id ; a \<triangleq> a"
  by (simp add: MatchPrims.weak_equiv_def eval_top_def)

lemma "id ; a \<doteq> a"
  by (simp add: strong_equiv_def)

lemma "fail ? a \<triangleq> fail"
  by (simp add: MatchPrims.weak_equiv_def eval_top_def)

lemma "fail ? a \<doteq> fail"
  by (simp add: strong_equiv_def)

lemma "fail ; a \<triangleq> a"
  by (simp add: MatchPrims.weak_equiv_def eval_top_def)

lemma "a \<doteq> b \<Longrightarrow> (a ; c) \<doteq> (b ; c)"
  by (simp add: strong_equiv_def)

lemma "a \<doteq> b \<Longrightarrow> (a ; c) \<triangleq> (b ; c)"
  by (simp add: eval_top_def strong_equiv_def weak_equiv_def)

lemma "a \<doteq> b \<Longrightarrow> (c ; a) \<triangleq> (c ; b)"
  by (simp add: eval_top_def strong_equiv_def weak_equiv_def)

lemma "a \<doteq> b \<Longrightarrow> (c ; a) \<doteq> (c ; b)"
  by (simp add: strong_equiv_def)

lemma "a \<triangleq> b \<Longrightarrow> (c ; a) \<triangleq> (c ; b)"
  by (simp add: split_beta weak_equiv_def)

lemma "(a ? (b ? c)) \<doteq> ((a ? b) ? c)"
  by (simp add: prod.case_eq_if strong_equiv_def)

value "\<lbrakk>((''a'' \<leftarrow> x ? replace (Var ''a'')))\<rbrakk> (Sub (Const 1) (Const 2))"
value "\<lbrakk>((''a'' \<leftarrow> x ? replace (Var ''a'')) ; (''a'' \<leftarrow> x ? replace (Var ''a'')))\<rbrakk> (Sub (Const 1) (Const 2))"

lemma "\<lbrace>a\<rbrace> ; a \<doteq> a"
  unfolding strong_equiv_def
  apply (rule allI)+ subgoal for C \<sigma>
  proof (induction a C \<sigma> arbitrary: C \<sigma> rule: eval.induct)
    case (1 C \<sigma>)
    then show ?case by simp
  next
    case (2 C \<sigma>)
    then show ?case by simp
  next
    case (3 v f C \<sigma>)
    then show ?case by simp
  next
    case (4 a b C \<sigma>)
    then show ?case by simp
  next
    case (5 T C \<sigma>)
    then show ?case by simp
  next
    case (6 e C \<sigma>)
    then show ?case by simp
  next
    case (7 a b C' \<sigma>' C \<sigma>)
    then show ?case sorry
  next
    case (8 a b C \<sigma>)
    then show ?case sorry
  next
    case (9 a C \<sigma>)
    then show ?case sorry
  qed

(*
lemma "(a ? (b ; c)) \<doteq> ((a ? b) ; (a ? c))"
  unfolding strong_equiv_def apply (rule allI)+ subgoal for C \<sigma>
proof -
  obtain C' \<sigma>' \<beta> where "(C', \<sigma>', \<beta>) = eval a C \<sigma>"
    by (metis prod_cases3)
  then show ?thesis apply (cases \<beta>) sledgehammer
  by (simp add: prod.case_eq_if strong_equiv_def)
*)

lemma "(a =? a) \<doteq> id"
  by (simp add: strong_equiv_def)

end