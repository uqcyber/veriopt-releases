section "Expression Rewriting"
text \<open>Expressions that can be rewritten as other semantically equivalent expressions.\<close>

theory ExpressionRewrites
  imports
    Semantics
    Monotonic
    OperatorProperties
begin 

text \<open>
A rewrite (\isasymturnstile) is true if one expression can be rewritten by another expression with
the original semantics preserved.
\<close>
fun expression_rewrites :: "Node \<Rightarrow> Node \<Rightarrow> bool" (infixl "\<turnstile>" 50) where
  "expression_rewrites a b = (\<forall> s :: State . ((eval a s) \<tturnstile> (eval b s)))"

lemma expression_rewrites_def:
  fixes a b :: Node
  shows "a \<turnstile> b \<equiv> (\<forall> s :: State . ((eval a s) \<tturnstile> (eval b s)))"
  by auto

subsection "Subnode Rewrites"
text \<open>
Subnode Rewrites are theories for the binary and unary nodes that proof that
if a subnode, x, can be rewritten by another node, z, then the node can be
rewritten with the x subnode replaced with the node z.
\<close>
theorem binary_left_subnode_rewrite:
  fixes x y z :: Node
  fixes op :: BinaryOp
  assumes "x \<turnstile> z"
  shows "BinaryNode op x y \<turnstile> BinaryNode op z y"
proof (cases "op")
case AddOp
  then show ?thesis
    using MonotonicFunctions.add_monotonic assms monotonic_both_def monotonic_left_def by auto
next
case SubOp
  then show ?thesis
    using MonotonicFunctions.minus_monotonic assms monotonic_both_def monotonic_left_def by auto
next
  case MulOp
  then show ?thesis
    using MonotonicFunctions.times_monotonic assms monotonic_both_def monotonic_left_def by auto
next
  case DivOp
  then show ?thesis
    using MonotonicFunctions.divide_monotonic assms monotonic_both_def monotonic_left_def by auto
next
  case EqualOp
  then show ?thesis
    using MonotonicFunctions.equal_monotonic assms monotonic_left_def by auto
next
  case LessOp
  then show ?thesis
    using MonotonicFunctions.less_monotonic assms monotonic_both_def monotonic_left_def by auto
next
  case AndOp
  then show ?thesis
    using MonotonicFunctions.and_monotonic assms monotonic_both_def monotonic_left_def by auto
next
  case OrOp
then show ?thesis
  using MonotonicFunctions.or_monotonic assms monotonic_both_def monotonic_left_def by auto
next
  case XorOp
  then show ?thesis
    using MonotonicFunctions.xor_monotonic assms monotonic_both_def monotonic_left_def by auto
qed

theorem binary_right_subnode_rewrite:
  fixes x y z :: Node
  fixes op :: BinaryOp
  assumes "x \<turnstile> z"
  shows "BinaryNode op y x \<turnstile> BinaryNode op y z"
proof (cases "op")
case AddOp
  then show ?thesis
    using MonotonicFunctions.add_monotonic assms monotonic_both_def monotonic_right_def by auto
next
case SubOp
  then show ?thesis
    using MonotonicFunctions.minus_monotonic assms monotonic_both_def monotonic_right_def by auto
next
  case MulOp
  then show ?thesis
    using MonotonicFunctions.times_monotonic assms monotonic_both_def monotonic_right_def by auto
next
  case DivOp
  then show ?thesis
    using MonotonicFunctions.divide_monotonic assms monotonic_both_def monotonic_right_def by auto
next
  case EqualOp
  then show ?thesis
    using MonotonicFunctions.equal_monotonic assms monotonic_right_def by auto
next
  case LessOp
  then show ?thesis
    using MonotonicFunctions.less_monotonic assms monotonic_both_def monotonic_right_def by auto
next
  case AndOp
  then show ?thesis
    using MonotonicFunctions.and_monotonic assms monotonic_both_def monotonic_right_def by auto
next
  case OrOp
then show ?thesis
  using MonotonicFunctions.or_monotonic assms monotonic_both_def monotonic_right_def by auto
next
  case XorOp
  then show ?thesis
    using MonotonicFunctions.xor_monotonic assms monotonic_both_def monotonic_right_def by auto
qed

theorem unary_refines_subnode:
  fixes x y :: Node
  fixes op :: UnaryOp
  assumes refines: "x \<turnstile> y"
  shows "UnaryNode op x \<turnstile> UnaryNode op y"
proof (cases "op")
case AbsOp
  then show ?thesis
    using MonotonicFunctions.abs_monotonic assms monotonic_def by auto
next
case MinusOp
  then show ?thesis
    using MonotonicFunctions.uminus_monotonic assms monotonic_def by auto
next
  case NotOp
  then show ?thesis
    using MonotonicFunctions.not_monotonic assms monotonic_def by auto
qed


lemma reflexive_refinement:
  fixes v :: Value
  shows "v \<tturnstile> v"
  using refines.elims(3) by auto
  
subsection "Conditional Node Rewrites"
lemma negation:
  assumes "(eval x s) = (BooleanValue val)"
  shows "(Eval.bool (eval (UnaryNode NotOp x) s)) = (\<not>(Eval.bool (eval x s)))"
  by (simp add: Eval.bool.simps(1) Semantic.logicNot.simps(1) assms)

theorem rewrite_conditional_negated:
  fixes trueExp falseExp :: Node
  assumes nc: "\<forall> s :: State . (eval x s = BooleanValue val)"
  shows
  "(ConditionalNode (UnaryNode NotOp x) trueExp falseExp)
    \<turnstile> (ConditionalNode x falseExp trueExp)"
  using nc negation refines.elims(3) by fastforce

theorem rewrite_conditional_equal_xy:
  fixes cond x :: Node
  shows "(ConditionalNode cond x x) \<turnstile> (x)"
  by (simp add: reflexive_refinement)

theorem rewrite_conditional_true:
  fixes trueExp falseExp :: Node
  shows
  "(ConditionalNode (ConstNode (BooleanValue True)) trueExp falseExp)
    \<turnstile> trueExp"
  using refines.elims(3)
  by (simp add: Eval.bool.simps(1) reflexive_refinement)

theorem rewrite_conditional_false:
  fixes trueExp falseExp :: Node
  shows
  "(ConditionalNode (ConstNode (BooleanValue False)) trueExp falseExp)
    \<turnstile> falseExp"
  using rewrite_conditional_true
  by (simp add: Eval.bool.simps(1))

lemma either_or:
  fixes a :: Node
  shows "(ConditionalNode (BinaryNode EqualOp a a) a a) \<turnstile> a"
  using reflexive_refinement by simp

lemma equal_node_refinement:
  fixes a b :: Node
  fixes s :: State
  assumes nc: "(eval (BinaryNode EqualOp a b) s) = (BooleanValue True)"
  shows "(eval a s) \<tturnstile> (eval b s)"
proof - 
  have "(eval (BinaryNode EqualOp a b) s) \<tturnstile> (Semantic.equal (eval a s) (eval b s))" using nc by auto
  then have "((eval (BinaryNode EqualOp a b) s) \<tturnstile> (BooleanValue ((eval a s) = (eval b s))))
            \<or> ((eval (BinaryNode EqualOp a b) s) \<tturnstile> (UndefinedValue))"
    by (cases "eval a s"; cases "eval b s"; simp add: Semantic.equal.simps)
  then show ?thesis
    using nc
    by (simp add: reflexive_refinement)
qed

theorem rewrite_conditional_equal:
  fixes a b :: Node
  shows "(ConditionalNode (BinaryNode EqualOp a b) a b) \<turnstile> b"
  using either_or apply auto
  using equal_node_refinement
  by (metis (full_types) Eval.bool.elims(2) eval.simps(6))


subsection "Binary Node Rewrites"
lemma demorgans:
  shows "(Semantic.logicAnd (Semantic.logicNot x) (Semantic.logicNot y))
  \<tturnstile> (Semantic.logicNot (Semantic.logicOr x y))"
  apply (cases x; cases y; simp)
  by (simp add: Semantic.logicAnd.simps Semantic.logicNot.simps Semantic.logicOr.simps)+

theorem rewrite_demorgans:
  shows "(BinaryNode AndOp (UnaryNode NotOp x) (UnaryNode NotOp y))
  \<turnstile> (UnaryNode NotOp (BinaryNode OrOp x y))"
  using demorgans by simp

theorem rewrite_add_sub:
  fixes x y :: Node
  shows "(BinaryNode AddOp (BinaryNode SubOp x y) y) \<turnstile> x"
  apply auto
proof -
  fix s :: State
  show "Semantic.add (Semantic.sub (eval x s) (eval y s)) (eval y s) \<tturnstile> eval x s"
    by (cases "eval x s"; cases "eval y s"; simp add: Semantic.sub.simps Semantic.add.simps)
qed

theorem rewrite_add_sub2:
  fixes x y :: Node
  shows "BinaryNode AddOp x (BinaryNode SubOp y x) \<turnstile> y"
  apply auto
proof -
  fix s :: State
  show "Semantic.add (eval x s) (Semantic.sub (eval y s) (eval x s)) \<tturnstile> eval y s"
    by (cases "eval x s"; cases "eval y s"; simp add: Semantic.add.simps Semantic.sub.simps)
qed

subsubsection "Binary Right Constant Shift"
text "Binary right shift rewriting rule is a canonicalisation rule for shifting
all constant nodes to the right subnode of binary operations."
theorem binary_right_shift:
  assumes one_const: "y \<noteq> ConstNode val"
  assumes commutative: "commutative op"
  shows "BinaryNode op (ConstNode const) y \<turnstile> BinaryNode op y (ConstNode const)"
proof (cases op)
case AddOp
  then show ?thesis using add_commutative by simp
next
  case SubOp
  then show ?thesis
    using commutative by simp
next
  case MulOp
  then show ?thesis using mul_commutative by simp
next
  case DivOp
  then show ?thesis
    using commutative by simp
next
  case EqualOp
  then show ?thesis
    using commutative by simp
next
  case LessOp
  then show ?thesis
    using commutative by simp
next
  case AndOp
  then show ?thesis using and_commutative by simp
next
  case OrOp
  then show ?thesis using or_commutative by simp
next
  case XorOp
  then show ?thesis using xor_commutative by simp
qed

subsection "Unary Node Rewrites"


lemma abs_pos [simp]:
  assumes pos: "sint val \<ge> 0"
  shows "Semantic.abs (IntegerValue val) = IntegerValue val"
  using Semantic.abs.simps(1) [of val]
  by (simp add: less_le_not_le pos)

lemma abs_neg [simp]:
  assumes neg: "sint val < 0"
  shows "Semantic.abs (IntegerValue val) = IntegerValue (-val)"
  using Semantic.abs.simps(1) [of val]
  by (simp add: neg)

lemma abs_minint [simp]:
  shows "Semantic.abs (IntegerValue (-2147483648::int32)) = IntegerValue (-2147483648::int32)"
  using Semantic.abs.simps(1) [of "(-2147483648::int32)"]
  by simp

(*  Try to relate negative vs positive?
lemma neg32_distrib:
  fixes val :: int32
  assumes val: "val \<noteq> (-2147483648::int32)"
  assumes nonzero: "val \<noteq> 0"
  assumes "sint val < 0"
  shows "sint(-val) > 0"
  apply word-bitwise
*)

text_raw \<open>\DefineSnippet{rewrite:abs}{\<close>
lemma nested_abs:
  shows "Semantic.abs (Semantic.abs (IntegerValue val)) \<tturnstile> Semantic.abs (IntegerValue val)"
  using Semantic.abs.simps(1) [of val]
  (* apply (cases "sint val \<ge> 0" ; simp add: Semantic.abs.simps(1)) *)
  apply (cases "val = (-2147483648::int32)" ; simp add: Semantic.abs.simps(1))
  apply (cases "sint val < 0" ; simp)
proof
  assume "val \<noteq> - 2147483648"
  assume "sint val < 0"
  assume "sint (-val) < 0"
  have valneg: "val <s 0"
    by (simp add: \<open>sint val < 0\<close> word_sless_alt)
  have negvalneg: "- val <s 0"
    by (simp add: \<open>sint (- val) < 0\<close> word_sless_alt)
  show "2 * val = 0"
    sorry
qed
(*
  apply simp
  using Word.word_sless_alt[symmetric, where ?a="- val" and ?b=0]
  apply simp
  apply (simp only: word_sless_alt[of val 0] ])
  using Word.word_sless_alt [of "- val" 0]
*)
  

theorem rewrite_nested_abs:
  fixes e :: Node
  shows "(UnaryNode AbsOp (UnaryNode AbsOp e)) \<turnstile> (UnaryNode AbsOp e)"
  using nested_abs
  by (metis Semantic.abs.elims Semantic.abs.simps(2) eval.simps(13) expression_rewrites.simps refines.elims(3))
text_raw \<open>}%EndSnippet\<close>


lemma nested_minus:
  assumes "e = (IntegerValue val)"
  shows "Semantic.uminus (Semantic.uminus e) \<tturnstile> e"
  by (simp add: Semantic.uminus.simps(1) assms)

theorem rewrite_nested_minus:
  fixes e :: Node
  shows "(UnaryNode MinusOp (UnaryNode MinusOp e)) \<turnstile> e"
  using nested_minus
  by (metis Semantic.uminus.elims Value.distinct(1) Value.distinct(3) Value.distinct(5) eval.simps(11) expression_rewrites.simps refines.elims(3))

lemma nested_not:
  assumes "e = (BooleanValue val)"
  shows "Semantic.logicNot (Semantic.logicNot e) = e"
  by (simp add: Semantic.logicNot.simps(1) assms)

theorem rewrite_nested_not:
  fixes e :: Node
  shows "(UnaryNode NotOp (UnaryNode NotOp e)) \<turnstile> e"
  apply (simp add: nested_not)
  by (metis Semantic.logicNot.elims Semantic.logicNot.simps(2) nested_not refines.simps(1) reflexive_refinement)


subsection "Neutral Constants"
text \<open>Rewrite rules that deal with neutral constant in expressions.\<close>

theorem rewrite_neutral_add:
  fixes e :: Node
  shows "BinaryNode AddOp e (ConstNode (IntegerValue 0)) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "Semantic.add (eval e s) (IntegerValue 0) \<tturnstile> eval e s"
    by (cases "eval e s"; simp add: Semantic.add.simps)
qed

theorem rewrite_neutral_sub:
  fixes e :: Node
  shows "(BinaryNode SubOp e (ConstNode (IntegerValue 0))) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "Semantic.sub (eval e s) (IntegerValue 0) \<tturnstile> eval e s"
    by (cases "eval e s"; simp add: Semantic.sub.simps)
qed

theorem rewrite_neutral_mul:
  fixes e :: Node
  shows "(BinaryNode MulOp e (ConstNode (IntegerValue 1))) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "Semantic.mul (eval e s) (IntegerValue 1) \<tturnstile> eval e s"
    by (cases "eval e s"; simp add: Semantic.mul.simps)
qed

theorem rewrite_neutral_div:
  fixes e :: Node
  shows "(BinaryNode DivOp e (ConstNode (IntegerValue 1))) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "Semantic.divide (eval e s) (IntegerValue 1) \<tturnstile> eval e s"
    by (cases "eval e s"; simp add: Semantic.divide.simps)
qed

theorem rewrite_neutral_or:
  fixes e :: Node
  shows "(BinaryNode OrOp e (ConstNode (BooleanValue False))) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "Semantic.logicOr (eval e s) (BooleanValue False) \<tturnstile> eval e s"
    by (cases "eval e s"; simp add: Semantic.logicOr.simps)
qed

theorem rewrite_neutral_and:
  fixes e :: Node
  shows "(BinaryNode AndOp e (ConstNode (BooleanValue True))) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "Semantic.logicAnd (eval e s) (BooleanValue True) \<tturnstile> eval e s"
    by (cases "eval e s"; simp add: Semantic.logicAnd.simps)
qed

subsection "Constant Folding"
text "Constant folding is the elimination of expressions where all values are constant"

theorem rewrite_fold_add:
  fixes x y :: int32
  shows "(BinaryNode AddOp (ConstNode (IntegerValue x)) (ConstNode (IntegerValue y))) \<turnstile> ConstNode (IntegerValue (x + y))"
  using eval.simps
  by (simp add: Semantic.add.simps(1))

theorem rewrite_fold_sub:
  fixes x y :: int32
  shows "(BinaryNode SubOp (ConstNode (IntegerValue x)) (ConstNode (IntegerValue y))) \<turnstile> ConstNode (IntegerValue (x - y))"
  using eval.simps
  by (simp add: Semantic.sub.simps(1))

theorem rewrite_fold_mul:
  fixes x y :: int32
  shows "(BinaryNode MulOp (ConstNode (IntegerValue x)) (ConstNode (IntegerValue y))) \<turnstile> ConstNode (IntegerValue (x * y))"
  using eval.simps
  by (simp add: Semantic.mul.simps(1))

theorem rewrite_fold_div:
  fixes x y :: int32
  shows "(BinaryNode DivOp (ConstNode (IntegerValue x)) (ConstNode (IntegerValue y))) \<turnstile> ConstNode (IntegerValue (x div y))"
  using eval.simps
  by (simp add: Semantic.divide.simps(1))

theorem rewrite_fold_less:
  fixes x y :: int32
  shows "(BinaryNode LessOp (ConstNode (IntegerValue x)) (ConstNode (IntegerValue y))) \<turnstile> ConstNode (BooleanValue (sint x < sint y))"
  using eval.simps
  by (simp add: Semantic.less.simps(1))

theorem rewrite_fold_and:
  fixes x y :: bool
  shows "(BinaryNode AndOp (ConstNode (BooleanValue x)) (ConstNode (BooleanValue y))) \<turnstile> ConstNode (BooleanValue (x \<and> y))"
  using eval.simps
  by (simp add: Semantic.logicAnd.simps(1))

theorem rewrite_fold_or:
  fixes x y :: bool
  shows "(BinaryNode OrOp (ConstNode (BooleanValue x)) (ConstNode (BooleanValue y))) \<turnstile> ConstNode (BooleanValue (x \<or> y))"
  using eval.simps
  by (simp add: Semantic.logicOr.simps(1))

theorem rewrite_fold_xor:
  fixes x y :: bool
  shows "(BinaryNode XorOp (ConstNode (BooleanValue x)) (ConstNode (BooleanValue y))) \<turnstile> ConstNode (BooleanValue ((x \<and> y) \<or> (\<not>x \<and> \<not>y)))"
  using eval.simps
  by (simp add: Semantic.logicXor.simps(1))

end
