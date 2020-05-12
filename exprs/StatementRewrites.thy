section "Statement Rewriting"
text \<open>Statements that can be rewritten as other semantically equivalent statements.\<close>

theory StatementRewrites
  imports
    Semantics
    Traversal
begin 

text \<open>
A rewrite (\isasymturnstile) is true if one statement can be rewritten by
another statement with the original semantics preserved.
\<close>
fun statement_rewrites :: "ControlNode \<Rightarrow> ControlNode \<Rightarrow> bool" (infixl "\<turnstile>" 50) where
  "statement_rewrites a b = (\<forall> s :: State . ((exec a s) = (exec b s)))"

lemma statement_rewrites_def:
  fixes a b :: ControlNode
  shows "a \<turnstile> b \<equiv> (\<forall> s :: State . ((exec a s) = (exec b s)))"
  by simp

subsection "If Rewrites"
lemma negation:
  assumes "(eval x s) = (IntegerValue val)"
  shows "(Eval.bool (eval (UnaryNode NotOp x) s)) = (\<not>(Eval.bool (eval x s)))"
  by (simp add: Eval.bool.simps(1) Semantic.logicNot.simps(1) assms)

theorem rewrite_if_negated_condition:
  fixes trueBranch falseBranch :: ControlNode
  assumes nc: "\<forall> s :: State . (eval x s = IntegerValue val)"
  shows "(IfNode (UnaryNode NotOp x) trueBranch falseBranch)
          \<turnstile> (IfNode x falseBranch trueBranch)"
  using negation nc by auto

theorem rewrite_if_true_const:
  fixes trueBranch falseBranch :: ControlNode
  shows "(IfNode (ConstNode (IntegerValue 1)) trueBranch falseBranch)
    \<turnstile> trueBranch"
  by (simp add: Eval.bool.simps)

theorem rewrite_if_false_const:
  fixes trueBranch falseBranch :: ControlNode
  shows "(IfNode (ConstNode (IntegerValue 0)) trueBranch falseBranch)
    \<turnstile> falseBranch"
  by (simp add: Eval.bool.simps)

subsection "While Rewrites"
theorem rewrite_while_false_const:
  fixes body after :: ControlNode
  shows "(WhileNode (ConstNode (IntegerValue 0)) body after) \<turnstile> after"
  by (simp add: Eval.bool.simps(1))

subsection "Usage Rewrites"
text "Rewriting rules based on whether an expression is used again in any successor nodes"

lemma contains_recursive:
  fixes node subnode program :: ControlNode
  assumes "contains subnode program"
  assumes "\<not>(contains node program)"
  shows "\<not>(contains node subnode)"
  using assms contains.simps subnodes.simps apply auto
  sorry

lemma unmodified_state:
  fixes program :: ControlNode
  assumes "\<not>(contains (AssignNode ident e n) program) \<and> \<not>(contains (WriteNode expr next) program)"
  shows "\<forall> s :: State . (exec program s) = s"
  using contains_recursive exec.simps sorry

theorem rewrite_unused_if:
  fixes cond :: Node
  fixes body succ :: ControlNode
  assumes nc: "\<not>(contains (AssignNode ident expr next) body) \<and> \<not>(contains (WriteNode expr next) body)"
  shows "(WhileNode cond body succ) \<turnstile> succ"
  using unmodified_state nc exec.simps
  by (metis Value.distinct(6) contains.elims(2) equals0D eval.simps(1) subnodes.simps(1) subnodes.simps(4) update.elims)

end