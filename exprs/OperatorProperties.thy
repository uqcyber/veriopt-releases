section "Operator Properties"
text \<open>
Defines which operators are associative and commutative by the definition of the
associative and commutative functions.

Additionally, provides a proof for each of the commutative operators that the
corresponding semantic is commutative.
\<close>

theory OperatorProperties
  imports Semantics
begin

fun associative :: "BinaryOp \<Rightarrow> bool" where
  "associative AddOp = True" |
  "associative SubOp = True" |
  "associative MulOp = True" |
  "associative DivOp = True" |
  "associative EqualOp = False" |
  "associative LessOp = False" |
  "associative AndOp = True" |
  "associative OrOp = True" |
  "associative XorOp = True"

fun commutative :: "BinaryOp \<Rightarrow> bool" where
  "commutative AddOp = True" |
  "commutative SubOp = False" |
  "commutative MulOp = True" |
  "commutative DivOp = False" |
  "commutative EqualOp = False" |
  "commutative LessOp = False" |
  "commutative AndOp = True" |
  "commutative OrOp = True" |
  "commutative XorOp = True"

subsection "Commutative Proofs"
text \<open>Proofs that the semantics of each of the commutative operators are commutative.\<close>
lemma add_commutative:
  fixes x y :: Value
  shows "Semantic.add x y \<tturnstile> Semantic.add y x"
  by (cases x; cases y; simp add: Semantic.add.simps)

lemma mul_commutative:
  fixes x y :: Value
  shows "Semantic.mul x y \<tturnstile> Semantic.mul y x"
  by (cases x; cases y; simp add: Semantic.mul.simps)

lemma and_commutative:
  fixes x y :: Value
  shows "Semantic.logicAnd x y \<tturnstile> Semantic.logicAnd y x"
  by (cases x; cases y; simp add: Semantic.logicAnd.simps; auto)

lemma or_commutative:
  fixes x y :: Value
  shows "Semantic.logicOr x y \<tturnstile> Semantic.logicOr y x"
  by (cases x; cases y; simp add: Semantic.logicOr.simps; auto)

lemma xor_commutative:
  fixes x y :: Value
  shows "Semantic.logicXor x y \<tturnstile> Semantic.logicXor y x"
  by (cases x; cases y; simp add: Semantic.logicXor.simps; auto)

end