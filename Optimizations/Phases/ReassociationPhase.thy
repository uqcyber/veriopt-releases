subsection \<open>Reassociation Phase\<close>
theory ReassociationPhase
  imports Canonicalizations.Common
begin

text \<open>The reassociation phase focuses re-ordering associative binary operations.
The purpose of this phase is to disassociate constants and invariant variables within a loop from variant variables.
This enables later phases to hoist more expressions outside of a loop.\<close>

phase ReassociationPhase
  terminating size
begin



subsubsection \<open>Rewrite Shifts to Multiplication\<close>

text \<open>Multiplication to powers of 2 are optimized to left shift operations in earlier phases.
As left shifts aren't associative this reduces the scope of this phase so the following undoes the optimization.\<close>

fun intval_power :: "nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_power b (IntVal32 v) = IntVal32 (word_of_nat (b^(unat v)))" |
  "intval_power b (IntVal64 v) = IntVal64 (word_of_nat (b^(unat v)))" |
  "intval_power _ _ = UndefVal"

lemma LeftShift32:
  fixes x y :: "32 word"
  shows "x << unat (and y 31) = x << unat y"
  sorry

lemma LeftShiftToMulVal:
  assumes "intval_mul x (intval_power 2 y) \<noteq> UndefVal"
  shows "intval_left_shift x y = intval_mul x (intval_power 2 y)"
  using assms apply (cases x; cases y; auto) sorry

optimization LeftShiftToMul:
  "x << (const c) \<longmapsto> x * (const (intval_power 2 c))"
  apply unfold_optimization apply simp sorry


end

end