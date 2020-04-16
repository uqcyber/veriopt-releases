section "Monotonicity"
text \<open>
A collection of definitions for monotonicity with respect to the refinement
operator.

Also includes proofs that the semantic functions used by the binary and unary
operators are monotonic with respect to refinement.
\<close>

theory Monotonic
  imports
    Semantics
begin

text \<open>Unary monotonicity relationship\<close>
definition
  monotonic :: "(Value \<Rightarrow> Value) \<Rightarrow> bool"
where
  "monotonic F \<equiv> (\<forall> a b . ((a \<tturnstile> b) \<longrightarrow> (F a \<tturnstile> F b)))"


text \<open>Binary monotonicity relationship\<close>
definition
  monotonic_left :: "(Value \<Rightarrow> Value \<Rightarrow> Value) \<Rightarrow> bool"
where
  "monotonic_left F \<equiv> (\<forall> a b c . ((a \<tturnstile> b) \<longrightarrow> (F a c \<tturnstile> F b c)))"
definition
  monotonic_right :: "(Value \<Rightarrow> Value \<Rightarrow> Value) \<Rightarrow> bool"
where
  "monotonic_right F \<equiv> (\<forall> a b c . ((a \<tturnstile> b) \<longrightarrow> (F c a \<tturnstile> F c b)))"
definition
  monotonic_both :: "(Value \<Rightarrow> Value \<Rightarrow> Value) \<Rightarrow> bool"
where
  "monotonic_both F \<equiv> (monotonic_left F) \<and> (monotonic_right F)"


subsection "Semantic Monotonicity"
text \<open>
The MonotonicFunctions locale defines a collection of theorems for each of the
semantics in the Semantic locale. The theories prove that each semantic definition
is monotonic for both unary and binary relations.

These theorems are used in the general theorems that the subnodes of binary
and unary operators can be refined.
\<close>
locale MonotonicFunctions
begin
subsubsection "Binary Monotonicity"
theorem add_monotonic:
  "monotonic_both Semantic.add" 
  unfolding monotonic_both_def apply safe
  using monotonic_left_def Semantic.add.simps apply simp
  apply (metis Value.distinct(1) Value.distinct(3) Value.distinct(5) refines.elims(3) refines_def)
  by (metis (mono_tags, lifting) Semantic.add.simps(5) Value.distinct(1) Value.distinct(3) Value.distinct(5) monotonic_right_def refines.elims(3) refines_def)

theorem minus_monotonic:
  "monotonic_both Semantic.sub"
  unfolding monotonic_both_def apply safe
  using monotonic_left_def Semantic.sub.simps apply simp
  apply (metis Value.distinct(1) Value.distinct(3) Value.distinct(5) refines.elims(3) refines_def)
  by (metis (mono_tags, lifting) Semantic.sub.simps(5) Value.distinct(1) Value.distinct(3) Value.distinct(5) monotonic_right_def refines.elims(3) refines_def)

theorem divide_monotonic:
  "monotonic_both Semantic.divide"
  unfolding monotonic_both_def apply safe
  using monotonic_left_def Semantic.divide.simps apply simp
  apply (metis Value.distinct(1) Value.distinct(3) Value.distinct(5) refines.elims(3) refines_def)
  by (metis (mono_tags, lifting) Semantic.divide.simps(5) Value.distinct(1) Value.distinct(3) Value.distinct(5) monotonic_right_def refines.elims(3) refines_def)


theorem times_monotonic:
  "monotonic_both Semantic.mul"
  unfolding monotonic_both_def apply safe
  using monotonic_left_def Semantic.mul.simps apply simp
  apply (metis Value.distinct(1) Value.distinct(3) Value.distinct(5) refines.elims(3) refines_def)
  by (metis (mono_tags, lifting) Semantic.mul.simps(5) Value.distinct(1) Value.distinct(3) Value.distinct(5) monotonic_right_def refines.elims(3) refines_def)


theorem equal_monotonic:
  "monotonic_left Semantic.equal \<and> monotonic_right Semantic.equal"
  using monotonic_left_def monotonic_right_def Semantic.equal.simps apply simp
  using refines.simps
  by (metis Semantic.equal.simps(3) refines.elims(2) refines.elims(3))

theorem less_monotonic:
  "monotonic_both Semantic.less"
  unfolding monotonic_both_def apply safe
  using monotonic_left_def Semantic.less.simps apply simp
  apply (metis Value.distinct(1) Value.distinct(3) Value.distinct(5) refines.elims(3) refines_def)
  by (metis (mono_tags, lifting) Semantic.less.simps(5) Value.distinct(1) Value.distinct(3) Value.distinct(5) monotonic_right_def refines.elims(3) refines_def)

theorem and_monotonic:
  "monotonic_both Semantic.logicAnd"
  unfolding monotonic_both_def apply safe
  using monotonic_left_def Semantic.logicAnd.simps apply simp
  apply (metis Value.distinct(1) Value.distinct(3) Value.distinct(5) refines.elims(3) refines_def)
  by (metis (mono_tags, lifting) Semantic.logicAnd.simps(5) Value.distinct(1) Value.distinct(3) Value.distinct(5) monotonic_right_def refines.elims(3) refines_def)

theorem or_monotonic:
  "monotonic_both Semantic.logicOr"
  unfolding monotonic_both_def apply safe
  using monotonic_left_def Semantic.logicOr.simps apply simp
   apply (metis Value.distinct(1) Value.distinct(3) Value.distinct(5) refines.elims(3) refines_def)
  by (metis (mono_tags, lifting) Semantic.logicOr.simps(5) Value.distinct(1) Value.distinct(3) Value.distinct(5) monotonic_right_def refines.elims(3) refines_def)

theorem xor_monotonic:
  "monotonic_both Semantic.logicXor"
  unfolding monotonic_both_def apply safe
  using monotonic_left_def Semantic.logicXor.simps apply simp
  apply (metis Value.distinct(1) Value.distinct(3) Value.distinct(5) refines.elims(3) refines_def)
  by (metis (mono_tags, lifting) Semantic.logicXor.simps(5) Value.distinct(1) Value.distinct(3) Value.distinct(5) monotonic_right_def refines.elims(3) refines_def)


subsubsection "Unary Monotonicity"
theorem abs_monotonic:
  "monotonic Semantic.abs"
  using monotonic_def Semantic.abs.simps apply simp
  using refines.simps
  using refines.elims(3) refines_def by fastforce

theorem uminus_monotonic:
  "monotonic Semantic.uminus"
  using monotonic_def Semantic.uminus.simps apply simp
  using refines.simps
  by (metis Semantic.uminus.elims)

theorem not_monotonic:
  "monotonic Semantic.logicNot"
  using monotonic_def Semantic.logicNot.simps apply simp
  using refines.simps
  by (metis Semantic.logicNot.elims)
end

end