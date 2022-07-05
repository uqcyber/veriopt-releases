section \<open>Canonicalization Phase\<close>

theory Common
  imports 
    OptimizationDSL.Canonicalization
    Semantics.IRTreeEvalThms
begin

lemma size_pos[simp]: "0 < size y"
  apply (induction y; auto?)
  subgoal premises prems for op a b
    using prems by (induction op; auto)
  done

lemma size_non_add: "op \<noteq> BinAdd \<Longrightarrow> size (BinaryExpr op a b) = size a + size b"
  by (induction op; auto)

lemma size_non_const:
  "\<not> is_ConstantExpr y \<Longrightarrow> 1 < size y"
  using size_pos apply (induction y; auto)
  subgoal premises prems for op a b
    apply (cases "op = BinAdd")
    using size_non_add size_pos apply auto
    by (simp add: Suc_lessI one_is_add)+
  done

end