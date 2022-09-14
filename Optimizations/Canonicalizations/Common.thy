section \<open>Canonicalization Phase\<close>

theory Common
  imports 
    OptimizationDSL.Canonicalization
    Semantics.IRTreeEvalThms
begin


(* Old size function
fun size :: "IRExpr \<Rightarrow> nat" where
  (* "size (UnaryExpr op e) = (size e) + 1" | *) (* Old, new below. *)
  "size (UnaryExpr op e) = (size e) * 2" |
  "size (BinaryExpr op x y) = (size x) + ((size y) * 2)" |
 (* "size (BinaryExpr op x y) = (size x) + (size y)" |*)
  "size (ConditionalExpr cond t f) = (size cond) + (size t) + (size f) + 2" |
  "size (ConstantExpr c) = 1" |
  "size (ParameterExpr ind s) = 2" |
  "size (LeafExpr nid s) = 2" |
  "size (ConstantVar c) = 2" |
  "size (VariableExpr x s) = 2"
*)


lemma size_pos[size_simps]: "0 < size y"
  apply (induction y; auto?)
  subgoal premises prems for op a b
    using prems by (induction op; auto)
  done

lemma size_non_add[size_simps]: "op \<noteq> BinAdd \<Longrightarrow> size (BinaryExpr op a b) = size a + size b"
  by (induction op; auto)

lemma size_non_const[size_simps]:
  "\<not> is_ConstantExpr y \<Longrightarrow> 1 < size y"
  using size_pos apply (induction y; auto)
  subgoal premises prems for op a b
    apply (cases "op = BinAdd")
    using size_non_add size_pos apply auto
    by (simp add: Suc_lessI one_is_add)+
  done

lemmas arith[size_simps] = Suc_leI add_strict_increasing


definition well_formed_equal :: "Value \<Rightarrow> Value \<Rightarrow> bool" 
  (infix "\<approx>" 50) where
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"

lemma well_formed_equal_defn [simp]:
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"
  unfolding well_formed_equal_def by simp

end