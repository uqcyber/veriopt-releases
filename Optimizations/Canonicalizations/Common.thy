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
  by (induction y; auto?)

lemma size_non_add[size_simps]: "size (BinaryExpr op a b) = size a + (size b) * 2"
  by (induction op; auto)

lemma size_non_const[size_simps]:
  "\<not> is_ConstantExpr y \<Longrightarrow> 1 < size y"
  using size_pos apply (induction y; auto)
  apply (metis Suc_lessI mult_eq_1_iff mult_pos_pos n_not_Suc_n numeral_2_eq_2 pos2)
  by (metis add_strict_increasing less_Suc0 linorder_not_less mult_2_right not_add_less2)

lemmas arith[size_simps] = Suc_leI add_strict_increasing

definition well_formed_equal :: "Value \<Rightarrow> Value \<Rightarrow> bool" 
  (infix "\<approx>" 50) where
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"

lemma well_formed_equal_defn [simp]:
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"
  unfolding well_formed_equal_def by simp

end