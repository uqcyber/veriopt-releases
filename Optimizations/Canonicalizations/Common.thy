section \<open>Canonicalization Optimizations\<close>

theory Common
  imports 
    OptimizationDSL.Canonicalization
    Semantics.IRTreeEvalThms
begin

lemma size_pos[size_simps]: "0 < size y"
  apply (induction y; auto?)
  subgoal for op
    apply (cases op) by (smt (z3) gr0I one_neq_zero pos2 size.elims trans_less_add2)+
  done

lemma size_non_add[size_simps]: "size (BinaryExpr op a b) = size a + size b + 2 \<longleftrightarrow> \<not>(is_ConstantExpr b)"
  by (induction b; induction op; auto simp: is_ConstantExpr_def)

lemma size_non_const[size_simps]:
  "\<not> is_ConstantExpr y \<Longrightarrow> 1 < size y"
  using size_pos apply (induction y; auto)
  by (metis Suc_lessI add_is_1 is_ConstantExpr_def le_less linorder_not_le n_not_Suc_n size_non_add
      numeral_2_eq_2 pos2 size.simps(2))

lemma size_binary_const[size_simps]:
  "size (BinaryExpr op a b) = size a + 2 \<longleftrightarrow> (is_ConstantExpr b)"
  by (induction b; auto simp: is_ConstantExpr_def size_pos)

lemma size_flip_binary[size_simps]:
  "\<not>(is_ConstantExpr y) \<longrightarrow> size (BinaryExpr op (ConstantExpr x) y) > size (BinaryExpr op y (ConstantExpr x))"
  by (metis add_Suc not_less_eq order_less_asym plus_1_eq_Suc size.simps(2,11) size_non_add)

lemma size_binary_lhs_a[size_simps]:
  "size (BinaryExpr op (BinaryExpr op' a b) c) > size a"
  by (metis add_lessD1 less_add_same_cancel1 pos2 size_binary_const size_non_add)

lemma size_binary_lhs_b[size_simps]:
  "size (BinaryExpr op (BinaryExpr op' a b) c) > size b"
  by (metis IRExpr.disc(42) One_nat_def add.left_commute add.right_neutral is_ConstantExpr_def
      less_add_Suc2 numeral_2_eq_2 plus_1_eq_Suc size.simps(11) size_binary_const size_non_add
      size_non_const trans_less_add1)

lemma size_binary_lhs_c[size_simps]:
  "size (BinaryExpr op (BinaryExpr op' a b) c) > size c"
  by (metis IRExpr.disc(42) add.left_commute add.right_neutral is_ConstantExpr_def less_Suc_eq
      numeral_2_eq_2 plus_1_eq_Suc size.simps(11) size_non_add size_non_const trans_less_add2)

lemma size_binary_rhs_a[size_simps]:
  "size (BinaryExpr op c (BinaryExpr op' a b)) > size a"
  apply auto
  by (metis trans_less_add2 less_Suc_eq less_add_same_cancel1 linorder_neqE_nat not_add_less1 pos2
      order_less_trans size_binary_const size_non_add)

lemma size_binary_rhs_b[size_simps]:
  "size (BinaryExpr op c (BinaryExpr op' a b)) > size b"
  by (metis add.left_commute add.right_neutral is_ConstantExpr_def lessI numeral_2_eq_2 size_non_add
      plus_1_eq_Suc size.simps(4,11) trans_less_add2)

lemma size_binary_rhs_c[size_simps]:
  "size (BinaryExpr op c (BinaryExpr op' a b)) > size c"
  by simp

lemma size_binary_lhs[size_simps]:
  "size (BinaryExpr op x y) > size x"
  by (metis One_nat_def Suc_eq_plus1 add_Suc_right less_add_Suc1 numeral_2_eq_2 size_binary_const
      size_non_add)

lemma size_binary_rhs[size_simps]:
  "size (BinaryExpr op x y) > size y"
  by (metis IRExpr.disc(42) add_strict_increasing is_ConstantExpr_def linorder_not_le not_add_less1
      size.simps(11) size_non_add size_non_const size_pos)

lemma size_eq_ops [size_simps]:
  "size (BinaryExpr BinIntegerEquals y z) < Suc (Suc (size (BinaryExpr op y x) + size (BinaryExpr op z x)))"
  by (cases x; cases y; cases z; auto)

lemma size_eq_const [size_simps]:
  "Suc (Suc (size x)) < size (BinaryExpr op' (BinaryExpr op x y) y)"
  by (cases x; cases y; auto)

lemmas arith[size_simps] = Suc_leI add_strict_increasing order_less_trans trans_less_add2

definition well_formed_equal :: "Value \<Rightarrow> Value \<Rightarrow> bool" 
  (infix "\<approx>" 50) where
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"

lemma well_formed_equal_defn [simp]:
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"
  unfolding well_formed_equal_def by simp

text \<open> Helpful lemmas for canonicalization proofs \<close>

(* General lemmas *)

(* take_bit lemmas *)
lemma takeBitNot:
  fixes xv :: "64word"
  assumes "xb \<ge> 1"
  shows "(take_bit xb (not xv) \<noteq> take_bit xb xv)"
  apply auto subgoal premises p
  proof -
    have addAllOnes: "take_bit xb (not xv) + take_bit xb xv = take_bit xb (-1)"
      by (smt (z3) take_bit_not_eq_mask_diff add_minus_cancel p take_bit_minus_one_eq_mask
          uminus_add_conv_diff)
    have orAllOnes:  "or (take_bit xb (not xv)) (take_bit xb xv) = take_bit xb (-1)"
      by (metis bit.disj_cancel_left take_bit_or)
    then show ?thesis
      using addAllOnes assms orAllOnes p by force
  qed
  done

lemma take_bit_size_eq:
  shows "take_bit 64 a = take_bit LENGTH(64) (a::64 word)"
  by auto

lemma take_bit64 [simp]:
  fixes w :: "int64"
  shows "take_bit 64 w = w"
proof -
  have "Nat.size w = 64"
    by (simp add: size64)
  then show ?thesis
    by (metis lt2p_lem mask_eq_iff take_bit_eq_mask verit_comp_simplify1(2) wsst_TYs(3))
qed

lemma mergeTakeBit:
  fixes a :: "nat"
  fixes b c :: "64 word"
  shows "take_bit a (take_bit a (b) * take_bit a (c)) = take_bit a (b * c)"
 by (smt (verit, ccfv_SIG) take_bit_mult take_bit_of_int unsigned_take_bit_eq word_mult_def)

(* Evaluation lemmas *)
lemma const_eval_is_const:
  assumes "wf_value n"
  shows "[m,p] \<turnstile> exp[const (n)] \<mapsto> n"
  by (simp add: assms IRTreeEval.evaltree.ConstantExpr)

(* Operator commutativity lemmas *)
lemma val_add_commutative:
  "val[x + y] = val[y + x]"
  by (cases x; cases y; auto simp: add.commute)

lemma val_and_commutative:
  "val[x & y] = val[y & x]"
  by (cases x; cases y; auto simp: and.commute)

lemma val_eq_commutative:
  "val[x eq y] = val[y eq x]"
  by (cases y; cases x; auto simp: unwrap_bool_to_val)

lemma val_or_commutative:
  "val[x | y] = val[y | x]"
  by (cases x; cases y; auto simp: or.commute)

lemma val_xor_commutative:
  "val[x \<oplus> y] = val[y \<oplus> x]"
  by (cases x; cases y; auto simp: word_bw_comms(3))

lemma exp_add_commutative:
  "exp[x + y] \<ge> exp[y + x]"
  by (auto simp: val_add_commutative)

lemma exp_and_commutative:
  "exp[x & y] \<ge> exp[y & x]"
  by (auto simp: val_and_commutative)

lemma exp_eq_commutative:
  "exp[x eq y] \<ge> exp[y eq x]"
  by (auto simp: val_eq_commutative)

lemma exp_or_commutative:
  "exp[x | y] \<ge> exp[y | x]"
  by (auto simp: val_or_commutative)

lemma exp_xor_commutative:
  "exp[x \<oplus> y] \<ge> exp[y \<oplus> x]"
  by (auto simp: val_xor_commutative)

(* Operator associativity lemmas *)
lemma val_and_associative:
  "val[(x & y) & z] = val[x & (y & z)]"
  by (cases x; cases y; cases z; auto simp: and.assoc)

lemma val_or_associative:
  "val[(x | y) | z] = val[x | (y | z)]"
  by (cases x; cases y; cases z; auto simp: or.assoc)

lemma val_xor_associative:
  "val[(x \<oplus> y) \<oplus> z] = val[x \<oplus> (y \<oplus> z)]"
  by (cases x; cases y; cases z; auto simp: xor.assoc)

lemma exp_and_associative:
  "exp[(x & y) & z] \<ge> exp[x & (y & z)]"
  using val_and_associative by fastforce

lemma exp_or_associative:
  "exp[(x | y) | z] \<ge> exp[x | (y | z)]"
  using val_or_associative by fastforce

lemma exp_xor_associative:
  "exp[(x \<oplus> y) \<oplus> z] \<ge> exp[x \<oplus> (y \<oplus> z)]"
  using val_xor_associative by fastforce

(* Operator self lemmas *)
lemma val_xor_self:
  assumes "x = IntVal b xv"
  shows "val[x \<oplus> x] = val[IntVal b 0]"
  using assms by (cases x; auto)

end