section \<open>Canonicalization Optimizations\<close>

theory Common
  imports
    OptimizationDSL.Canonicalization
    Semantics.IRTreeEvalThms
begin

lemma size_un_ops[size_simps]: "un_op_size ops op = ops"
  by simp

lemma size_bin_ops_div[size_simps]: "(bin_op_size ops op = ops) \<longleftrightarrow> (op \<noteq> BinDiv)"
  by (induction op; auto)

lemma size_un: "size (UnaryExpr op x) = un_op_size ((size x) + 2) op"
  by simp

lemma size_binary_lhs[size_simps]: "size (BinaryExpr op x y) > size x"
  by (cases x; cases y; cases op; auto)

lemma size_binary_rhs[size_simps]: "size (BinaryExpr op x y) > size y"
  by (cases x; cases y; cases op; auto)

lemma size_binary_lhs_succ[size_simps]: "size (BinaryExpr op x y) > Suc (size x)"
  by (cases x; cases y; cases op; auto)

lemma size_binary_rhs_succ[size_simps]: "size (BinaryExpr op x y) > Suc (size y)"
  apply (cases x; cases y; cases op; auto)
  by (metis less_nat_zero_code size_binary_lhs gr0I zero_less_iff_neq_zero less_zeroE)+

lemma size_pos[size_simps]: "0 < size y"
  apply (induction y; auto?)
  subgoal for op
    apply (cases op) by (metis size_binary_lhs bot_nat_0.not_eq_extremum less_nat_zero_code)+
  done

lemma size_non_add[size_simps]: "size (BinaryExpr op a b) = bin_op_size (size a + size b + 2) op \<longleftrightarrow>
                                 \<not>is_ConstantExpr b"
  by (induction b; induction op; auto simp: is_ConstantExpr_def)

lemma size_bin_rhs_const[size_simps]:
  "is_ConstantExpr y \<Longrightarrow> size (BinaryExpr op x y) = bin_op_size ((size x) + 2) op"
  using is_ConstantExpr_def by force

lemma size_bin_rhs_nonconst[size_simps]:
  "\<not>is_ConstantExpr y \<Longrightarrow> size (BinaryExpr op x y) = bin_op_size ((size x) + (size y) + 2) op"
  using size_non_add by auto

lemma size_bin_lt_sum_div[size_simps]:
  "op \<noteq> BinDiv \<Longrightarrow> size (BinaryExpr op x y) < Suc (Suc (Suc (size x + size y)))"
  using size_bin_rhs_nonconst apply (cases "is_ConstantExpr y")
  apply (metis add_2_eq_Suc' not_add_less1 not_less_eq size_bin_ops_div size_bin_rhs_const)
  by (simp add: less_Suc_eq size_bin_ops_div)

lemma size_un_gt_1[size_simps]: "1 < size (UnaryExpr op y)"
  by (induction y; auto?)

lemma size_bin_gt_1[size_simps]: "1 < size (BinaryExpr op x y)"
  by (metis add_diff_inverse_nat less_one size_binary_lhs size_pos trans_less_add1 zero_less_diff)

lemma size_cond_gt_1[size_simps]: "1 < size (ConditionalExpr cond t f)"
  by (cases t; cases f; auto)

lemma size_non_const[size_simps]: "\<not>is_ConstantExpr y \<Longrightarrow> 1 < size y"
  using size_pos apply (induction y; auto) by (metis Suc_lessI not_less_eq size_binary_rhs)

lemma size_binary_const[size_simps]:
  "size (BinaryExpr op a b) = bin_op_size (size a + 2) op \<longleftrightarrow> is_ConstantExpr b"
  by (metis (no_types, lifting) add_diff_cancel_right' add_eq_self_zero not_one_less_zero div_size
      size_bin_ops_div size_bin_rhs_nonconst size_non_const add_right_cancel size_bin_rhs_const)

lemma size_lt_implies_bin_lt[size_simps]:
  "size x < size y \<longleftrightarrow> size (BinaryExpr bop x z) < size (BinaryExpr bop y z)"
  apply (cases "is_ConstantExpr z")
  apply (metis size_bin_rhs_const div_size add_2_eq_Suc' add_less_cancel_right size_bin_ops_div
         add_less_mono1)
  by (metis div_size size_bin_ops_div size_bin_rhs_nonconst add_less_cancel_right)

lemma size_gt_implies_bin_gt[size_simps]:
  "size x > size y \<longleftrightarrow> size (BinaryExpr bop x z) > size (BinaryExpr bop y z)"
  by (simp add: size_lt_implies_bin_lt)

lemma size_eq_implies_bin_eq[size_simps]:
  "size x = size y \<longleftrightarrow> size (BinaryExpr bop x z) = size (BinaryExpr bop y z)"
  by (metis less_irrefl_nat linorder_neqE_nat size_gt_implies_bin_gt)

lemma size_flip_binary[size_simps]:
  "\<not>is_ConstantExpr y \<longrightarrow>
   size (BinaryExpr op (ConstantExpr x) y) > size (BinaryExpr op y (ConstantExpr x))"
  by (cases x; cases y; cases op; auto)

lemma size_bin_rhs_const_lt[size_simps]:
  "\<not>is_ConstantExpr x \<and> is_ConstantExpr y \<Longrightarrow> size (BinaryExpr op x y) < size (BinaryExpr op y x)"
  by (metis IRExpr.collapse(6) size_flip_binary)

lemma size_binary_lhs_a[size_simps]: "size (BinaryExpr op (BinaryExpr op' a b) c) > size a"
  by (meson order_less_trans size_binary_lhs)

lemma size_binary_lhs_b[size_simps]: "size (BinaryExpr op (BinaryExpr op' a b) c) > size b"
  by (meson order_less_trans size_binary_lhs size_binary_rhs)

lemma size_binary_lhs_c[size_simps]: "size (BinaryExpr op (BinaryExpr op' a b) c) > size c"
  by (simp add: size_binary_rhs)

lemma size_binary_rhs_a[size_simps]: "size (BinaryExpr op c (BinaryExpr op' a b)) > size a"
  by (meson order_less_trans size_binary_lhs size_binary_rhs)

lemma size_binary_rhs_b[size_simps]: "size (BinaryExpr op c (BinaryExpr op' a b)) > size b"
  by (meson dual_order.strict_trans size_binary_rhs)

lemma size_binary_rhs_c[size_simps]: "size (BinaryExpr op c (BinaryExpr op' a b)) > size c"
  using size_binary_lhs by blast

lemma size_bin_lt_succ_bin[size_simps]:
  "size (BinaryExpr BinIntegerEquals y z) <
   Suc (Suc (size (BinaryExpr op y x) + size (BinaryExpr op z x)))"
  using size_non_add size_binary_const apply (cases "is_ConstantExpr z")
  apply (metis add_2_eq_Suc' bin_op_size.simps(13) size_binary_lhs_succ less_Suc_eq not_less_eq
         add_lessD1)
  by (smt (verit, del_insts) size_binary_lhs add_2_eq_Suc' add_less_mono bin_op_size.simps(13)
      add_2_eq_Suc nat_add_left_cancel_less)

lemma size_succ_lt_bin[size_simps]:
  "Suc (Suc (size x)) < size (BinaryExpr op' (BinaryExpr op x y) y)"
  using size_non_add size_binary_const apply (cases "is_ConstantExpr y")
  apply (metis less_trans_Suc size_binary_lhs size_binary_lhs_succ)
  by (meson less_trans_Suc size_binary_lhs size_binary_lhs_succ)

lemma size_bineq_lt_succ[size_simps]:
  "op \<noteq> BinDiv \<Longrightarrow> size (BinaryExpr BinIntegerEquals y z) <
                   Suc (Suc (size (BinaryExpr op x y) + size (BinaryExpr op x z)))"
  by (smt (verit, ccfv_threshold) size_non_add size_bin_rhs_nonconst size_binary_const less_add_Suc1
      size_bin_ops_div size_binary_rhs add_2_eq_Suc' add_strict_mono bin_op_size.simps(13) lessI
      less_trans_Suc)

lemma size_bineq_lt_succ_commute_rhs[size_simps]:
  "op \<noteq> BinDiv \<Longrightarrow> size (BinaryExpr BinIntegerEquals y z) <
                   Suc (Suc (size (BinaryExpr op x y) + size (BinaryExpr op z x)))"
  by (smt (z3) size_non_add size_binary_const less_add_Suc1 size_bin_ops_div size_binary_rhs lessI
      add_2_eq_Suc' add_strict_mono bin_op_size.simps(13) less_trans_Suc add.assoc less_SucI)

lemma size_bineq_lt_succ_commute_lhs[size_simps]:
  "op \<noteq> BinDiv \<Longrightarrow> size (BinaryExpr BinIntegerEquals y z) <
                   Suc (Suc (size (BinaryExpr op y x) + size (BinaryExpr op x z)))"
  by (smt (verit) size_non_add size_bin_rhs_nonconst size_binary_const less_add_Suc1 size_binary_rhs
      size_bin_ops_div add_2_eq_Suc' add_strict_mono bin_op_size.simps(13) lessI plus_1_eq_Suc
      add.assoc One_nat_def Suc_eq_plus1 add.left_commute size_binary_lhs_succ less_SucI)

lemma size_bin_lt_bin_un[size_simps]:
  "bop \<noteq> BinDiv \<Longrightarrow> size (BinaryExpr bop x y) < size (BinaryExpr bop' (UnaryExpr uop y) x)"
  apply (cases "is_ConstantExpr x")
  apply (smt (verit, ccfv_threshold) div_size Suc_1 ab_semigroup_add_class.add_ac(1) add.commute
         lessI add_Suc_right size_bin_ops_div size_bin_rhs_nonconst un_op_size.simps const_size
         IRExpr.collapse(6) size_binary_const trans_less_add1 size_un)
  by (smt (verit, del_insts) div_size Suc_1 ab_semigroup_add_class.add_ac(1) add.commute size_un
      add_Suc_right size_bin_ops_div size_bin_rhs_nonconst un_op_size.simps size_binary_const lessI
      trans_less_add1)

lemma size_bin_eq_div:
  "(op = BinDiv) \<longleftrightarrow> (op' = BinDiv) \<Longrightarrow> size (BinaryExpr op x y) = size (BinaryExpr op' x y)"
  by (metis size_bin_ops_div size_bin_rhs_const size_bin_rhs_nonconst)

lemma size_bin_lt_commute[size_simps]:
  "size (BinaryExpr op x y) < Suc (Suc (size (BinaryExpr op y x)))"
  by (cases x; cases y; cases op; auto)

lemmas arith[size_simps] = Suc_leI add_strict_increasing order_less_trans trans_less_add2

definition well_formed_equal :: "Value \<Rightarrow> Value \<Rightarrow> bool"
  (infix "\<approx>" 50) where
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"

lemma well_formed_equal_defn [simp]: "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"
  unfolding well_formed_equal_def by simp

subsection \<open> Helpful lemmas for canonicalization proofs \<close>

subsubsection \<open> Operator commutativity lemmas \<close>

lemma val_add_commutative: "val[x + y] = val[y + x]"
  by (cases x; cases y; auto simp: add.commute)

lemma val_and_commutative: "val[x & y] = val[y & x]"
  by (cases x; cases y; auto simp: and.commute)

lemma val_eq_commutative: "val[x eq y] = val[y eq x]"
  by (cases y; cases x; auto simp: unwrap_bool_to_val)

lemma val_mul_commutative: "val[x * y] = val[y * x]"
  by (cases x; cases y; auto simp: mult.commute)

lemma val_or_commutative: "val[x | y] = val[y | x]"
  by (cases x; cases y; auto simp: or.commute)

lemma val_xor_commutative: "val[x \<oplus> y] = val[y \<oplus> x]"
  by (cases x; cases y; auto simp: word_bw_comms(3))

lemma exp_add_commutative: "exp[x + y] \<ge> exp[y + x]"
  by (auto simp: val_add_commutative)

lemma exp_and_commutative: "exp[x & y] \<ge> exp[y & x]"
  by (auto simp: val_and_commutative)

lemma exp_eq_commutative: "exp[x eq y] \<ge> exp[y eq x]"
  by (auto simp: val_eq_commutative)

lemma exp_mul_commutative: "exp[x * y] \<ge> exp[y * x]"
  by (auto simp: val_mul_commutative)

lemma exp_or_commutative: "exp[x | y] \<ge> exp[y | x]"
  by (auto simp: val_or_commutative)

lemma exp_xor_commutative: "exp[x \<oplus> y] \<ge> exp[y \<oplus> x]"
  by (auto simp: val_xor_commutative)

subsubsection \<open> Operator associativity lemmas \<close>

lemma val_add_associative: "val[(x + y) + z] = val[x + (y + z)]"
  by (cases x; cases y; cases z; auto simp: ab_semigroup_add_class.add_ac(1))

lemma val_and_associative: "val[(x & y) & z] = val[x & (y & z)]"
  by (cases x; cases y; cases z; auto simp: and.assoc)

lemma val_mul_associative: "val[(x * y) * z] = val[x * (y * z)]"
  apply (cases x; cases y; cases z; auto)
  by (metis (no_types, lifting) mergeTakeBit mult.assoc new_int.elims new_int_take_bits)

lemma val_or_associative: "val[(x | y) | z] = val[x | (y | z)]"
  by (cases x; cases y; cases z; auto simp: or.assoc)

lemma val_xor_associative: "val[(x \<oplus> y) \<oplus> z] = val[x \<oplus> (y \<oplus> z)]"
  by (cases x; cases y; cases z; auto simp: xor.assoc)

lemma exp_add_associative: "exp[(x + y) + z] \<ge> exp[x + (y + z)]"
  using val_add_associative by fastforce

lemma exp_and_associative: "exp[(x & y) & z] \<ge> exp[x & (y & z)]"
  using val_and_associative by fastforce

lemma exp_mul_associative: "exp[(x * y) * z] \<ge> exp[x * (y * z)]"
  using val_mul_associative by fastforce

lemma exp_or_associative: "exp[(x | y) | z] \<ge> exp[x | (y | z)]"
  using val_or_associative by fastforce

lemma exp_xor_associative: "exp[(x \<oplus> y) \<oplus> z] \<ge> exp[x \<oplus> (y \<oplus> z)]"
  using val_xor_associative by fastforce

subsubsection \<open> Operator self lemmas \<close>

lemma val_xor_self: "x = IntVal b xv \<Longrightarrow> val[x \<oplus> x] = val[IntVal b 0]"
  by simp

end