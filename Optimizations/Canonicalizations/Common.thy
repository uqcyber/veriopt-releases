section \<open>Canonicalization Optimizations\<close>

theory Common
  imports
    OptimizationDSL.Canonicalization
    Semantics.IRTreeEvalThms
begin

subsection \<open> Size proofs \<close>

subsubsection \<open> $un_exp_size$ and $un_cycles$ proofs \<close>

lemma un_cycles_0: "un_cycles op = 0 \<longleftrightarrow> op \<in> un_empty_cycles"
  unfolding un_empty_cycles_def using un_cycles.simps by (cases op; auto)

lemma un_exp_size_geq_op: "un_exp_size ops op \<ge> ops"
  unfolding un_exp_size_def by simp

lemma un_exp_size_eq_empty: "op \<in> un_empty_cycles \<longleftrightarrow> un_exp_size ops op = ops"
  unfolding un_exp_size_def by (simp add: un_cycles_0)

lemma un_exp_size_gt: "op \<notin> un_empty_cycles \<longleftrightarrow> un_exp_size ops op > ops"
  unfolding un_exp_size_def using un_exp_size_def un_exp_size_eq_empty by auto

lemma size_un_eq_cycles_eq_iff:
  "(un_cycles op = un_cycles op') \<longleftrightarrow> size (UnaryExpr op x) = size (UnaryExpr op' x)"
  unfolding unary_size un_exp_size_def by simp

subsubsection \<open> $bin_exp_size$ and $bin_cycles$ proofs \<close>

lemma bin_cycles_0[size_simps]: "bin_cycles op = 0 \<longleftrightarrow> op \<in> bin_empty_cycles"
  unfolding bin_empty_cycles_def using bin_cycles.simps by (cases op; auto)

lemma bin_exp_size_geq_op[size_simps]: "bin_exp_size ops op \<ge> ops"
  unfolding bin_exp_size_def by simp

lemma bin_exp_size_eq_empty[size_simps]: "op \<in> bin_empty_cycles \<longleftrightarrow> bin_exp_size ops op = ops"
  unfolding bin_exp_size_def by (simp add: bin_cycles_0)

lemma bin_exp_size_gt[size_simps]: "op \<notin> bin_empty_cycles \<longleftrightarrow> bin_exp_size ops op > ops"
  unfolding bin_exp_size_def using bin_cycles_0 by force

lemma size_bin_rhs_const[size_simps]:
  "is_ConstantExpr y \<Longrightarrow> size (BinaryExpr op x y) = bin_exp_size ((size x) + 2) op"
  using is_ConstantExpr_def by force

lemma size_bin_rhs_nonconst[size_simps]:
  "\<not>is_ConstantExpr y \<Longrightarrow> size (BinaryExpr op x y) = bin_exp_size ((size x) + (size y) + 2) op"
  by (metis (full_types) IRExpr.disc(46) IRExpr.exhaust size.simps(3,4,5,6,7,8,9))

lemma size_bin_eq_cycles_eq_iff[size_simps]:
  "(bin_cycles op = bin_cycles op') \<longleftrightarrow> size (BinaryExpr op x y) = size (BinaryExpr op' x y)"
  apply (cases "is_ConstantExpr y")
  using size_bin_rhs_const size_bin_rhs_nonconst unfolding bin_exp_size_def by auto

subsubsection \<open> General size proofs \<close>

lemma size_pos[size_simps]: "0 < size y"
  apply (cases y; auto) unfolding un_exp_size_def cond_cycles_def apply simp_all
  subgoal premises p for op x y
    apply (cases "is_ConstantExpr y")
    using size_bin_rhs_const size_bin_rhs_nonconst unfolding bin_exp_size_def by auto
  done

lemma size_non_const[size_simps]: "\<not>is_ConstantExpr y \<Longrightarrow> Suc 0 < size y"
  apply (cases y; auto) prefer 3 using cond_cycles_def size_pos apply force
  apply (metis linorder_neqE_nat not_less_eq_eq size_pos un_exp_size_geq_op verit_comp_simplify1(3)
         less_one)
  by (smt (verit, ccfv_threshold) Suc_lessI bot_nat_0.extremum_strict add_is_1 size_bin_rhs_nonconst
      size_bin_rhs_const bin_exp_size_def size_pos add_Suc_right add_cancel_right_left gr0_conv_Suc
      pos2)

lemma size_const_lt[size_simps]: "\<not>is_ConstantExpr x \<Longrightarrow> size (ConstantExpr y) < size x"
  using size_non_const by auto

subsubsection \<open> Conditional size proofs \<close>

lemma size_cond_gt_1[size_simps]: "Suc 0 < size (ConditionalExpr cond t f)"
  unfolding cond_size cond_cycles_def by (simp add: size_pos)

lemma size_cond_gt_cond[size_simps]: "size c < size (ConditionalExpr c x y)"
  using cond_size [of c x y] unfolding cond_cycles_def by linarith

subsubsection \<open> Unary size proofs \<close>

lemma size_un_gt_1[size_simps]: "Suc 0 < size (UnaryExpr op y)"
  unfolding unary_size un_exp_size_def by (simp add: size_pos)

subsubsection \<open> Binary size proofs \<close>

lemma size_bin_diff[size_simps]: "bin_exp_size (size x + size y + 2) op \<noteq>
                                  bin_exp_size (size x + 2) op"
  unfolding bin_exp_size_def by (simp add: size_pos)

lemma size_bin_gt[size_simps]: "bin_exp_size (size x + size y + 2) op >
                                bin_exp_size (size x + 2) op"
  unfolding bin_exp_size_def
  by (metis add.commute linorder_neqE_nat nat_add_left_cancel_less not_add_less1 size_bin_diff)

lemma size_bin_iff[size_simps]:
  "size x < size y \<longleftrightarrow> size (BinaryExpr op x z) < size (BinaryExpr op y z)"
  apply (cases "is_ConstantExpr z")
  using size_bin_rhs_const size_bin_rhs_nonconst unfolding bin_exp_size_def by auto

lemma size_bin_eq_iff[size_simps]:
  "size x = size y \<longleftrightarrow> size (BinaryExpr bop x z) = size (BinaryExpr bop y z)"
  by (metis less_irrefl_nat linorder_neqE_nat size_bin_iff)

lemma size_bin_gt_1[size_simps]: "Suc 0 < size (BinaryExpr op x y)"
  using size_non_const by auto

lemma size_bin_const_iff[size_simps]:
  "size (BinaryExpr op a b) = bin_exp_size (size a + 2) op \<longleftrightarrow> is_ConstantExpr b"
  apply (cases "is_ConstantExpr b")
  using size_bin_rhs_const size_bin_rhs_nonconst bin_exp_size_def size_bin_gt by auto

lemma size_bin_nonconst_iff[size_simps]:
  "size (BinaryExpr op a b) = bin_exp_size (size a + size b + 2) op \<longleftrightarrow> \<not>is_ConstantExpr b"
  by (metis size_bin_diff size_bin_rhs_const size_bin_rhs_nonconst)

lemma size_bin_lhs[size_simps]: "size (BinaryExpr op x y) > size x"
  apply (cases "is_ConstantExpr y")
  using size_bin_rhs_const size_bin_rhs_nonconst unfolding bin_exp_size_def by auto

lemma size_bin_rhs[size_simps]: "size (BinaryExpr op x y) > size y"
  apply (cases "is_ConstantExpr y")
  using size_bin_rhs_const size_bin_rhs_nonconst is_ConstantExpr_def unfolding bin_exp_size_def
  by auto

lemma size_bin_lhs_succ[size_simps]: "size (BinaryExpr op x y) > Suc (size x)"
  apply (cases "is_ConstantExpr y")
  using size_bin_rhs_const size_bin_rhs_nonconst unfolding bin_exp_size_def by auto

lemma size_bin_rhs_succ[size_simps]: "size (BinaryExpr op x y) > Suc (size y)"
  apply (cases "is_ConstantExpr y")
  using size_bin_rhs_const size_bin_rhs_nonconst is_ConstantExpr_def size_pos
  unfolding bin_exp_size_def by auto

lemma size_bin_lhs_a[size_simps]: "size (BinaryExpr op (BinaryExpr op' a b) c) > size a"
  by (meson order_less_trans size_bin_lhs)

lemma size_bin_lhs_b[size_simps]: "size (BinaryExpr op (BinaryExpr op' a b) c) > size b"
  by (meson order_less_trans size_bin_lhs size_bin_rhs)

lemma size_bin_lhs_c[size_simps]: "size (BinaryExpr op (BinaryExpr op' a b) c) > size c"
  by (simp add: size_bin_rhs)

lemma size_bin_rhs_a[size_simps]: "size (BinaryExpr op c (BinaryExpr op' a b)) > size a"
  by (meson order_less_trans size_bin_lhs size_bin_rhs)

lemma size_bin_rhs_b[size_simps]: "size (BinaryExpr op c (BinaryExpr op' a b)) > size b"
  by (meson dual_order.strict_trans size_bin_rhs)

lemma size_bin_rhs_c[size_simps]: "size (BinaryExpr op c (BinaryExpr op' a b)) > size c"
  using size_bin_lhs by blast

lemma size_bin_lt_const_succ[size_simps]:
  "is_ConstantExpr y \<Longrightarrow> size (BinaryExpr op x y) < Suc (Suc (size (BinaryExpr op y x)))"
  apply (cases "is_ConstantExpr x")
  using size_bin_rhs_const size_bin_rhs_nonconst is_ConstantExpr_def
  unfolding bin_exp_size_def by force+

lemma size_bin_lt_nonconst_succ[size_simps]:
  "\<not>is_ConstantExpr y \<Longrightarrow> size (BinaryExpr op x y) < Suc (Suc (size (BinaryExpr op y x)))"
  apply (cases "is_ConstantExpr x")
  using size_bin_rhs_const size_bin_rhs_nonconst is_ConstantExpr_def bin_exp_size_def
  by (fastforce, simp)

lemma size_bin_lt_succ[size_simps]:
  "size (BinaryExpr op x y) < Suc (Suc (size (BinaryExpr op y x)))"
  using size_bin_lt_nonconst_succ size_bin_lt_const_succ by blast

lemma size_bin_cycle1_lt_succ_sum[size_simps]:
  "bin_cycles op \<le> 1 \<Longrightarrow> size (BinaryExpr op x y) < Suc (Suc (Suc (Suc (size x + size y))))"
  apply (cases "is_ConstantExpr y")
  using size_bin_rhs_const size_bin_rhs_nonconst unfolding bin_exp_size_def by (force, auto)

lemma size_bin_cycle1_lt_succ_bin_sum[size_simps]:
  "bin_cycles bop \<le> 1 \<Longrightarrow>
   size (BinaryExpr bop y z) < Suc (Suc (size (BinaryExpr op x y) + size (BinaryExpr op z x)))"
  apply (cases "is_ConstantExpr z")
  using size_bin_rhs_const [of z bop y] unfolding bin_exp_size_def apply auto
  apply (metis add_strict_mono le_Suc_eq le_zero_eq size_bin_gt_1 size_bin_rhs size_pos)
  using size_bin_rhs_nonconst [of z bop y] unfolding bin_exp_size_def apply auto
  by (metis Suc_eq_plus1 add.right_neutral add_strict_mono arith_is_1 not_gr_zero size_bin_lhs_succ
      size_bin_lhs size_bin_rhs add.assoc)

lemma size_bin_cycle1_lt_succ_bin_sum_lhs[size_simps]:
  "bin_cycles bop \<le> 1 \<Longrightarrow>
  size (BinaryExpr bop y z) < Suc (Suc (size (BinaryExpr op y x) + size (BinaryExpr op x z)))"
  apply (cases "is_ConstantExpr z")
  using size_bin_rhs_const [of z bop y] unfolding bin_exp_size_def apply auto
  apply (metis Suc_eq_plus1 add.right_neutral arith_is_1 not_gr_zero size_bin_lhs size_bin_lhs_succ
         trans_less_add1)
  using size_bin_rhs_nonconst unfolding bin_exp_size_def apply auto
  by (metis One_nat_def Suc_eq_plus1 add_mono_thms_linordered_field(3) size_bin_lhs trans_less_add1)

lemma size_bin_cycle_eq_lt_succ[size_simps]:
  "bin_cycles bop = bin_cycles bop' \<Longrightarrow>
   size (BinaryExpr bop z x) < Suc (Suc (Suc (size z + size (BinaryExpr bop' x y))))"
  apply (cases "is_ConstantExpr x")
  using size_bin_rhs_const size_bin_rhs_nonconst unfolding bin_exp_size_def apply auto
  apply (metis less_Suc_eq less_add_Suc2)
  by (smt (verit, del_insts) add.assoc less_Suc_eq less_add_Suc2 not_less_eq size_bin_lt_succ)

lemma size_bin_cycle_eq_lt_succ_rhs[size_simps]:
  "bin_cycles bop = bin_cycles bop' \<Longrightarrow>
   size (BinaryExpr bop z y) < Suc (Suc (Suc (size z + size (BinaryExpr bop' x y))))"
  apply (cases "is_ConstantExpr y")
  using size_bin_rhs_const size_bin_rhs_nonconst unfolding bin_exp_size_def by auto

lemma size_bin_cycle_eq_lt_bin_un[size_simps]:
  "bin_cycles bop = bin_cycles bop' \<Longrightarrow> un_cycles uop = 2 \<Longrightarrow>
   size (BinaryExpr bop y e) < size (BinaryExpr bop' (UnaryExpr uop e) y)"
  apply (cases "is_ConstantExpr y")
  using size_bin_rhs_const unfolding bin_exp_size_def apply auto[1] unfolding un_exp_size_def
  apply (metis add_2_eq_Suc' add_Suc less_Suc_eq size_bin_lt_succ)
  using size_bin_rhs_nonconst unfolding bin_exp_size_def apply auto unfolding un_exp_size_def
  by (metis add.assoc add_2_eq_Suc' add_Suc_shift less_Suc_eq size_bin_lt_succ)

lemma size_bin_cycle_eq_lt_sum_succ[size_simps]:
  "bin_cycles op = bin_cycles op' \<Longrightarrow>
   size (BinaryExpr op' y z) < Suc (Suc (Suc (size (BinaryExpr op x y) + size (BinaryExpr op x z))))"
  apply (cases "is_ConstantExpr z")
  using size_bin_rhs_const size_bin_rhs_nonconst unfolding bin_exp_size_def
  by (simp add: add.commute size_bin_rhs trans_less_add2)+

lemma size_bin_cycle_eq_lt_sum_succ_commute[size_simps]:
  "bin_cycles op = bin_cycles op' \<Longrightarrow>
   size (BinaryExpr op' y z) < Suc (Suc (Suc (size (BinaryExpr op y x) + size (BinaryExpr op z x))))"
  apply (cases "is_ConstantExpr z") using size_bin_rhs_const unfolding bin_exp_size_def
  by (metis (no_types, lifting) Suc_lessD less_trans_Suc size_bin_cycle_eq_lt_succ size_bin_iff
      size_bin_lhs)+

lemmas arith[size_simps] = Suc_leI add_strict_increasing order_less_trans trans_less_add2

subsection \<open> Helpful lemmas for canonicalization proofs \<close>

definition well_formed_equal :: "Value \<Rightarrow> Value \<Rightarrow> bool"
  (infix "\<approx>" 50) where
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"

lemma well_formed_equal_defn [simp]: "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"
  unfolding well_formed_equal_def by simp

subsubsection \<open> Operator commutativity lemmas \<close>

lemma val_add_commutative: "val[x + y] = val[y + x]"
  by (cases x; cases y; auto simp: add.commute)

lemma val_and_commutative: "val[x & y] = val[y & x]"
  by (cases x; cases y; auto simp: and.commute)

lemma val_eq_commutative: "val[x eq y] = val[y eq x]"
  by (cases y; cases x; auto simp: bool_to_val_unwrap)

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

lemma val_below_self: "x = IntVal b xv \<Longrightarrow> val[x |<| x] = val[false]"
  by simp

lemma val_eq_self: "x = IntVal b xv \<Longrightarrow> val[x eq x] = val[true]"
  by simp

lemma val_xor_self: "x = IntVal b xv \<Longrightarrow> val[x \<oplus> x] = val[IntVal b 0]"
  by simp

end