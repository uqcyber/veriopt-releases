section \<open>Canonicalization Optimizations\<close>

theory Common
  imports
    OptimizationDSL.Canonicalization
    Semantics.IRTreeEvalThms
begin

lemma size_un_ops[size_simps]:
  "un_op_size ops op = ops"
  by simp

lemma size_bin_ops_div[size_simps]:
  "(bin_op_size ops op = ops) \<longleftrightarrow> (op \<noteq> BinDiv)"
  by (induction op; auto)

lemma size_binary_lhs[size_simps]:
  "size (BinaryExpr op x y) > size x"
  by (cases x; cases y; cases op; auto)

lemma size_binary_rhs[size_simps]:
  "size (BinaryExpr op x y) > size y"
  by (cases x; cases y; cases op; auto)

lemma size_pos[size_simps]: "0 < size y"
  apply (induction y; auto?)
  subgoal for op
    apply (cases op) by (metis size_binary_lhs bot_nat_0.not_eq_extremum less_nat_zero_code)+
  done

lemma size_non_add[size_simps]: "size (BinaryExpr op a b) = bin_op_size (size a + size b + 2) op \<longleftrightarrow>
                                 \<not>(is_ConstantExpr b)"
  by (induction b; induction op; auto simp: is_ConstantExpr_def)

lemma size_bin_rhs_const[size_simps]:
  "is_ConstantExpr y \<Longrightarrow> size (BinaryExpr op x y) = (bin_op_size ((size x) + 2) op)"
  using is_ConstantExpr_def by force

lemma size_bin_rhs_nonconst[size_simps]:
  "\<not>(is_ConstantExpr) y \<Longrightarrow> size (BinaryExpr op x y) = (bin_op_size ((size x) + (size y) + 2) op)"
  using size_non_add by auto

lemma size_non_const[size_simps]:
  "\<not> is_ConstantExpr y \<Longrightarrow> 1 < size y"
  using size_pos apply (induction y; auto) by (metis Suc_lessI not_less_eq size_binary_rhs)

lemma size_binary_const[size_simps]:
  "size (BinaryExpr op a b) = bin_op_size (size a + 2) op \<longleftrightarrow> (is_ConstantExpr b)"
proof -
  have const: "is_ConstantExpr b \<Longrightarrow> size (BinaryExpr op a b) = bin_op_size (size a + 2) op"
    by (simp add: size_bin_rhs_const)
  have "\<not>(is_ConstantExpr b) \<Longrightarrow> \<not>(size (BinaryExpr op a b) = bin_op_size (size a + 2) op)"
    apply (cases "op = BinDiv") apply (induction b; auto) using size_pos apply auto
    apply (induction b; auto) defer
    apply (metis bin_const_size div_size IRExpr.collapse(6) Suc_inject add_eq_self_zero size_non_add
           size_bin_ops_div zero_eq_add_iff_both_eq_0 zero_neq_numeral)
    by (metis size_bin_ops_div add_2_eq_Suc' add_eq_self_zero zero_neq_numeral add_diff_cancel_left'
        diff_add_zero plus_1_eq_Suc)+
  then show ?thesis
    using const by auto
qed

lemma size_flip_binary[size_simps]:
  "\<not>(is_ConstantExpr y) \<longrightarrow>
   size (BinaryExpr op (ConstantExpr x) y) > size (BinaryExpr op y (ConstantExpr x))"
  by (cases x; cases y; cases op; auto)

lemma size_bin_rhs_const_lt[size_simps]:
  assumes "\<not>is_ConstantExpr x"
  assumes "is_ConstantExpr y"
  shows "size (BinaryExpr op x y) < size (BinaryExpr op y x)"
  by (metis IRExpr.collapse(6) assms size_flip_binary)

lemma size_binary_lhs_a[size_simps]:
  "size (BinaryExpr op (BinaryExpr op' a b) c) > size a"
  by (meson order_less_trans size_binary_lhs)

lemma size_binary_lhs_b[size_simps]:
  "size (BinaryExpr op (BinaryExpr op' a b) c) > size b"
  by (meson order_less_trans size_binary_lhs size_binary_rhs)

lemma size_binary_lhs_c[size_simps]:
  "size (BinaryExpr op (BinaryExpr op' a b) c) > size c"
  by (simp add: size_binary_rhs)

lemma size_binary_rhs_a[size_simps]:
  "size (BinaryExpr op c (BinaryExpr op' a b)) > size a"
  by (meson order_less_trans size_binary_lhs size_binary_rhs)

lemma size_binary_rhs_b[size_simps]:
  "size (BinaryExpr op c (BinaryExpr op' a b)) > size b"
  by (meson dual_order.strict_trans size_binary_rhs)

lemma size_binary_rhs_c[size_simps]:
  "size (BinaryExpr op c (BinaryExpr op' a b)) > size c"
  using size_binary_lhs by blast

lemma size_eq_ops[size_simps]:
  "size (BinaryExpr BinIntegerEquals y z) <
   Suc (Suc (size (BinaryExpr op y x) + size (BinaryExpr op z x)))"
proof -
  have sizelhs_const: "is_ConstantExpr z \<Longrightarrow>
       size (BinaryExpr BinIntegerEquals y z) = (bin_op_size ((size y) + 2) BinIntegerEquals)"
    using size_binary_const by presburger
  have sizelhs_nonconst: "\<not>(is_ConstantExpr z) \<Longrightarrow>
       size (BinaryExpr BinIntegerEquals y z) =
      (bin_op_size ((size y) + (size z) + 2) BinIntegerEquals)"
    using size_non_add by blast
  then show ?thesis
    apply (cases "is_ConstantExpr z")
    by (simp add: size_binary_lhs sizelhs_const trans_less_add1 add_strict_mono sizelhs_nonconst)+
qed

lemma size_eq_const[size_simps]:
  "Suc (Suc (size x)) < size (BinaryExpr op' (BinaryExpr op x y) y)"
proof -
  have sizerhs_const: "is_ConstantExpr y \<Longrightarrow>
       size (BinaryExpr op x y) = (bin_op_size ((size x) + 2) op)"
    using size_binary_const by auto
  have sizerhs_nonconst: "\<not>(is_ConstantExpr) y \<Longrightarrow>
       size (BinaryExpr op x y) = (bin_op_size ((size x) + (size y) + 2) op)"
    using size_non_add by auto
  show ?thesis
    apply (cases "is_ConstantExpr y")
    apply (metis sizerhs_const div_size add_2_eq_Suc' add_lessD1 size_bin_ops_div size_binary_lhs)
    by (smt (z3) sizerhs_nonconst div_size less_2_cases_iff less_add_same_cancel1 less_trans_Suc
        size_bin_ops_div size_binary_lhs size_pos trans_less_add1)
qed

lemma size_binop_equality[size_simps]:
  assumes "op \<noteq> BinDiv"
  shows "size (BinaryExpr BinIntegerEquals y z) <
         Suc (Suc (size (BinaryExpr op x y) + size (BinaryExpr op x z)))"
proof -
  have sizerhslhs_const: "is_ConstantExpr y \<Longrightarrow>
       size (BinaryExpr op x y) = (bin_op_size ((size x) + 2) op)"
    using size_binary_const by auto
  have sizerhslhs_nonconst: "\<not>(is_ConstantExpr) y \<Longrightarrow>
       size (BinaryExpr op x y) = (bin_op_size ((size x) + (size y) + 2) op)"
    using size_non_add by auto
  have sizelhs_const: "is_ConstantExpr z \<Longrightarrow>
       size (BinaryExpr BinIntegerEquals y z) = (bin_op_size ((size y) + 2) BinIntegerEquals)"
    by (meson size_binary_const)
  have sizelhs_nonconst: "\<not>(is_ConstantExpr) z \<Longrightarrow>
       size (BinaryExpr BinIntegerEquals y z) =
      (bin_op_size ((size y) + (size z) + 2) BinIntegerEquals)"
    using size_non_add by blast
  show ?thesis
    using assms apply (cases "is_ConstantExpr y") apply (cases "is_ConstantExpr z") prefer 3
    apply (cases "is_ConstantExpr z")
    apply (metis add_mono_thms_linordered_field(1) bin_op_size.simps(13) less_SucI trans_less_add1
           less_add_same_cancel2 size_bin_ops_div size_pos sizelhs_const sizerhslhs_nonconst)
    apply (smt (z3) Suc_1 add.assoc add.commute add_Suc_shift assms bin_op_size.simps(13) less_SucI
           nat_add_left_cancel_less plus_1_eq_Suc size_bin_ops_div size_binary_rhs sizelhs_nonconst
           sizerhslhs_nonconst trans_less_add2)
    apply (smt (verit, del_insts) const_size IRExpr.collapse(6) bin_op_size.simps(13) not_less_eq
           plus_1_eq_Suc size_bin_ops_div size_binary_const trans_less_add2)
    by (simp add: add_strict_mono size_binary_rhs sizelhs_nonconst)
qed

lemma size_binop_equality_commute_rhs[size_simps]:
  assumes "op \<noteq> BinDiv"
  shows "size (BinaryExpr BinIntegerEquals y z) <
         Suc (Suc (size (BinaryExpr op x y) + size (BinaryExpr op z x)))"
proof -
  have sizerhslhs_const: "is_ConstantExpr y \<Longrightarrow>
       size (BinaryExpr op x y) = (bin_op_size ((size x) + 2) op)"
    using size_binary_const by auto
  have sizerhslhs_nonconst: "\<not>(is_ConstantExpr) y \<Longrightarrow>
       size (BinaryExpr op x y) = (bin_op_size ((size x) + (size y) + 2) op)"
    using size_non_add by auto
  have sizelhs_const: "is_ConstantExpr z \<Longrightarrow>
       size (BinaryExpr BinIntegerEquals y z) = (bin_op_size ((size y) + 2) BinIntegerEquals)"
    by (meson size_binary_const)
  have sizelhs_nonconst: "\<not>(is_ConstantExpr) z \<Longrightarrow>
       size (BinaryExpr BinIntegerEquals y z) =
      (bin_op_size ((size y) + (size z) + 2) BinIntegerEquals)"
    using size_non_add by blast
  show ?thesis
    using assms apply (cases "is_ConstantExpr y") apply (cases "is_ConstantExpr z") prefer 3
    apply (cases "is_ConstantExpr z") prefer 2
    apply (simp add: add_strict_mono size_binary_lhs size_binary_rhs sizelhs_nonconst)
    apply (metis add_mono_thms_linordered_field(1) bin_op_size.simps(13) less_add_same_cancel2
           less_SucI size_bin_ops_div size_pos sizelhs_const sizerhslhs_nonconst trans_less_add1)
    apply (metis add_2_eq_Suc' add_lessD1 bin_op_size.simps(13) not_less_eq size_binary_rhs
           sizelhs_const)
    by (metis const_size Suc_mono sizerhslhs_const add_Suc_shift bin_op_size.simps(13) add.commute
        is_ConstantExpr_def plus_1_eq_Suc size_bin_ops_div size_binary_lhs sizelhs_nonconst Suc_1
        trans_less_add2)
qed

lemma size_binop_equality_commute_lhs[size_simps]:
  assumes "op \<noteq> BinDiv"
  shows "size (BinaryExpr BinIntegerEquals y z) <
         Suc (Suc (size (BinaryExpr op y x) + size (BinaryExpr op x z)))"
proof -
  have sizerhslhs_const: "is_ConstantExpr x \<Longrightarrow>
       size (BinaryExpr op y x) = (bin_op_size ((size y) + 2) op)"
    using size_binary_const by auto
  have sizerhslhs_nonconst: "\<not>(is_ConstantExpr) x \<Longrightarrow>
       size (BinaryExpr op y x) = (bin_op_size ((size y) + (size x) + 2) op)"
    using size_non_add by auto
  have sizelhs_const: "is_ConstantExpr z \<Longrightarrow>
       size (BinaryExpr BinIntegerEquals y z) = (bin_op_size ((size y) + 2) BinIntegerEquals)"
    by (meson size_binary_const)
  show ?thesis
    using assms apply (cases "is_ConstantExpr y") apply (cases "is_ConstantExpr z") prefer 3
    apply (cases "is_ConstantExpr z") prefer 4
    apply (smt (verit, del_insts) Canonicalization.const_size IRExpr.collapse(6) add.assoc less_SucI
           add.commute bin_op_size.simps(13) less_add_Suc1 size_bin_ops_div size_bin_rhs_nonconst)
    apply (metis add_mono_thms_linordered_field(1) bin_op_size.simps(13) less_SucI sizelhs_const
           less_add_same_cancel1 size_bin_ops_div size_pos sizerhslhs_const sizerhslhs_nonconst
           trans_less_add1)
    by (metis add.commute size_binop_equality_commute_rhs size_non_add size_bin_rhs_const)+
qed

lemmas arith[size_simps] = Suc_leI add_strict_increasing order_less_trans trans_less_add2

definition well_formed_equal :: "Value \<Rightarrow> Value \<Rightarrow> bool"
  (infix "\<approx>" 50) where
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"

lemma well_formed_equal_defn [simp]:
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"
  unfolding well_formed_equal_def by simp

subsection \<open> Helpful lemmas for canonicalization proofs \<close>

subsubsection \<open> Evaluation lemmas \<close>

lemma const_eval_is_const:
  assumes "wf_value n"
  shows "[m,p] \<turnstile> exp[const (n)] \<mapsto> n"
  by (simp add: assms IRTreeEval.evaltree.ConstantExpr)

subsubsection \<open> Operator commutativity lemmas \<close>

lemma val_add_commutative:
  "val[x + y] = val[y + x]"
  by (cases x; cases y; auto simp: add.commute)

lemma val_and_commutative:
  "val[x & y] = val[y & x]"
  by (cases x; cases y; auto simp: and.commute)

lemma val_eq_commutative:
  "val[x eq y] = val[y eq x]"
  by (cases y; cases x; auto simp: unwrap_bool_to_val)

lemma val_mul_commutative:
  "val[x * y] = val[y * x]"
  by (cases x; cases y; auto simp: mult.commute)

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

lemma exp_mul_commutative:
  "exp[x * y] \<ge> exp[y * x]"
  by (auto simp: val_mul_commutative)

lemma exp_or_commutative:
  "exp[x | y] \<ge> exp[y | x]"
  by (auto simp: val_or_commutative)

lemma exp_xor_commutative:
  "exp[x \<oplus> y] \<ge> exp[y \<oplus> x]"
  by (auto simp: val_xor_commutative)

subsubsection \<open> Operator associativity lemmas \<close>

lemma val_add_associative:
  "val[(x + y) + z] = val[x + (y + z)]"
  by (cases x; cases y; cases z; auto simp: ab_semigroup_add_class.add_ac(1))

lemma val_and_associative:
  "val[(x & y) & z] = val[x & (y & z)]"
  by (cases x; cases y; cases z; auto simp: and.assoc)

lemma val_mul_associative:
  "val[(x * y) * z] = val[x * (y * z)]"
  apply (cases x; cases y; cases z; auto)
  by (metis (no_types, lifting) mergeTakeBit mult.assoc new_int.elims new_int_take_bits)

lemma val_or_associative:
  "val[(x | y) | z] = val[x | (y | z)]"
  by (cases x; cases y; cases z; auto simp: or.assoc)

lemma val_xor_associative:
  "val[(x \<oplus> y) \<oplus> z] = val[x \<oplus> (y \<oplus> z)]"
  by (cases x; cases y; cases z; auto simp: xor.assoc)

lemma exp_add_associative:
  "exp[(x + y) + z] \<ge> exp[x + (y + z)]"
  using val_add_associative by fastforce

lemma exp_and_associative:
  "exp[(x & y) & z] \<ge> exp[x & (y & z)]"
  using val_and_associative by fastforce

lemma exp_mul_associative:
  "exp[(x * y) * z] \<ge> exp[x * (y * z)]"
  using val_mul_associative by fastforce

lemma exp_or_associative:
  "exp[(x | y) | z] \<ge> exp[x | (y | z)]"
  using val_or_associative by fastforce

lemma exp_xor_associative:
  "exp[(x \<oplus> y) \<oplus> z] \<ge> exp[x \<oplus> (y \<oplus> z)]"
  using val_xor_associative by fastforce

subsubsection \<open> Operator self lemmas \<close>

lemma val_xor_self:
  assumes "x = IntVal b xv"
  shows "val[x \<oplus> x] = val[IntVal b 0]"
  using assms by (cases x; auto)

end