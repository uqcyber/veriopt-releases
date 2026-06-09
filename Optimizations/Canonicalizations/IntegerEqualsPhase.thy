subsection \<open>IntegerEqualsNode Phase\<close>

theory IntegerEqualsPhase
  imports
    Common
    Proofs.StampEvalThms
begin

context stamp_mask
begin

lemma val_equal_xor_one_shift_64:
  assumes "x = IntVal xb xvv"
  assumes "b = 64"
  assumes "xvv \<in> {0, 1}"
  assumes "val[(x \<oplus> (IntVal b 1)) eq (IntVal b cv)] \<noteq> UndefVal"
  shows "val[(x \<oplus> (IntVal b 1)) eq (IntVal b cv)] = val[x eq (new_int b (xor cv 1))]"
  using assms unfolding assms(2) apply auto
  apply (smt (verit) bit.xor_left_self xor.right_neutral)
  by (smt (verit, best) bit.xor_left_self xor.assoc xor.right_neutral)

lemma exp_equal_xor_one_shift_64:
  assumes "b = 64"
  assumes "stamp_expr x = IntegerStamp 64 lo hi"
  assumes "wf_stamp x"
  assumes "\<up>x = 1"
  shows "exp[(x \<oplus> (const (IntVal b 1))) eq (const (IntVal b cv))] \<ge>
         exp[x eq (const (new_int b (xor cv 1)))]"
  using assms apply auto subgoal premises p for m p xa
proof -
  obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
    using p(6) by auto
  obtain xbb xvv where xvv: "xa = IntVal xbb xvv"
    using p(2,3,4) stamp_mask_up_1_implies_0_1 xa by blast
  have zeroOne: "xvv \<in> {0, 1}"
    using p(2,3,4) stamp_mask_up_1_implies_0_1 xa xvv by blast
  have constE: "[m,p] \<turnstile> exp[const (new_int b (xor cv 1))] \<mapsto> val[new_int b (xor cv 1)]"
    by (metis ConstantExpr le_refl p(1) validIntConst wf_value_def zero_less_numeral)
  have rhsE: "[m,p] \<turnstile> exp[x eq (const (new_int b (xor cv 1)))] \<mapsto> val[xa eq (new_int b (xor cv 1))]"
    by (metis (no_types, lifting) BinaryExpr xa bin_eval.simps(13) constE evalDet p(1,5,6) zeroOne
        val_equal_xor_one_shift_64 xvv)
  have eq: "val[xa eq (IntVal 64 (xor cv 1))] = val[(xa \<oplus> (IntVal 64 1)) eq (IntVal 64 cv)]"
    using assms xvv zeroOne apply auto
    apply (metis (mono_tags, opaque_lifting) bit.xor_left_self unwrap_bool_to_val xor.right_neutral)
    by (smt (verit, ccfv_SIG) bit.xor_left_self xor.assoc xor.right_neutral)
  have "[m,p] \<turnstile> exp[x eq (const (IntVal 64 (xor cv 1)))] \<mapsto>
                val[(xa \<oplus> (IntVal 64 1)) eq (IntVal 64 cv)]"
    using eq p(1) rhsE by auto
  then show ?thesis
    by (metis evalDet p(6) xa)
qed
  done

end

phase IntegerEqualsNode
  terminating size
begin

(* Word level proofs *)
lemma bin_xor_equality: "((xor x y) = (xor x z)) \<longleftrightarrow> (y = z)" for x y z::int64
  by (metis bit.xor_left_self)

lemma bin_subtraction_equality: "((x - y) = (x - z)) \<longleftrightarrow> (y = z)" for x y z::int64
  by auto

lemma bin_subtraction_equality_swapped: "((y - x) = (z - x)) \<longleftrightarrow> (y = z)" for x y z::int64
  by auto

lemma bin_xor_zero_equality: "(x = (xor x y)) \<longleftrightarrow> y = 0" for x y::int64
  by (metis bin_xor_equality xor.right_neutral)

lemma bin_sub_zero_equality: "(x = (x - y)) \<longleftrightarrow> y = 0" for x y::int64
  by simp

lemma bin_not_self_equality: "(x = (not x)) \<longleftrightarrow> False" for x::int64
  by (metis less_eq_mask takeBitNot)

(* Value level proofs *)
lemma val_addition_equality:
  assumes "x = new_int n xv"
  assumes "y = new_int n yv"
  assumes "z = new_int n zv"
  assumes "val[(x + y) eq (x + z)] \<noteq> UndefVal"
  shows "val[(x + y) eq (x + z)] = val[y eq z]"
  using assms apply (cases x; cases y; cases z; auto)
proof -
  have "\<forall>a b. - (b::64 word) + (b + a) = a"
    by auto
  then show "bool_to_val (take_bit n (xv + yv) = take_bit n (xv + zv)) =
             bool_to_val (take_bit n yv = take_bit n zv)"
    by (smt (z3) ValueThms.take_bit_dist_addR)
qed

lemma val_xor_equality:
  assumes "x = new_int n xv"
  assumes "y = new_int n yv"
  assumes "z = new_int n zv"
  assumes "val[(x \<oplus> y) eq (x \<oplus> z)] \<noteq> UndefVal"
  shows "val[(x \<oplus> y) eq (x \<oplus> z)] = val[y eq z]"
  using assms apply (cases x; cases y; cases z; auto) by (simp add: bin_xor_equality)

lemma val_subtraction_equality:
  assumes "x = new_int n xv"
  assumes "y = new_int n yv"
  assumes "z = new_int n zv"
  assumes "val[(x - y) eq (x - z)] \<noteq> UndefVal"
  shows "val[(x - y) eq (x - z)] = val[y eq z]"
  using assms apply (cases x; cases y; cases z; auto)
  by (smt (verit, ccfv_threshold) ValueThms.take_bit_dist_subR add_diff_cancel_left' diff_diff_eq2)

lemma val_subtraction_equality_swapped:
  assumes "x = new_int n xv"
  assumes "y = new_int n yv"
  assumes "z = new_int n zv"
  assumes "val[(y - x) eq (z - x)] \<noteq> UndefVal"
  shows "val[(y - x) eq (z - x)] = val[y eq z]"
proof -
  have "val[z - x] = IntVal n (take_bit n (zv - xv))"
    by (simp add: assms(1,3))
  moreover have "val[y - x] = IntVal n (take_bit n (yv - xv))"
    by (simp add: assms(1,2))
  ultimately show ?thesis
    by (smt (verit) ValueThms.take_bit_dist_addL assms(2,3) diff_add_cancel intval_equals.simps(1)
        new_int.simps)
qed

lemma val_add_zero_equality:
  assumes "x = new_int n xv"
  assumes "y = new_int n yv"
  assumes "val[x eq (x + y)] \<noteq> UndefVal"
  shows "val[x eq (x + y)] = val[y eq (new_int n 0)]"
  using assms add_cancel_right_right apply auto
  by (smt (verit, ccfv_threshold) ValueThms.take_bit_dist_addR add_cancel_right_right take_bit_of_0
      minus_add_cancel)

lemma val_xor_zero_equality:
  assumes "x = new_int n xv"
  assumes "y = new_int n yv"
  assumes "val[x eq (x \<oplus> y)] \<noteq> UndefVal"
  shows "val[x eq (x \<oplus> y)] = val[y eq (new_int n 0)]"
  using assms bin_xor_zero_equality by auto

lemma val_sub_zero_equality:
  assumes "x = new_int n xv"
  assumes "y = new_int n yv"
  assumes "val[x eq (x - y)] \<noteq> UndefVal"
  shows "val[x eq (x - y)] = val[y eq (new_int n 0)]"
  using assms apply (cases x; cases y; auto)
  by (smt (verit, del_insts) diff_add_eq diff_diff_eq2 take_bit_of_0 ValueThms.take_bit_dist_subR
      diff_self diff_zero)

lemma val_not_self_equality:
  assumes "x = new_int n xv"
  assumes "1 \<le> n"
  shows "val[x eq (~x)] = val[false]"
proof -
  have "take_bit n (not xv) \<noteq> take_bit n xv"
    using assms(2) takeBitNot by auto
  then show ?thesis
    using assms(1) apply auto by (simp add: take_bit_not_take_bit)
qed

lemma val_equal_substraction:
  assumes "x = new_int n xv"
  assumes "y = new_int n yv"
  shows "val[(x - y) eq (new_int n 0)] = val[x eq y]"
  using assms right_minus_eq apply auto
  by (smt (verit, del_insts) ValueThms.take_bit_dist_subR right_minus_eq diff_0 diff_right_commute
      minus_diff_eq take_bit_of_0)

lemma val_xor_not_fall_through:
  assumes "x = new_int b xv"
  assumes "y = new_int b yv"
  shows "val[(x \<oplus> y) eq (\<not>x)] = val[y eq (new_int b (not 0))]"
  using assms apply auto
  by (smt (verit, ccfv_SIG) bit.xor_cancel_right bit.xor_left_self mask_eq_take_bit_minus_one
      take_bit_not_take_bit take_bit_xor)

lemma val_and_or_eq_64:
  assumes "val[(x & y) eq (x | y)] \<noteq> UndefVal"
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  shows "val[(x & y) eq (x | y)] = val[x eq y]"
  using assms apply (cases x; cases y; auto)
  subgoal premises p
    proof -
      have unfold_x: "take_bit 64 xv = take_bit (LENGTH(64)) xv"
        by simp
      have unfold_y: "take_bit 64 yv = take_bit (LENGTH(64)) yv"
        by auto
      then show ?thesis
        unfolding unfold_x unfold_y take_bit_length_eq
        by (smt (verit, ccfv_SIG) and.idem word_ao_absorbs(5) word_ao_equiv word_bw_assocs(1))
    qed
  done

lemma val_not_abs:
  assumes "x = new_int xb xv"
  assumes "val[abs(x)] \<noteq> UndefVal"
  assumes "xb \<ge> 1"
  shows "val[(\<not>x) eq (abs(x))] = val[false]"
  using assms apply (cases x) using assms(1) prefer 2 defer apply (simp, simp, simp, simp)
  proof (cases "int_signed_value xb xv < 0")
    case True
    obtain xvv where xvv: "xvv = (take_bit xb xv)"
      by simp
    have xIntVal: "x = IntVal xb xvv"
      by (simp add: assms(1) xvv)
    have absX: "val[abs(x)] = new_int xb (-xvv)"
      unfolding xIntVal xvv apply simp
      by (metis One_nat_def True ValueThms.signed_take_take_bit assms(3) int_signed_value.simps
          order_less_le_trans zero_less_one)
    have notX: "val[\<not>x] = new_int xb (not xv)"
      by (simp add: take_bit_not_take_bit xIntVal xvv)
    have "take_bit xb 1 \<noteq> 0"
      using assms(3) by force
    then have "take_bit xb (- (xv + 1)) \<noteq> take_bit xb (- xv)"
      by (smt (verit, del_insts) ValueThms.take_bit_dist_addL add.assoc add.commute take_bit_of_0
          add.inverse_inverse add.inverse_neutral add.right_inverse add_minus_cancel)
    then have negNotNot: "(take_bit xb (- xv) = take_bit xb (not (take_bit xb xv))) = False"
      by (metis (no_types, opaque_lifting) minus_eq_not_plus_1 take_bit_not_take_bit
          verit_minus_simplify(4) word_not_not)
    have wordNotEq: "take_bit xb (not xv) \<noteq> take_bit xb (- xv)"
      by (metis negNotNot take_bit_not_take_bit)
    have "val[(\<not>x) eq (abs(x))] = val[false]"
      unfolding absX notX apply simp by (simp add: wordNotEq xvv)
    then show ?thesis
      by blast
next
    case False
    obtain xvv where xvv: "xvv = (take_bit xb xv)"
      by simp
    have xIntVal: "x = IntVal xb xvv"
      by (simp add: assms(1) xvv)
    have absX: "val[abs(x)] = new_int xb xv"
      unfolding xIntVal xvv apply simp
      by (metis False One_nat_def ValueThms.signed_take_take_bit int_signed_value.simps neq0_conv
          take_bit_0)
    have "val[(\<not>x) eq (abs(x))] = val[false]"
      using absX assms(1,3) val_eq_commutative val_not_self_equality takeBitNot by auto
    then show ?thesis
      by blast
  qed

lemma val_negate_false:
  assumes "x = new_int xb xv"
  assumes "xb \<ge> 1"
  shows "val[(-x) eq (~x)] = val[false]"
  using assms apply (cases x; auto)
  subgoal premises p
  proof (cases "xb = 1")
    case True
    have xvv: "-xv = (not xv) + 1"
      using minus_eq_not_plus_1 by auto
    have "take_bit 1 (-xv) \<noteq> take_bit 1 (not xv)"
      unfolding xvv
      by (metis (no_types, opaque_lifting) One_nat_def ValueThms.take_bit_dist_addR Word.mask_Suc_0
          add.right_inverse take_bit_minus_one_eq_mask take_bit_of_0 xvv word_add_not zero_neq_one)
    then show ?thesis
      by (metis (mono_tags, opaque_lifting) True bool_to_val.simps(2) take_bit_not_take_bit)
  next
    case False
    have "xb \<ge> 2"
      using False assms(2) by force
    then have "take_bit xb 1 \<noteq> 0"
      by simp
    then have "take_bit xb (- (xv + 1)) \<noteq> take_bit xb (- xv)"
      by (metis (no_types) ValueThms.take_bit_dist_subR add.right_inverse minus_add_cancel
          take_bit_of_0 uminus_add_conv_diff verit_minus_simplify(4))
    then have "(take_bit xb (- xv) = take_bit xb (not (take_bit xb xv))) = False"
      by (metis (no_types, opaque_lifting) minus_eq_not_plus_1 take_bit_not_take_bit
          verit_minus_simplify(4) word_not_not)
    then show ?thesis
      using bool_to_val.simps(2) by auto
qed
  done

lemma val_negate_sub_right:
  assumes "x = new_int xb xv"
  assumes "y = new_int yb yv"
  assumes "val[(-x) eq (y - x)] \<noteq> UndefVal"
  shows "val[(-x) eq (y - x)] = val[y eq (new_int yb 0)]"
  using assms apply (cases x; cases y; auto)
  by (smt (verit, ccfv_SIG) ValueThms.take_bit_dist_neg ValueThms.take_bit_dist_subL take_bit_of_0
      cancel_comm_monoid_add_class.diff_cancel diff_right_commute diff_zero minus_diff_commute
      minus_diff_eq verit_minus_simplify(3))

lemma val_negate_eq_zero:
  assumes "x = new_int xb xv"
  shows "val[(-x) eq (new_int b 0)] = val[x eq (new_int b 0)]"
  using assms apply (cases x; auto)
  by (smt (verit, del_insts) ValueThms.take_bit_dist_neg neg_0_equal_iff_equal
      verit_minus_simplify(4))

lemma val_negate_eq:
  assumes "x = new_int xb xv"
  assumes "y = new_int yb yv"
  shows "val[(-x) eq (-y)] = val[x eq y]"
  using assms apply (cases x; cases y; auto)
  by (smt (verit, ccfv_threshold) ValueThms.take_bit_dist_neg verit_minus_simplify(4))

lemma val_not_zero_neg_one:
  assumes "x = new_int xb xv"
  shows "val[(\<not>x) eq (new_int xb 0)] = val[x eq (new_int xb (not 0))]"
  using assms apply (cases x; auto)
  by (smt (verit, best) take_bit_minus_one_eq_mask take_bit_not_mask_eq_0 take_bit_not_take_bit
      verit_comp_simplify1(2) word_not_not)

lemma val_not_eq:
  assumes "x = new_int xb xv"
  assumes "y = new_int yb yv"
  shows "val[(~x) eq (~y)] = val[x eq y]"
  using assms apply (cases x; cases y; auto) by (simp add: take_bit_not_iff)

lemma val_equal_xor:
  assumes "x = new_int b xv"
  assumes "y = new_int b yv"
  shows "val[(x \<oplus> y) eq (IntVal b 0)] = val[x eq y]"
  using assms apply (cases x; cases y; auto)
  by (smt (verit) bin_xor_zero_equality bit.xor_left_self)

(* Exp level proofs *)
lemma exp_addition_equality:
  shows "exp[(x + y) eq (x + z)] \<ge> exp[y eq z]"
  apply auto
  subgoal premises p for m p xa ya xaa za
  proof -
  obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
    using p(2) by auto
  obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
    using p(3) by auto
  obtain za where za: "[m,p] \<turnstile> z \<mapsto> za"
    using p(6) by auto
  have l_add: "val[xa + ya] \<noteq> UndefVal"
    by (metis evalDet p(2,3,4) xa ya)
  have r_add: "val[xa + za] \<noteq> UndefVal"
    by (metis evalDet p(5,6,7) xa za)
  have xEq: "xa = xaa"
    using evalDet p(5) xa by blast
  obtain xn xv where xa_int: "xa = new_int xn xv"
    by (metis new_int.elims eval_unused_bits_zero evaltree_not_undef intval_add.simps(3,4,5) l_add
        intval_logic_negation.cases xa)
  obtain yn yv where ya_int: "ya = new_int yn yv"
    by (metis evaltree_not_undef intval_add.simps(7,8,9) intval_logic_negation.cases l_add ya
        eval_unused_bits_zero new_int.elims)
  obtain zn zv where za_int: "za = new_int zn zv"
    by (metis eval_unused_bits_zero Value.exhaust evaltree_not_undef intval_add.simps(7,8,9) evalDet
        intval_equals.simps(6) p(1,6) za new_int.elims)
  have width: "xn = yn"
    by (metis intval_add.simps(1) l_add new_int.elims xa_int ya_int)
  moreover have "xn = zn"
    by (metis intval_add.simps(1) new_int.elims r_add xEq xa_int za_int)
  then have "val[(xa + ya) eq (xa + za)] = val[ya eq za]"
    by (metis p(1,2,3,5,6) width xa_int ya_int za_int xEq val_addition_equality evalDet ya za)
  then show ?thesis
    by (metis BinaryExpr bin_eval.simps(13) evalDet p(1,2,3,5,6) xEq ya za)
qed
  done

lemma exp_xor_equality:
  shows "exp[(x \<oplus> y) eq (x \<oplus> z)] \<ge> exp[y eq z]"
  apply auto
  subgoal premises p for m p xa ya xaa za
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(2) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using p(3) by auto
    obtain za where za: "[m,p] \<turnstile> z \<mapsto> za"
      using p(6) by auto
    have defined: "val[(xa \<oplus> ya) eq (xaa \<oplus> za)] \<noteq> UndefVal"
      by (metis evalDet p(1,2,3,6) xa ya za)
    have xzDefined: "val[xa \<oplus> za] \<noteq> UndefVal"
      by (metis evalDet p(5,6,7) xa za)
    have xyDefined: "val[xa \<oplus> ya] \<noteq> UndefVal"
      by (metis evalDet p(2,3,4) xa ya)
    have xEq: "xa = xaa"
      using evalDet p(5) xa by auto
    obtain xn xv where xv: "xa = IntVal xn xv"
      by (metis intval_equals.simps(6) intval_logic_negation.cases intval_xor.simps(2,3,4,5) p(1)
          xEq)
    obtain yn yv where yv: "ya = IntVal yn yv"
      by (metis xyDefined intval_logic_negation.cases intval_xor.simps(6,7,8,9))
    obtain zn zv where zv: "za = IntVal zn zv"
      by (metis Value.exhaust xzDefined intval_xor.simps(6,7,8,9))
    have newIntX: "xa = new_int xn xv"
      using eval_unused_bits_zero xa xv by auto
    have newIntY: "ya = new_int yn yv"
      using eval_unused_bits_zero ya yv by auto
    have newIntZ: "za = new_int zn zv"
      using eval_unused_bits_zero za zv by fastforce
    have width: "xn = yn \<and> xn = zn"
      by (metis xyDefined xzDefined intval_xor.simps(1) new_int_bin.simps xv yv zv)+
    have "val[(xa \<oplus> ya) eq (xaa \<oplus> za)] = val[ya eq za]"
      using defined newIntX newIntY newIntZ val_xor_equality width xEq by blast
    then show ?thesis
      by (metis BinaryExpr bin_eval.simps(13) evalDet p(1,2,3,6) xa xEq ya za)
  qed
  done
  
lemma exp_subtraction_equality:
  shows "exp[(x - y) eq (x - z)] \<ge> exp[y eq z]"
  apply auto
  subgoal premises p for m p xa ya xaa za
  proof -
  obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
    using p(2) by auto
  obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
    using p(3) by auto
  obtain za where za: "[m,p] \<turnstile> z \<mapsto> za"
    using p(6) by auto
  have defined: "val[(xa - ya) eq (xa - za)] \<noteq> UndefVal"
    by (metis evalDet p(1,2,3,5,6) xa ya za)
  have xyDefined: "val[xa - ya] \<noteq> UndefVal"
    by (metis evalDet p(2,3,4) xa ya)
  have xzDefined: "val[xa - za] \<noteq> UndefVal"
    by (metis evalDet p(5,6,7) xa za)
  have xEq: "xa = xaa"
    using evalDet p(5) xa by blast
  obtain xn xv where xv: "xa = IntVal xn xv"
    by (metis intval_equals.simps(6) intval_logic_negation.cases intval_sub.simps(2,3,4,5) p(1) xEq)
  obtain yn yv where yv: "ya = IntVal yn yv"
    by (metis defined intval_equals.simps(2) intval_logic_negation.cases intval_sub.simps(6,7,8,9))
  obtain zn zv where zv: "za = IntVal zn zv"
    by (metis defined intval_equals.simps(6) intval_is_null.cases intval_sub.simps(6,7,8,9))
  have newIntX: "xa = new_int xn xv"
    using eval_unused_bits_zero xa xv by simp
  have newIntY: "ya = new_int yn yv"
    using eval_unused_bits_zero ya yv by simp
  have newIntZ: "za = new_int zn zv"
    using eval_unused_bits_zero za zv by fastforce
  have width: "xn = yn \<and> xn = zn"
    by (metis xyDefined xzDefined intval_sub.simps(1) new_int_bin.elims xv yv zv)+
  then have "val[(xa - ya) eq (xa - za)] = val[ya eq za]"
    using defined newIntX newIntY newIntZ val_subtraction_equality by blast
  then show ?thesis
    by (metis BinaryExpr bin_eval.simps(13) evalDet p(1,2,3,6) xEq xa ya za)
qed
  done

lemma exp_subtraction_equality_swapped:
  shows "exp[(y - x) eq (z - x)] \<ge> exp[y eq z]"
  apply auto
  subgoal premises p for m p ya xa za xaa
  proof -
  obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
    using p(2) by auto
  obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
    using p(3) by auto
  obtain za where za: "[m,p] \<turnstile> z \<mapsto> za"
    using p(5) by auto
  have yxDefined: "val[ya - xa] \<noteq> UndefVal"
    by (metis evalDet p(2,3,4) xa ya)
  have defined: "val[(ya - xa) eq (za - xa)] \<noteq> UndefVal"
    by (metis evalDet p(1,2,3,5,6) xa ya za)
  have zxDefined: "val[za - xa] \<noteq> UndefVal"
    using defined by force
  have xEq: "xa = xaa"
    using evalDet p(6) xa by auto
  obtain xn xv where xv: "xa = IntVal xn xv"
    by (metis intval_equals.simps(6) intval_logic_negation.cases intval_sub.simps(6,7,8,9) p(1) xEq)
  obtain yn yv where yv: "ya = IntVal yn yv"
    by (metis evalDet intval_equals.simps(2) intval_is_null.elims intval_sub.simps(2,3,4,5) p(1,2)
        ya)
  obtain zn zv where zv: "za = IntVal zn zv"
    by (metis defined intval_equals.simps(6) intval_is_null.cases intval_sub.simps(2,3,4,5))
  have newIntX: "xa = new_int xn xv"
    using eval_unused_bits_zero xa xv by auto
  have newIntY: "ya = new_int yn yv"
    using eval_unused_bits_zero ya yv by auto
  have newIntZ: "za = new_int zn zv"
    using eval_unused_bits_zero za zv by auto
  have width: "xn = yn \<and> xn = zn"
    by (metis yxDefined zxDefined intval_sub.simps(1) new_int_bin.simps xv yv zv)+
  have "val[(ya - xa) eq (za - xa)] = val[ya eq za]"
    using defined newIntX newIntY newIntZ val_subtraction_equality_swapped width by blast
  then show ?thesis
    by (metis BinaryExpr bin_eval.simps(13) evalDet p(1,2,3,5,6) xEq ya za)
qed
  done

lemma exp_add_zero_equality:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  shows "exp[x eq (x + y)] \<ge> exp[y eq const (IntVal b 0)]"
  apply auto
  subgoal premises p for m p xa xaa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(1) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using p(4) by auto
    have defined: "val[xa eq (xaa + ya)] \<noteq> UndefVal"
      by (metis evalDet p(1,2,4) xa ya)
    have xaEq: "xa = xaa"
      using evalDet p(3) xa by auto
    obtain xn xv where xv: "xa = IntVal xn xv"
      by (metis evaltree_not_undef intval_add.simps(7,8,9) intval_add_sym intval_bits.elims p(5) xa
          xaEq)
    obtain yn yv where yv: "ya = IntVal yn yv"
      by (metis evalDet intval_add.simps(6,7,8,9) intval_logic_negation.cases p(4,5) ya)
    have newIntX: "xa = new_int xn xv"
      using eval_unused_bits_zero xa xv by simp
    have newIntY: "ya = new_int yn yv"
      using eval_unused_bits_zero ya yv by auto
    have width: "xn = yn"
      by (metis evalDet intval_add.simps(1) p(4,5) xaEq xv ya yv)
    have widthB: "yn = b"
      using assms newIntY stamp_eval_same_bits ya by auto
    then have rhsDefined: "val[ya eq (IntVal b 0)] \<noteq> UndefVal"
      using defined newIntX newIntY val_add_zero_equality width widthB xaEq by auto
    have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[ya eq (IntVal b 0)]"
      by (metis bin_eval.simps(13) const_eval_is_const newIntY new_int_zero_is_intval widthB ya
          rhsDefined unfold_binary eval_new_int_has_wf_value_zero)
    then show ?thesis
      by (metis defined evalDet newIntX newIntY new_int_zero_is_intval p(1,4) val_add_zero_equality
          width widthB xa xaEq ya)
  qed
  done

lemma exp_xor_zero_equality:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  shows "exp[x eq (x \<oplus> y)] \<ge> exp[y eq const (IntVal b 0)]"
  apply auto
  subgoal premises p for m p xa xaa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(1) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using p(4) by auto
    have xEq: "xa = xaa"
      using evalDet p(3) xa by auto
    have lhsDefined: "val[xa eq (xa \<oplus> ya)] \<noteq> UndefVal"
      by (metis evalDet p(1,2,4) xa ya xEq)
    have xorDefined: "val[xa \<oplus> ya] \<noteq> UndefVal"
      using lhsDefined by fastforce
    obtain xn xv where xv: "xa = IntVal xn xv"
      by (metis Value.exhaust_sel intval_equals.simps(2,3,4,5) lhsDefined)
    obtain yn yv where yv: "ya = IntVal yn yv"
      by (metis intval_equals.simps(6) intval_logic_negation.cases intval_xor.simps(6,7,8,9)
          lhsDefined)
    have newIntX: "xa = new_int xn xv"
      using eval_unused_bits_zero xa xv by simp
    have newIntY: "ya = new_int yn yv"
      using eval_unused_bits_zero ya yv by simp
    have width: "xn = yn"
      by (metis intval_xor.simps(1) new_int_bin.elims xv yv xorDefined)
    have widthB: "yn = b"
      using assms newIntY stamp_eval_same_bits ya by auto
    have rhsDefined: "val[ya eq (IntVal b 0)] \<noteq> UndefVal"
      using lhsDefined newIntX newIntY val_xor_zero_equality width widthB by force
    have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[ya eq (IntVal b 0)]"
      by (metis BinaryExpr bin_eval.simps(13) newIntY new_int_zero_is_intval rhsDefined widthB ya
          unfold_const eval_new_int_has_wf_value_zero)
    then show ?thesis
      by (metis evalDet lhsDefined newIntX newIntY new_int_zero_is_intval p(1,3,4) width widthB xEq
          ya val_xor_zero_equality)
  qed
  done

lemma exp_sub_zero_equality:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  shows "exp[x eq (x - y)] \<ge> exp[y eq const (IntVal b 0)]"
  apply auto
  subgoal premises p for m p xa xaa ya
  proof - 
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(1) by simp
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using p(4) by auto
    have xEq: "xaa = xa"
      using evalDet p(3) xa by auto
    then have lhsDefined: "val[xa eq (xa - ya)] \<noteq> UndefVal"
      by (metis evalDet p(1,2,3,4) ya)
    obtain xn xv where xv: "xa = IntVal xn xv"
      by (metis Value.exhaust_sel intval_equals.simps(6) intval_sub.simps(2,3,4,5) lhsDefined)
    obtain yn yv where yv: "ya = IntVal yn yv"
      by (metis evalDet intval_logic_negation.cases intval_sub.simps(6,7,8,9) p(4,5) ya)
    then have newIntX: "xa = new_int xn xv"
      using eval_unused_bits_zero xa xv by auto
    then have newIntY: "ya = new_int yn yv"
      using eval_unused_bits_zero ya yv by auto
    have yBits: "yn = b"
      using assms newIntY stamp_eval_same_bits ya by auto
    then have rhsDefined: "val[ya eq (IntVal b 0)] \<noteq> UndefVal"
      using bool_to_val.elims yBits yv by auto
    then have equals: "val[xa eq (xa - ya)] = val[ya eq (new_int b 0)]"
      by (metis intval_equals.simps(6) intval_sub.simps(1) lhsDefined newIntX newIntY xv yBits yv
          new_int_bin.simps val_sub_zero_equality)
    have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[ya eq (IntVal b 0)]"
      by (metis BinaryExpr bin_eval.simps(13) newIntY new_int_zero_is_intval unfold_const ya yBits
          rhsDefined eval_new_int_has_wf_value_zero)
    then show ?thesis
      by (metis equals evalDet new_int_zero_is_intval p(1,3,4) xEq ya)
    qed
    done

lemma exp_not_self_equality:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  shows "exp[(~x) eq x] \<ge> exp[const val[false]]"
  apply auto
  subgoal premises p for m p xa xaa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(1) by auto
    then have lhsDefined: "val[xa eq (~xa)] \<noteq> UndefVal"
      by (metis evalDet p(1,2,3) val_eq_commutative)
    have xEq: "xa = xaa"
      using evalDet p(3) xa by auto
    obtain xn xv where xv: "xa = IntVal xn xv"
      by (metis Value.exhaust_sel intval_equals.simps(2) intval_not.simps(3,4,5) lhsDefined p(4)
          xEq)
    have newIntX: "xa = new_int xn xv"
      using eval_unused_bits_zero xa xv by fastforce
    have width: "xn = b"
      using assms newIntX p(3) stamp_eval_same_bits xEq by blast
    have bits: "b \<noteq> 0"
      using assms p(1) wf_integerstamp_implies_nonzero_bits by auto
    have "val[xa eq (~xa)] = IntVal 32 0"
      using bits newIntX val_not_self_equality width by force
    then show ?thesis
      using evalDet p(1,3) val_eq_commutative xEq by fastforce
  qed
  done

lemma exp_equal_substraction:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  shows "exp[(x - y) eq const (IntVal b 0)] \<ge> exp[x eq y]"
  apply auto
  subgoal premises p for m p xa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(2) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using p(3) by auto
    have lhsDefined: "val[(xa - ya) eq (IntVal b 0)] \<noteq> UndefVal"
      by (metis evalDet p(1,2,3) xa ya)
    have xyDefined: "val[xa - ya] \<noteq> UndefVal"
      by (metis evalDet p(2,3,4) xa ya)
    obtain xn xv where xv: "xa = IntVal xn xv"
      by (metis ExpIntBecomesIntVal assms wf_stamp_def xa)
    obtain yn yv where yv: "ya = IntVal yn yv"
      by (metis Value.exhaust intval_sub.simps(6,7,8,9) xyDefined)
    have newIntX: "xa = new_int xn xv"
      using eval_unused_bits_zero xa xv by auto
    have newIntY: "ya = new_int yn yv"
      using eval_unused_bits_zero ya yv by auto
    have width: "xn = yn"
      by (metis new_int_bin.elims xv yv xyDefined intval_sub.simps(1))
    have widthB: "yn = b"
      using newIntX stamp_eval_same_bits width xa assms by blast
    then have "val[(xa - ya) eq (new_int b 0)] = val[xa eq ya]"
      using val_equal_substraction lhsDefined newIntX newIntY width widthB by blast
    then show ?thesis
      by (metis BinaryExpr bin_eval.simps(13) evalDet new_int_zero_is_intval p(1,2,3) xa ya)
  qed
  done

lemma exp_equal_xor:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  shows "exp[(x \<oplus> y) eq const (IntVal b 0)] \<ge> exp[x eq y]"
  apply auto
  subgoal premises p for m p xa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(2) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using p(3) by auto
    have xorDefined: "val[xa \<oplus> ya] \<noteq> UndefVal"
      by (metis evalDet p(2,3,4) xa ya)
    obtain xb xv where xv: "xa = IntVal xb xv"
      by (metis ExpIntBecomesIntVal assms wf_stamp_def xa)
    obtain yb yv where yv: "ya = IntVal yb yv"
      by (metis intval_logic_negation.cases xorDefined intval_xor.simps(6,7,8,9))
    have newIntX: "xa = new_int xb xv"
      using eval_unused_bits_zero xa xv by force
    have newIntY: "ya = new_int yb yv"
      using eval_unused_bits_zero ya yv by auto
    have "xb = yb"
      by (metis new_int_bin.elims xv yv xorDefined intval_xor.simps(1))
    then show ?thesis
      by (metis BinaryExpr assms bin_eval.simps(13) evalDet newIntX newIntY p(1,2,3) val_equal_xor
          stamp_eval_same_bits xa ya)
  qed
  done

lemma exp_and_or_eq_64:
  assumes "stamp_expr x = IntegerStamp 64 xl xh"
  assumes "stamp_expr y = IntegerStamp 64 yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  shows "exp[(x & y) eq (x | y)] \<ge> exp[x eq y]"
  apply auto
  subgoal premises p for m p xa ya xaa yaa
    proof -
      obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
        using p(2) by auto
      obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
        using p(3) by auto
      obtain xw where xw: "xv = IntVal 64 xw"
        by (metis assms(1,3) valid_int wf_stamp_def xv)
      have val: "val[((xv & yv) eq (xv | yv)) = (xv eq yv)]"
        by (metis assms(2,4) evalDet p(1,2,3,5,6) val_and_or_eq_64 valid_int wf_stamp_def xv xw yv)
      then show ?thesis
        by (metis bin_eval.simps(13) evalDet p(1,2,3,5,6) unfold_binary xv yv)
    qed
  done

lemma exp_xor_not_fall_through:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  shows "exp[(x \<oplus> y) eq (\<not>x)] \<ge> exp[y eq (const (new_int b (not 0)))]"
  using assms apply auto
  subgoal premises p for m p xa ya xaa
  proof -
    obtain b xv where xa: "[m,p] \<turnstile> x \<mapsto> new_int b xv"
      by (metis eval_unused_bits_zero intval_not.elims new_int.elims p(9,10))
    obtain yv where ya: "[m,p] \<turnstile> y \<mapsto> new_int b yv"
      by (metis new_int.elims p(1,2,3,4,7) valid_int valid_value.simps(1) wf_stamp_def xa)
    have yaEval: "[m,p] \<turnstile> y \<mapsto> ya"
      by (simp add: p(7))
    have xaaEquiv: "xaa = xa"
      using evalDet p(6,9) by auto
    then have wfVal: "wf_value (new_int b (not 0))"
      using eval_new_int_has_wf_value_all_ones xa by auto
    have rhs: "[m,p] \<turnstile> exp[y eq (const (new_int b (not 0)))] \<mapsto> val[ya eq (new_int b (not 0))]"
      by (metis (no_types, lifting) yaEval bin_eval.simps(13) val_xor_not_fall_through evalDet wfVal
          p(5,6) unfold_binary unfold_const xa xaaEquiv ya)
    have "val[(xa \<oplus> ya) eq (\<not>xa)] = val[ya eq (new_int b (not 0))]"
      by (metis val_xor_not_fall_through evalDet p(6,7) xa ya)
    then show ?thesis
      by (metis bit.compl_zero mask_eq_take_bit_minus_one new_int.elims p(2,4) xaaEquiv wf_stamp_def
          valid_value.simps(1) rhs ya)
   qed
   done

lemma exp_not_abs:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  assumes "xb \<ge> 1"
  shows "exp[(~x) eq (abs(x))] \<ge> exp[false]"
  using assms apply auto subgoal premises p for m p xa
  proof -
    obtain xv where xa: "[m,p] \<turnstile> x \<mapsto> new_int xb xv"
      by (metis p(1,2,5) stamp_eval_same_bits wf_integerstamp_eval_is_new_int)
    have absNotUndef: "val[abs(xa)] \<noteq> UndefVal"
      using evalDet p(5,7,8) xa by blast
    have "val[(~xa) eq (abs(xa))] = val[false]"
      using val_not_abs by (meson absNotUndef assms(3) xa evalDet p(5))
    then show ?thesis
      by (metis evalDet false_always_evals p(5,7))
  qed
  done

lemma exp_negate_not_false:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  assumes "xb \<ge> 1"
  shows "exp[(-x) eq (~x)] \<ge> exp[false]"
  using assms apply auto
  by (metis assms(3) evalDet stamp_eval_same_bits unfold_const val_negate_false wf_value_false
      wf_integerstamp_eval_is_new_int)

lemma exp_negate_sub_right:
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  assumes "stamp_expr y = IntegerStamp yb yl yh"
  shows "exp[(-x) eq (y - x)] \<ge> exp[y eq (const new_int yb 0)]"
  using assms apply auto
  subgoal premises p for m p ya xa xaa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(9) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using p(6) by auto
    obtain xv xbb where xv: "xa = new_int xbb xv"
      using p(1,3) wf_integerstamp_eval_is_new_int xa by blast
    obtain yv ybb where yv: "ya = new_int ybb yv"
      using p(2,4) wf_integerstamp_eval_is_new_int ya by blast
    have yWidth: "ybb = yb"
      using p(2,4) stamp_eval_same_bits ya yv by blast
    have lhsEval: "[m,p] \<turnstile> exp[(-x) eq (y - x)] \<mapsto> val[(-xa) eq (ya - xa)]"
      by (metis evalDet xa ya unfold_binary bin_eval.simps(13,2) unary_eval.simps(2) p(5,6,7,8,9,10)
          UnaryExpr)
    have lhsDef: "val[(-xa) eq (ya - xa)] \<noteq> UndefVal"
      apply auto using xa ya lhsEval by (simp add: evaltree_not_undef)
    have "val[(-xa) eq (ya - xa)] = val[(ya) eq (new_int yb 0)]"
      using lhsDef val_negate_sub_right xv yWidth yv by blast
    then show ?thesis
      by (metis (no_types, opaque_lifting) BinaryExpr bin_eval.simps(13) const_eval_is_const evalDet
          new_int_zero_is_intval p(5,6,7,9) eval_new_int_has_wf_value_zero xa yWidth ya yv)
  qed
  done

lemma exp_negate_eq_zero:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  shows "exp[(-x) eq (const (new_int b 0))] \<ge> exp[x eq (const (new_int b 0))]"
  using assms apply auto
  subgoal premises p for m p xa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(4) by auto
    obtain xbb xv where xv: "xa = new_int xbb xv"
      using p(1,2) wf_integerstamp_eval_is_new_int xa by blast
    have "val[(-xa) eq (new_int b 0)] = val[xa eq (new_int b 0)]"
      using val_negate_eq_zero xv by auto
    then show ?thesis
      apply auto by (metis BinaryExpr bin_eval.simps(13) evalDet p(3,4,6) unfold_const xa)
  qed
  done

lemma exp_negate_eq:
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  assumes "stamp_expr y = IntegerStamp yb yl yh"
  shows "exp[(-x) eq (-y)] \<ge> exp[x eq y]"
  using assms apply auto
  subgoal premises p for m p xa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(6) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using p(8) by auto
    have rhsEval: "[m,p] \<turnstile> exp[x eq y] \<mapsto> val[xa eq ya]"
      by (smt (verit, best) bin_eval.simps(13) evalDet p(1,2,3,4,5,6,8) unfold_binary val_negate_eq
          wf_integerstamp_eval_is_new_int xa ya)
    have "val[(-xa) eq (-ya)] = val[xa eq ya]"
      using val_negate_eq by (meson p(1,2,3,4) wf_integerstamp_eval_is_new_int xa ya)
    then show ?thesis
      by (metis evalDet p(6,8) rhsEval xa ya)
  qed
  done

lemma exp_not_zero_neg_one:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  shows "exp[(\<not>x) eq (const new_int xb 0)] \<ge> exp[x eq (const new_int xb (not 0))]"
  using assms apply auto
  subgoal premises p for m p xa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(4) by auto
    obtain xv xbb where xv: "xa = new_int xbb xv"
      using p(1,2) wf_integerstamp_eval_is_new_int xa by blast
    have width: "xbb = xb"
      using p(1,2) stamp_eval_same_bits xa xv by blast
    have negEval: "[m,p] \<turnstile> exp[\<not>x] \<mapsto> val[\<not>xa]"
      by (metis evalDet p(4,5) unary_eval.simps(3) unfold_unary xa)
    have lhsEval: "[m,p] \<turnstile> exp[(\<not>x) eq (const new_int xb 0)] \<mapsto> val[(\<not>xa) eq (new_int xb 0)]"
      by (metis bin_eval.simps(13) evalDet negEval new_int_zero_is_intval p(3,4,6) unfold_binary xa
          unfold_const)
    have rhsEval: "[m,p] \<turnstile> exp[x eq (const new_int xb (not 0))] \<mapsto> val[xa eq (new_int xb (not 0))]"
      by (metis BinaryExpr ConstantExpr bin_eval.simps(13) evaltree_not_undef lhsEval xa xv width
          val_not_zero_neg_one eval_new_int_has_wf_value_all_ones)
    have evalEq: "val[(\<not>xa) eq (new_int xb 0)] = val[xa eq (new_int xb (not 0))]"
      using val_not_zero_neg_one width xv by blast
    have "[m,p] \<turnstile> exp[x eq (const (new_int xb (mask xb)))] \<mapsto> val[(\<not>xa) eq (new_int xb 0)]"
      using evalEq rhsEval by simp
    then show ?thesis
      using evalDet p(4) xa by fastforce
  qed
  done

lemma exp_not_neg_one_zero:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  shows "exp[(\<not>x) eq (const new_int xb (not 0))] \<ge> exp[x eq (const new_int xb 0)]"
  using assms apply auto
  subgoal premises p for m p xa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(4) by auto
    obtain xv xbb where xv: "xa = new_int xbb xv"
      using p(1,2) wf_integerstamp_eval_is_new_int xa by blast
    have zeroEval: "[m,p] \<turnstile> exp[const new_int xb 0] \<mapsto> val[new_int xb 0]"
      using wf_integerstamp_implies_zero_evals p(1,2,4) by blast
    have notEval: "[m,p] \<turnstile> exp[\<not>x] \<mapsto>  val[\<not>xa]"
      by (metis UnaryExpr evalDet p(4,5) unary_eval.simps(3) xa)
    have lhsEval: "[m,p] \<turnstile> exp[(\<not>x) eq (const new_int xb (not 0))] \<mapsto>
                           val[(\<not>xa) eq (new_int xb (not 0))]"
      by (metis notEval BinaryExpr ConstantExpr bin_eval.simps(13) evalDet new_int_mask p(3,4,6) xa
          neg_one.elims neg_one_value unfold_binary)
    have rhsEval: "[m,p] \<turnstile> exp[x eq (const new_int xb 0)] \<mapsto> val[xa eq (new_int xb 0)]"
      by (metis xa zeroEval BinaryExpr bin_eval.simps(13) evaltree_not_undef intval_not.simps(1) xv
          lhsEval new_int_zero_is_intval val_not_eq)
    have evalEq: "val[(\<not>xa) eq (new_int xb (not 0))] = val[xa eq (new_int xb 0)]"
      by (metis xv intval_not.simps(1) new_int_zero_is_intval val_not_eq)
    have "[m,p] \<turnstile> exp[x eq (const (new_int xb (0)))] \<mapsto> val[(\<not>xa) eq (new_int xb (mask xb))]"
      using evalEq rhsEval by auto
    then show ?thesis
      using evalDet p(4) xa by fastforce
  qed
  done

lemma exp_not_eq:
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  assumes "stamp_expr y = IntegerStamp yb yl yh"
  shows "exp[(~x) eq (~y)] \<ge> exp[x eq y]"
  using assms apply auto
  subgoal premises p for m p xa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(6) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using p(8) by auto
    obtain xbb xv where xv: "xa = new_int xbb xv"
      using wf_integerstamp_eval_is_new_int p(1,3) xa by blast
    obtain ybb yv where yv: "ya = new_int ybb yv"
      using wf_integerstamp_eval_is_new_int p(2,4) ya by blast
    have rhsEval: "[m,p] \<turnstile> exp[x eq y] \<mapsto> val[xa eq ya]"
      by (metis bin_eval.simps(13) evalDet p(5,6,8) unfold_binary val_not_eq xa xv ya yv)
    have "val[(~xa) eq (~ya)] = val[xa eq ya]"
      using val_not_eq xv yv by blast
    then show ?thesis
      by (metis evalDet p(6,8) rhsEval xa ya)
  qed
  done

text \<open>Optimisations\<close>

optimization AdditionEquality: "exp[(x + y) eq (x + z)] \<longmapsto> exp[y eq z]"
  using exp_addition_equality by presburger

optimization AdditionEquality2: "exp[(x + y) eq (z + x)] \<longmapsto> exp[y eq z]"
  by (meson dual_order.trans exp_add_commutative exp_addition_equality mono_binary)

optimization AdditionEquality3: "exp[(y + x) eq (x + z)] \<longmapsto> exp[y eq z]"
  by (meson dual_order.trans exp_add_commutative exp_addition_equality mono_binary)

optimization AdditionEquality4: "exp[(y + x) eq (z + x)] \<longmapsto> exp[y eq z]"
  by (meson dual_order.trans exp_add_commutative exp_addition_equality mono_binary)

optimization XorEquality: "exp[(x \<oplus> y) eq (x \<oplus> z)] \<longmapsto> exp[y eq z]"
  by (meson exp_xor_equality)

optimization XorEquality2: "exp[(x \<oplus> y) eq (z \<oplus> x)] \<longmapsto> exp[y eq z]"
  by (meson dual_order.trans exp_xor_commutative exp_xor_equality mono_binary)

optimization XorEquality3: "exp[(y \<oplus> x) eq (x \<oplus> z)] \<longmapsto> exp[y eq z]"
  by (meson dual_order.trans exp_xor_commutative exp_xor_equality mono_binary)

optimization XorEquality4: "exp[(y \<oplus> x) eq (z \<oplus> x)] \<longmapsto> exp[y eq z]"
  by (meson dual_order.trans exp_xor_commutative exp_xor_equality mono_binary)

optimization SubtractionEquality: "exp[(x - y) eq (x - z)] \<longmapsto> exp[y eq z]"
  using exp_subtraction_equality by blast

optimization SubtractionEqualityFlipped: "exp[(y - x) eq (z - x)] \<longmapsto> exp[y eq z]"
  using exp_subtraction_equality_swapped by blast

optimization EqualAddZero_Flipped: "exp[(x + y) eq x] \<longmapsto> exp[y eq (const (IntVal b 0))]
                                    when (wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi)"
  apply (meson less_trans_Suc size_binary_lhs size_binary_rhs_succ)
  using exp_add_zero_equality exp_eq_commutative order.trans by blast

optimization EqualXorZero_Flipped: "exp[(x \<oplus> y) eq x] \<longmapsto> exp[y eq (const (IntVal b 0))]
                                    when (wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi)"
  by (meson exp_eq_commutative exp_xor_zero_equality order.trans less_trans_Suc size_binary_lhs
      size_binary_rhs_succ)+

optimization EqualAddZero_FlippedSwapped: "exp[(x + y) eq y] \<longmapsto> exp[x eq (const (IntVal b 0))]
                                           when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  by (meson dual_order.refl exp_add_commutative exp_add_zero_equality exp_eq_commutative mono_binary
      order.trans)

optimization EqualXorZero_FlippedSwapped: "exp[(x \<oplus> y) eq y] \<longmapsto> exp[x eq (const (IntVal b 0))]
                                           when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  by (meson dual_order.trans exp_eq_commutative exp_xor_commutative mono_binary order_refl
      exp_xor_zero_equality)

optimization EqualAddZero: "exp[x eq (x + y)] \<longmapsto> exp[y eq (const (IntVal b 0))]
                            when (wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi)"
  using exp_add_zero_equality by simp

optimization EqualXorZero: "exp[x eq (x \<oplus> y)] \<longmapsto> exp[y eq (const (IntVal b 0))]
                            when (wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi)"
  using exp_xor_zero_equality by simp

optimization EqualAddZero_Swapped: "exp[y eq (x + y)] \<longmapsto> exp[x eq (const (IntVal b 0))]
                                    when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  by (meson dual_order.trans exp_add_commutative exp_add_zero_equality mono_binary order_refl)

optimization EqualXorZero_Swapped: "exp[y eq (x \<oplus> y)] \<longmapsto> exp[x eq (const (IntVal b 0))]
                                    when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  by (meson dual_order.refl dual_order.trans exp_xor_commutative exp_xor_zero_equality mono_binary)

optimization EqualSubZeroFlipped: "exp[(x - y) eq x] \<longmapsto> exp[y eq (const (IntVal b 0))]
                                   when (wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi)"
  by (meson dual_order.trans exp_eq_commutative exp_sub_zero_equality less_trans_Suc size_binary_lhs
      size_binary_rhs_succ)+

optimization EqualSubZero: "exp[x eq (x - y)] \<longmapsto> exp[y eq (const (IntVal b 0))]
                            when (wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi)"
  using exp_sub_zero_equality by simp

optimization EqualNotSelf: "exp[(~x) eq x] \<longmapsto> false
                            when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  apply (metis Suc_lessI order_less_imp_not_less size_binary_rhs size_pos)
  using exp_not_self_equality by blast

optimization EqualNotSelfCommute: "exp[x eq (~x)] \<longmapsto> false
                                   when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  using exp_eq_commutative exp_not_self_equality order.trans by blast

optimization EqualSubtraction: "exp[(x - y) eq const (IntVal b 0)] \<longmapsto> exp[x eq y]
                                when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  apply (simp add: less_Suc_eq size_bin_eq_div) using exp_equal_substraction by auto

optimization EqualXor: "exp[(x \<oplus> y) eq const (IntVal b 0)] \<longmapsto> exp[x eq y]
                        when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi)"
  apply (simp add: less_Suc_eq size_bin_eq_div) using exp_equal_xor by auto

optimization AndOrEquals1: "exp[(x & y) eq (x | y)] \<longmapsto> exp[x eq y]
                            when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                                 (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis IRBinaryOp.distinct(113,99) less_SucI less_add_Suc1 size_bin_eq_div)
  using exp_and_or_eq_64 by blast

optimization AndOrEquals2: "exp[(x & y) eq (y | x)] \<longmapsto> exp[x eq y]
                            when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                                 (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis IRBinaryOp.distinct(113,99) less_SucI less_add_Suc1 size_bin_eq_div)
  using AndOrEquals1 apply simp
  by (meson exp_and_commutative exp_eq_commutative le_expr_def mono_binary order_eq_refl)

optimization AndOrEquals3: "exp[(x | y) eq (x & y)] \<longmapsto> exp[x eq y]
                            when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                                 (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis IRBinaryOp.distinct(101,113) less_SucI less_add_Suc1 size_bin_eq_div)
  by (meson dual_order.trans exp_and_or_eq_64 exp_eq_commutative)

optimization AndOrEquals4: "exp[(x | y) eq (y & x)] \<longmapsto> exp[x eq y]
                            when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                                 (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis IRBinaryOp.distinct(101,113) less_SucI less_add_Suc1 size_bin_eq_div)
  using AndOrEquals3 apply simp by (meson exp_and_commutative le_expr_def mono_binary)

optimization XorNotFallThrough1: "exp[(x \<oplus> y) eq (\<not>x)] \<longmapsto> exp[y eq (const (new_int b (not 0)))]
                                  when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                                       (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  apply (simp add: add.commute less_Suc_eq size_binary_rhs trans_less_add2)
  using exp_xor_not_fall_through by force

optimization XorNotFallThrough2: "exp[(y \<oplus> x) eq (\<not>x)] \<longmapsto> exp[y eq (const (new_int b (not 0)))]
                                  when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                                       (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  apply (meson less_SucI size_binary_lhs trans_less_add1)
  using XorNotFallThrough1 apply simp by (meson exp_xor_commutative le_expr_def mono_binary)

optimization XorNotFallThrough3: "exp[(\<not>x) eq (x \<oplus> y)] \<longmapsto> exp[y eq (const (new_int b (not 0)))]
                                  when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                                       (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  apply (simp add: less_SucI size_binary_rhs trans_less_add2)
  using exp_xor_not_fall_through exp_eq_commutative by force

optimization XorNotFallThrough4: "exp[(\<not>x) eq (y \<oplus> x)] \<longmapsto> exp[y eq (const (new_int b (not 0)))]
                                  when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                                       (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  apply (simp add: less_SucI size_binary_lhs trans_less_add2)
  using XorNotFallThrough2 apply simp by (meson le_expr_def exp_eq_commutative)

optimization NotAbs: "exp[(~x) eq (abs(x))] \<longmapsto> false
                      when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x \<and> xb \<ge> 1)"
  using exp_not_abs by force

optimization NotAbsCommute: "exp[(abs(x)) eq (~x)] \<longmapsto> false
                             when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x \<and> xb \<ge> 1)"
  using exp_eq_commutative exp_not_abs by force

optimization NegateNotFalse: "exp[(-x) eq (~x)] \<longmapsto> false
                              when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x \<and> xb \<ge> 1)"
  using exp_negate_not_false by fastforce

optimization NegateNotFalseCommute: "exp[(~x) eq (-x)] \<longmapsto> false
                                     when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x \<and>
                                           xb \<ge> 1)"
  by (metis dual_order.trans exp_eq_commutative exp_negate_not_false numeral_1_eq_Suc_0 numerals(1))

optimization NegateSubRight: "exp[(-x) eq (y - x)] \<longmapsto> exp[y eq (const new_int yb 0)]
                              when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                                   (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  apply (simp add: less_SucI pos_add_strict size_binary_lhs size_pos)
  using exp_negate_sub_right by force

optimization NegateSubRightCommute: "exp[(y - x) eq (-x)] \<longmapsto> exp[y eq (const new_int yb 0)]
                                     when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                                          (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  apply (simp add: add.commute less_SucI pos_add_strict size_binary_lhs size_pos)
  by (metis dual_order.trans exp_eq_commutative exp_negate_sub_right new_int_zero_is_intval)

optimization NegateEqZero: "exp[(-x) eq (const (new_int b 0))] \<longmapsto> exp[x eq (const (new_int b 0))]
                            when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x)"
  using exp_negate_eq_zero by auto

optimization NegateEqZeroCommute: "exp[(const (new_int b 0)) eq (-x)] \<longmapsto>
                                   exp[x eq (const (new_int b 0))]
                                   when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x)"
  using exp_eq_commutative exp_negate_eq_zero by auto

optimization NegateEq: "exp[(-x) eq (-y)] \<longmapsto> exp[x eq y]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  apply (simp add: less_SucI size_bin_lt_sum_div) using exp_negate_eq by blast

optimization NotZeroNegOne: "exp[(\<not>x) eq (const new_int xb 0)] \<longmapsto>
                             exp[x eq (const new_int xb (not 0))]
                             when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                                  (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  using exp_not_zero_neg_one by auto

optimization NotZeroNegOneCommute: "exp[(const new_int xb 0) eq (\<not>x)] \<longmapsto>
                                    exp[x eq (const new_int xb (not 0))]
                                    when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                                         (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  using exp_not_zero_neg_one exp_eq_commutative by auto

optimization NotNegOneZero: "exp[(\<not>x) eq (const new_int xb (not 0))] \<longmapsto>
                             exp[x eq (const new_int xb 0)]
                             when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                                  (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  using exp_not_neg_one_zero by simp

optimization NotNegOneZeroCommute: "exp[(const new_int xb (not 0)) eq (\<not>x)] \<longmapsto>
                                    exp[x eq (const new_int xb 0)]
                                    when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                                         (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  using exp_not_neg_one_zero exp_eq_commutative by simp

optimization NotEq: "exp[(~x) eq (~y)] \<longmapsto> exp[x eq y]
                     when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                          (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  apply (simp add: less_SucI size_bin_lt_sum_div) using exp_not_eq by auto

optimization EqualXorOneShift_64: "exp[(x \<oplus> (const (IntVal b 1))) eq (const (IntVal b cv))] \<longmapsto>
                                   exp[x eq (const (new_int b (xor cv 1)))]
                                   when (stamp_expr x = IntegerStamp 64 lo hi \<and> wf_stamp x \<and>
                                         b = 64 \<and> IRExpr_up x = 1)"
  using stamp_mask.exp_equal_xor_one_shift_64 simple_mask.stamp_mask_axioms by simp

end (* End of IntegerEqualsPhase *)

end (* End of file *)