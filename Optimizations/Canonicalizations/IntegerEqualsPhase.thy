subsection \<open>IntegerEqualsNode Phase\<close>

theory IntegerEqualsPhase
  imports 
    Common 
    Proofs.StampEvalThms
begin

phase IntegerEqualsNode
  terminating size
begin

(* Helpers *)
lemma val_and_commute:
  assumes "x \<noteq> UndefVal"
  assumes "y \<noteq> UndefVal"
  shows "val[x & y] = val[y & x]"
  using assms apply (cases x; cases y; auto) by (simp add: word_bw_comms(1))

lemma exp_and_commute:
  shows "exp[x & y] \<ge> exp[y & x]"
  apply auto by (simp add: BinaryExpr evaltree_not_undef val_and_commute)

lemma val_or_commute:
  assumes "x \<noteq> UndefVal"
  assumes "y \<noteq> UndefVal"
  shows "val[x | y] = val[y | x]"
  using assms apply (cases x; cases y; auto) by (simp add: or.commute)

lemma exp_or_commute:
  shows "exp[x | y] \<ge> exp[y | x]"
  apply auto by (simp add: BinaryExpr evaltree_not_undef val_or_commute)

lemma val_equals_commute:
  assumes "x \<noteq> UndefVal"
  assumes "y \<noteq> UndefVal"
  shows "val[x eq y] = val[y eq x]"
  using assms apply (cases x; cases y; auto) by (smt (verit, best))

lemma exp_equals_commute:
  shows "exp[x eq y] \<ge> exp[y eq x]"
  apply auto by (simp add: BinaryExpr evaltree_not_undef val_equals_commute)

lemma val_xor_commute:
  assumes "x \<noteq> UndefVal"
  assumes "y \<noteq> UndefVal"
  shows "val[x \<oplus> y] = val[y \<oplus> x]"
  using assms apply (cases x; cases y; auto) by (simp add: word_bw_comms(3))

lemma exp_xor_commute:
  shows "exp[x \<oplus> y] \<ge> exp[y \<oplus> x]"
  apply auto by (simp add: BinaryExpr evaltree_not_undef val_xor_commute)

(* Word level *)

lemma bin_add_commutative: "(x+y) = (y+x)" for x y z::int64
  by simp

lemma bin_xor_commutative: "(xor x y) = (xor y x)" for x y::int64
  by (simp add: word_bw_comms(3))

lemma bin_addition_equality: "((x+y) = (x+z)) \<longleftrightarrow> (y = z)" for x y z::int64
  by simp

lemma bin_xor_equality: "((xor x y) = (xor x z)) \<longleftrightarrow> (y = z)" for x y z::int64
  by (metis bit.xor_left_self) 

lemma bin_subtraction_equality: "((x-y) = (x-z)) \<longleftrightarrow> (y = z)" for x y z::int64
  by auto

lemma bin_subtraction_equality_swapped: "((y-x) = (z-x)) \<longleftrightarrow> (y = z)" for x y z::int64
  by auto

lemma bin_add_zero_equality: "(x = (x + y)) \<longleftrightarrow> y = 0" for x y::int64
  by simp

lemma bin_xor_zero_equality: "(x = (xor x y)) \<longleftrightarrow> y = 0" for x y::int64
  by (metis bin_xor_equality xor.right_neutral)

lemma bin_sub_zero_equality: "(x = (x-y)) \<longleftrightarrow> y = 0" for x y::int64
  by simp

lemma bin_not_self_equality: "(x = (not x)) \<longleftrightarrow> False" for x::int64
  by (metis bit.compl_one bit.disj_cancel_left bit.xor_cancel_right 
      disjunctive_and_not_eq_xor neg_equal_0_iff_equal word_not_dist(1) zero_neq_one)

lemma bin_equal_substraction: "(x - y) = 0 \<longleftrightarrow> x = y" for x y::int64
  by simp

(* Value level *)

lemma val_add_commutative:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "val[x + y] \<noteq> UndefVal"
  shows "val[x + y] = val[y + x]"
  by (simp add: intval_add_sym)

lemma val_xor_commutative:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "val[x \<oplus> y] \<noteq> UndefVal"
  shows "val[x \<oplus> y] = val[y \<oplus> x]"
  by (simp add: assms(1) assms(2) bin_xor_commutative)

lemma val_addition_equality: 
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "z = new_int n vz"
  assumes "val[(x + y) eq (x + z)] \<noteq> UndefVal"
  shows "val[(x + y) eq (x + z)] = val[y eq z]"
proof -
    have unfold_lhs: "val[x+z] = IntVal n (take_bit n (vx + vz))"
      by (simp add: assms(1) assms(3))
    show ?thesis
    proof (cases "val_to_bool (val[(x + y) eq (x + z)])")
      case True
      have "take_bit n (vx + vy) = take_bit n (vx + vz)" 
        using assms True apply auto
        by (metis (full_types) bool_to_val.simps(2) val_to_bool.simps(1))
      then have eq_word: "take_bit n vy = take_bit n vz"
        by (metis (no_types, opaque_lifting) ValueThms.take_bit_dist_subR add.right_neutral 
            diff_conv_add_uminus diff_diff_eq2 diff_self verit_minus_simplify(3)) 
      then show ?thesis using True
        using eq_word unfold_lhs assms(2) assms(3) by auto  
    next
      case False
      have noneq_sumword: "take_bit n (vx + vy) \<noteq> take_bit n (vx + vz)"
        using assms False by auto
      then have noneq_word:  "take_bit n vy \<noteq> take_bit n vz"
        by (metis ValueThms.take_bit_dist_addR)
      then show ?thesis using False
        by (simp add: noneq_sumword assms(1) assms(2) assms(3)) 
    qed
  qed

lemma val_xor_equality: 
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "z = new_int n vz"
  assumes "val[(x \<oplus> y) eq (x \<oplus> z)] \<noteq> UndefVal"
  shows "val[(x \<oplus> y) eq (x \<oplus> z)] = val[y eq z]"
proof -
  have unfold_llhs: "val[x \<oplus> y] = new_int n (xor vx vy)"
    by (simp add: assms(1) assms(2))
  have unfold_lrhs: "val[x \<oplus> z] = new_int n (xor vx vz)"
    by (simp add: assms(1) assms(3))
  then show ?thesis 
  proof (cases "val_to_bool val[(x \<oplus> y) eq (x \<oplus> z)]")
    case True
    have "new_int n (xor vx vy) = new_int n (xor vx vz)"
      using assms True apply auto
      using bool_to_val.elims by fastforce
    then have "new_int n vy = new_int n vz"
      using bin_xor_equality by auto
    then show ?thesis 
      using True assms by auto
  next
    case False
    have "new_int n (xor vx vy) \<noteq> new_int n (xor vx vz)"
      using assms False by auto
    then have "new_int n vy \<noteq> new_int n vz"
      by auto
    then show ?thesis 
      using False assms by (simp add: bin_xor_equality)
  qed
qed

lemma val_subtraction_equality:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "z = new_int n vz"
  assumes "val[(x - y) eq (x - z)] \<noteq> UndefVal"
  shows "val[(x - y) eq (x - z)] = val[y eq z]"
proof -
  have unfold_lhs: "val[x-z] = IntVal n (take_bit n (vx - vz))"
    by (simp add: assms(1) assms(3))
  then show ?thesis
    by (smt (verit) ValueThms.take_bit_dist_subL ValueThms.take_bit_dist_subR add_diff_cancel_left' 
        assms(1) assms(2) assms(3) bool_to_val_bin.elims diff_add_cancel intval_equals.simps(1) 
        intval_sub.simps(1) intval_word.simps new_int.elims new_int_bin.elims new_int_take_bits) 
  qed

lemma val_subtraction_equality_swapped:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "z = new_int n vz"
  assumes "val[(y - x) eq (z - x)] \<noteq> UndefVal"
  shows "val[(y - x) eq (z - x)] = val[y eq z]"
proof -
  have unfold_lrhs: "val[z-x] = IntVal n (take_bit n (vz - vx))"
    by (simp add: assms(1) assms(3))
  moreover have unfold_llhs: "val[y-x] = IntVal n (take_bit n (vy - vx))"
    by (simp add: assms(1) assms(2))
  ultimately show ?thesis
    by (smt (verit) ValueThms.take_bit_dist_addL assms(2) assms(3) diff_add_cancel 
        intval_equals.simps(1) new_int.simps)
  qed

lemma val_add_zero_equality:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "val[x eq (x + y)] \<noteq> UndefVal"
  shows "val[x eq (x + y)] = val[y eq (new_int n 0)]" 
  using assms bin_add_zero_equality apply auto
  by (smt (verit, ccfv_threshold) ValueThms.take_bit_dist_addR bin_add_zero_equality 
      minus_add_cancel take_bit_of_0)

lemma val_xor_zero_equality:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "val[x eq (x \<oplus> y)] \<noteq> UndefVal"
  shows "val[x eq (x \<oplus> y)] = val[y eq (new_int n 0)]" 
  using assms bin_xor_zero_equality by auto

lemma val_sub_zero_equality:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "val[x eq (x - y)] \<noteq> UndefVal"
  shows "val[x eq (x - y)] = val[y eq (new_int n 0)]"
proof (cases "val_to_bool val[x eq (x - y)]")
  case True
  then have "take_bit n vx = take_bit n (vx - vy)"
    using assms apply auto
    by (metis (full_types) bool_to_val.simps(2) val_to_bool.simps(1))
  moreover have "take_bit n vx = take_bit n (vx - 0)"
    by simp
  ultimately have "take_bit n (vx - vy) = take_bit n (vx - 0)"
    by metis
  then have "take_bit n vy = 0"
    by (metis (no_types, opaque_lifting) ValueThms.take_bit_dist_subR add.inverse_inverse 
        add.left_commute add.right_inverse add.right_neutral take_bit_of_0 uminus_add_conv_diff)
  then have "val_to_bool val[y eq (new_int n 0)]"
    by (simp add: assms(2))
  then show ?thesis using True apply auto
    by (simp add: \<open>take_bit (n::nat) (vy::64 word) = (0::64 word)\<close> assms(1) assms(2))
next
  case False
  have "val[x eq (x - y)] = IntVal 32 0"
    using assms False intval_equals_result by fastforce 
  then have "take_bit n vx \<noteq> take_bit n (vx - vy)"
    using assms by auto
  moreover have "take_bit n vx = take_bit n (vx - 0)"
    by simp 
  ultimately have "take_bit n vy \<noteq> 0"
    by (metis ValueThms.take_bit_dist_subR)
  then have "val[y eq (new_int n 0)] = IntVal 32 0"
    using assms(2) by auto
  then show ?thesis 
    using \<open>val[x eq (x - y)] = IntVal 32 0\<close> by auto
qed

lemma val_not_self_equality:
  assumes "x = new_int n vx"
  assumes "1 \<le> n" and "n \<le> 64"
  assumes "val[x eq (~ x)] \<noteq> UndefVal"
  shows "val[x eq (~ x)] = IntVal 32 0"
proof -
  have "take_bit n (not vx) \<noteq> take_bit n vx"
    by (metis (no_types, opaque_lifting) assms(2) bin_not_self_equality decr_eq_not_minus mask_1 
        minus_diff_eq take_bit_not_eq_mask_diff take_bit_tightened)
  then show ?thesis using assms apply auto
    by (simp add: take_bit_not_take_bit)
qed

lemma val_equal_substraction:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "1 \<le> n" and "n \<le> 64"
  assumes "val[(x-y) eq (new_int n 0)] \<noteq> UndefVal"
  shows "val[(x-y) eq (new_int n 0)] = val[x eq y]"
  using assms bin_equal_substraction apply auto
  by (smt (verit, del_insts) ValueThms.take_bit_dist_subR bin_equal_substraction diff_0
      diff_right_commute minus_diff_eq take_bit_of_0)

(* New Optimisations - Not in Graal yet

  AndOrEquals
  (x & y) == (x | y) \<mapsto> (x == y)

  XorNotFallThrough
  (x \<oplus> y) == \<not>x \<mapsto> (y == -1)
*)

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
  using assms apply (cases x) using assms(1) prefer 2 defer
  apply simp apply simp apply simp apply simp
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
    have notEq: "val[(\<not>x) eq (abs(x))] = val[false]"
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
    have notX: "val[\<not>x] = new_int xb (not xv)"
      by (simp add: take_bit_not_take_bit xIntVal xvv)
    have unfoldBoolVal: "(take_bit xb (not xv) \<noteq> take_bit xb xv)"
      using assms(3) takeBitNot by auto
    have notEq: "val[(\<not>x) eq (abs(x))] = val[false]"
      by (simp add: absX notX unfoldBoolVal)
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

(* Expression level *)

lemma wfZero [simp]: 
  assumes "1 \<le> b"
  assumes "b \<le> 64"
  shows "wf_value (IntVal b 0)"
  unfolding wf_value_def stamp_expr.simps(3) valid_value.simps apply auto
  using assms(1) apply auto[1]
  apply (simp add: assms(2))
  by (metis ValueThms.upper_bounds_equiv assms(1) gr0I less_numeral_extra(1) 
      linorder_not_less not_exp_less_eq_0_int)

lemma exp_commutative_addition: 
  shows "exp[x + y] \<ge> exp[y + x]"
  apply auto
  subgoal premises prems for m p xa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(1) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using prems(2) by auto
    have "val[xa + ya] \<noteq> UndefVal"
      by (metis evalDet prems(1) prems(2) prems(3) xa ya)
    have "[m,p] \<turnstile> exp[y + x] \<mapsto> val[xa + ya]"
      using \<open>intval_add (xa::Value) (ya::Value) \<noteq> UndefVal\<close> intval_add_sym xa ya by auto
    then show ?thesis
      by (metis evalDet prems(1) prems(2) xa ya) 
  qed
  done

lemma exp_commutative_xor:
  shows "exp[x \<oplus> y] \<ge> exp[y \<oplus> x]" 
  apply auto
  subgoal premises prems for m p xa ya
  proof -
    obtain xa where x: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(1) by auto
    obtain ya where y: "[m,p] \<turnstile> y \<mapsto> ya"
      using prems(2) by auto
    have "val[xa \<oplus> ya] \<noteq> UndefVal"
      by (metis evalDet prems(1) prems(2) prems(3) x y)
    moreover have "val[xa \<oplus> ya] = val[ya \<oplus> xa]"
      using val_xor_commutative
      by (smt (z3) Value.distinct(11) Value.distinct(9) Value.inject(1) bin_xor_commutative 
          evaltree_not_undef intval_xor.elims intval_xor.simps(5) intval_xor.simps(9) 
          new_int_bin.simps x y)
    ultimately have "[m,p] \<turnstile> exp[y \<oplus> x] \<mapsto> val[xa \<oplus> ya]"
      using x y by auto
    then show ?thesis
      by (metis evalDet prems(1) prems(2) x y)
  qed
  done

lemma exp_addition_equality:
  shows "exp[(x+y) eq (x+z)] \<ge> exp[(y eq z)]"
  apply auto
  subgoal premises prem for m p xa ya xb yb
  proof -
  have "val[(xa + ya) eq (xb + yb)] \<noteq> UndefVal"
    by (simp add: prem(1))
  obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
    using prem(2) by auto
  obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
    using prem(3) by auto
  have l_add: "val[xa + ya] \<noteq> UndefVal"
    by (metis evalDet prem(2) prem(3) prem(4) xa ya)
  obtain xb where xb: "[m,p] \<turnstile> x \<mapsto> xb"
    using prem(2) by auto
  obtain yb where yb: "[m,p] \<turnstile> z \<mapsto> yb"
    using prem(6) by auto
  have r_add: "val[xb + yb] \<noteq> UndefVal"
    by (metis evalDet prem(5) prem(6) prem(7) xb yb)
  have "xa = xb"
    using evalDet xa xb by auto
  obtain xn xv where o1: "xa = IntVal xn xv"
    by (metis evaltree_not_undef intval_add.simps(3) intval_add.simps(4) intval_add.simps(5) 
        intval_logic_negation.cases l_add xa)
  then have "xa = new_int xn xv"
    using eval_unused_bits_zero xa by auto
  obtain yn yv where o2: "ya = IntVal yn yv"
    by (metis evaltree_not_undef intval_add.simps(7) intval_add.simps(8) intval_add.simps(9) 
        intval_logic_negation.cases l_add ya)
  then have "ya = new_int yn yv"
    using eval_unused_bits_zero ya by auto
  obtain zn zv where o3: "yb = IntVal zn zv"
    by (metis evaltree_not_undef intval_add.simps(5) intval_add.simps(7) intval_add.simps(8) 
        intval_add_sym intval_logic_negation.cases r_add yb)
  then have "yb = new_int zn zv"
    using eval_unused_bits_zero yb by auto
  have "xn = yn" using l_add o1 o2 apply auto
    by presburger
  moreover have "xn = zn" using \<open>xa = xb\<close> r_add o1 o3 apply auto
    by presburger
  ultimately have "yn = zn" 
    by auto
  then have eq_value_level: "val[(xa + ya) eq (xb + yb)] = val[ya eq yb]" 
    using prem(1) \<open>xn=yn\<close> \<open>xa = new_int xn xv\<close> \<open>ya = new_int yn yv\<close> 
          \<open>yb = new_int zn zv\<close> \<open>xa = xb\<close> val_addition_equality
    by (metis evalDet prem(2) prem(3) prem(5) prem(6) xb ya yb)
  then have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[ya eq yb]"
    by (metis \<open>(xa::Value) = (xb::Value)\<close> bin_eval.simps(13) evalDet prem(1) prem(2) prem(3) 
        prem(5) prem(6) unfold_binary xb ya yb)
  moreover have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[(xa + ya) eq (xb + yb)]"
    by (simp add: \<open>[m,p] \<turnstile> exp[y eq z] \<mapsto> val[ya eq yb]\<close> eq_value_level)
  ultimately show ?thesis apply auto
    by (metis \<open>(xa::Value) = (xb::Value)\<close> 
        \<open>[m::nat \<Rightarrow> Value,p::Value list] \<turnstile> BinaryExpr BinIntegerEquals (y::IRExpr) (z::IRExpr) \<mapsto> intval_equals (ya::Value) (yb::Value)\<close> 
        evalDet prem(2) prem(3) prem(5) prem(6) xa ya yb)
qed
  done

lemma exp_xor_equality:
  shows "exp[(x \<oplus> y) eq (x \<oplus> z)] \<ge> exp[(y eq z)]"
  apply auto
  subgoal premises prems for m p xa ya xb yb
  proof -
    have "val[(xa \<oplus> ya) eq (xb \<oplus> yb)] \<noteq> UndefVal"
      using prems(1) by auto
    obtain xa where x: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(2) by auto
    obtain ya where y: "[m,p] \<turnstile> y \<mapsto> ya"
      using prems(3) by auto
    have "val[xa \<oplus> ya] \<noteq> UndefVal"
      by (metis evalDet prems(2) prems(3) prems(4) x y)
    obtain xb where x2: "[m,p] \<turnstile> x \<mapsto> xb"
      using prems(5) by auto
    obtain yb where y2: "[m,p] \<turnstile> z \<mapsto> yb"
      using prems(6) by auto
    have "val[xb \<oplus> yb] \<noteq> UndefVal"
      by (metis evalDet prems(5) prems(6) prems(7) x2 y2)
    have "xa = xb"
      using x x2 by (simp add: evalDet)
    obtain xn xv where xa: "xa = IntVal xn xv"
      by (metis \<open>(xa::Value) = (xb::Value)\<close> \<open>intval_xor (xb::Value) (yb::Value) \<noteq> UndefVal\<close> 
          evaltree_not_undef intval_logic_negation.cases intval_xor.simps(3) intval_xor.simps(4) 
          intval_xor.simps(5) x2)
    then have "xa = new_int xn xv"
      using eval_unused_bits_zero x by auto
    obtain yn yv where ya: "ya = IntVal yn yv"
      by (metis \<open>intval_xor (xa::Value) (ya::Value) \<noteq> UndefVal\<close> intval_logic_negation.cases 
          intval_xor.simps(6) intval_xor.simps(7) intval_xor.simps(8) intval_xor.simps(9))
    then have "ya = new_int yn yv"
      using eval_unused_bits_zero y by auto
    obtain zn zv where yb: "yb = IntVal zn zv"
      by (smt (z3) evalDet intval_equals.simps(6) intval_xor.elims prems(1) prems(6) y2)
    then have "yb = new_int zn zv"
      using eval_unused_bits_zero y2 by auto
    have "xn = yn"
      by (metis \<open>intval_xor (xa::Value) (ya::Value) \<noteq> UndefVal\<close> 
          intval_xor.simps(1) new_int_bin.elims xa ya)
    have "xn = zn"
      by (metis \<open>(xa::Value) = (xb::Value)\<close> evalDet intval_xor.simps(1) 
          new_int_bin.elims prems(5) prems(6) prems(7) x2 xa y2 yb)
    have eq_value_level: "val[(xa \<oplus> ya) eq (xb \<oplus> yb)] = val[ya eq yb]"
      using x y x2 y2 \<open>xa = xb\<close> \<open>xa = new_int xn xv\<close> \<open>ya = new_int yn yv\<close> 
        \<open>yb = new_int zn zv\<close> val_xor_equality
      by (metis \<open>(xn::nat) = (yn::nat)\<close> \<open>(xn::nat) = (zn::nat)\<close> evalDet prems(1) prems(2) prems(3) prems(5) prems(6))
    have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[ya eq yb]"
      by (metis BinaryExpr \<open>(xa::Value) = (xb::Value)\<close> \<open>intval_equals (intval_xor (xa::Value) 
          (ya::Value)) (intval_xor (xb::Value) (yb::Value)) = intval_equals ya yb\<close> 
          bin_eval.simps(13) evalDet prems(1) prems(2) prems(3) prems(5) prems(6) x2 y y2)
    then have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[(xa \<oplus> ya) eq (xb \<oplus> yb)]"
      by (simp add: eq_value_level)
    then show ?thesis
      by (metis \<open>(xa::Value) = (xb::Value)\<close> evalDet prems(2) prems(3) prems(5) prems(6) x2 y y2)
  qed
  done
  
lemma exp_subtraction_equality:
  shows "exp[(x-y) eq (x-z)] \<ge> exp[(y eq z)]"
  apply auto
  subgoal premises prem for m p xa ya xb yb
proof -
  obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
    using prem(2) by auto
  obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
    using prem(3) by auto
  have l_add: "val[xa - ya] \<noteq> UndefVal"
    by (metis evalDet prem(2) prem(3) prem(4) xa ya)
  obtain xb where xb: "[m,p] \<turnstile> x \<mapsto> xb"
    using prem(2) by auto
  obtain yb where yb: "[m,p] \<turnstile> z \<mapsto> yb"
    using prem(6) by auto
  have r_add: "val[xb - yb] \<noteq> UndefVal"
    by (metis evalDet prem(5) prem(6) prem(7) xb yb)
  have "xa = xb"
    using evalDet xa xb by auto
  obtain xn xv where o1: "xa = IntVal xn xv"
    by (metis \<open>(xa::Value) = (xb::Value)\<close> intval_is_null.cases intval_sub.simps(2) 
        intval_sub.simps(3) intval_sub.simps(4) intval_sub.simps(5) r_add)
  then have "xa = new_int xn xv"
    using eval_unused_bits_zero xa by auto
  obtain yn yv where o2: "ya = IntVal yn yv"
    by (metis intval_logic_negation.cases intval_sub.simps(6) intval_sub.simps(7) 
        intval_sub.simps(8) intval_sub.simps(9) l_add)
  then have "ya = new_int yn yv"
    using eval_unused_bits_zero ya by auto
  obtain zn zv where o3: "yb = IntVal zn zv"
    by (metis intval_logic_negation.cases intval_sub.simps(6) intval_sub.simps(7) 
        intval_sub.simps(8) intval_sub.simps(9) r_add)
  then have "yb = new_int zn zv"
    using eval_unused_bits_zero yb by auto
  have "xn = yn" using l_add o1 o2 apply auto
    by presburger
  moreover have "xn = zn" using \<open>xa = xb\<close> r_add o1 o3 apply auto
    by presburger
  ultimately have "yn = zn" 
    by auto
  then have eq_value_level: "val[(xa - ya) eq (xb - yb)] = val[ya eq yb]" 
    using prem(1) \<open>xn=yn\<close> \<open>xa = new_int xn xv\<close> \<open>ya = new_int yn yv\<close> 
          \<open>yb = new_int zn zv\<close> \<open>xa = xb\<close>
    by (metis evalDet prem(2) prem(3) prem(5) prem(6) val_subtraction_equality xb ya yb)
  then have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[ya eq yb]"
    by (metis \<open>(xa::Value) = (xb::Value)\<close> bin_eval.simps(13) evalDet prem(1) prem(2) prem(3) 
        prem(5) prem(6) unfold_binary xb ya yb)
  moreover have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[(xa - ya) eq (xb - yb)]"
    by (simp add: \<open>[m,p] \<turnstile> exp[y eq z] \<mapsto> val[ya eq yb]\<close> eq_value_level)
  ultimately show ?thesis apply auto
    by (metis \<open>(xa::Value) = (xb::Value)\<close> 
        \<open>[m::nat \<Rightarrow> Value,p::Value list] \<turnstile> BinaryExpr BinIntegerEquals (y::IRExpr) (z::IRExpr) \<mapsto> intval_equals (ya::Value) (yb::Value)\<close> 
        evalDet prem(2) prem(3) prem(5) prem(6) xa ya yb)
qed
  done

lemma exp_subtraction_equality_swapped:
  shows "exp[(y-x) eq (z-x)] \<ge> exp[(y eq z)]"
  apply auto
  subgoal premises prem for m p ya xa yb xb
proof -
  obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
    using prem(2) by auto
  obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
    using prem(3) by auto
  have l_add: "val[ya-xa] \<noteq> UndefVal"
    by (metis evalDet prem(2) prem(3) prem(4) xa ya)
  obtain xb where xb: "[m,p] \<turnstile> x \<mapsto> xb"
    using prem(6) by auto
  obtain yb where yb: "[m,p] \<turnstile> z \<mapsto> yb"
    using prem(5) by auto
  have "xa = xb"
    using evalDet xa xb by auto
  then have r_add: "val[yb - xb] \<noteq> UndefVal"
    by (metis evalDet prem(5) prem(6) prem(7) xa yb)
  obtain xn xv where o1: "xa = IntVal xn xv"
    by (metis \<open>(xa::Value) = (xb::Value)\<close> evaltree_not_undef intval_logic_negation.cases 
        intval_sub.simps(7) intval_sub.simps(8) intval_sub.simps(9) r_add xb)
  then have "xa = new_int xn xv"
    using eval_unused_bits_zero xa by auto
  obtain yn yv where o2: "ya = IntVal yn yv"
    by (metis evalDet intval_equals.simps(2) intval_is_null.elims intval_sub.simps(2) 
        intval_sub.simps(3) intval_sub.simps(4) intval_sub.simps(5) prem(1) prem(2) ya)
  then have "ya = new_int yn yv"
    using eval_unused_bits_zero ya by auto
  obtain zn zv where o3: "yb = IntVal zn zv"
    by (metis evalDet intval_logic_negation.cases intval_sub.simps(2) intval_sub.simps(3) 
        intval_sub.simps(4) intval_sub.simps(5) prem(5) prem(7) yb)
  then have "yb = new_int zn zv"
    using eval_unused_bits_zero yb by auto
  have "xn = yn" using l_add o1 o2 apply auto
    by presburger
  moreover have "xn = zn" using \<open>xa = xb\<close> r_add o1 o3 apply auto
    by presburger
  ultimately have "yn = zn" 
    by auto
  then have eq_value_level: "val[(ya - xa) eq (yb - xb)] = val[ya eq yb]" 
    using prem(1) \<open>xn=yn\<close> \<open>xa = new_int xn xv\<close> \<open>ya = new_int yn yv\<close> 
          \<open>yb = new_int zn zv\<close> \<open>xa = xb\<close>
    by (metis evalDet prem(2) prem(3) prem(5) prem(6) val_subtraction_equality_swapped xb ya yb)
  then have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[ya eq yb]"
    by (metis \<open>(xa::Value) = (xb::Value)\<close> bin_eval.simps(13) evalDet prem(1) prem(2) prem(3) 
        prem(5) prem(6) unfold_binary xb ya yb)
  moreover have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[(ya - xa) eq (yb - xb)]"
    by (simp add: \<open>[m,p] \<turnstile> exp[y eq z] \<mapsto> val[ya eq yb]\<close> eq_value_level)
  ultimately show ?thesis apply auto
    by (metis \<open>(xa::Value) = (xb::Value)\<close> 
        \<open>[m::nat \<Rightarrow> Value,p::Value list] \<turnstile> BinaryExpr BinIntegerEquals (y::IRExpr) (z::IRExpr) \<mapsto> intval_equals (ya::Value) (yb::Value)\<close> 
        evalDet prem(2) prem(3) prem(5) prem(6) xa ya yb)
qed
  done

lemma exp_add_zero_equality:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[x eq (x+y)] \<ge> exp[y eq const (IntVal b 0)]"
  apply auto
  subgoal premises prems for m p xa xaa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(1) by auto
    have "val[xa eq (xaa + ya)] \<noteq> UndefVal"
      using evalDet prems(1) prems(2) xa by blast
    have xaEq: "xa = xaa"
      using evalDet prems(3) xa by auto
    obtain ya where y: "[m,p] \<turnstile> y \<mapsto> ya"
      using prems(4) by auto
    have addNotUndef: "val[xaa + ya] \<noteq> UndefVal"
      using evalDet prems(4) prems(5) y by blast
    obtain xn xv where xaIntVal: "xa = IntVal xn xv"
      by (metis evaltree_not_undef intval_add.simps(7,8,9) intval_add_sym intval_bits.elims prems(5)
          xa xaEq)
    then have xaInt: "xa = new_int xn xv"
      using eval_unused_bits_zero xa by auto
    obtain yn yv where ya:"ya = IntVal yn yv"
      by (metis evalDet intval_add.simps(6,7,8,9) intval_logic_negation.cases prems(4,5) y)
    then have yaInt: "ya = new_int yn yv"
      using eval_unused_bits_zero y by auto
    have width: "xn = yn"
      by (metis xaEq xaIntVal ya addNotUndef intval_add.simps(1))
    have "wf_value (IntVal b 0)" 
      using wfZero assms(3) assms(4) by auto
    moreover have widthB: "yn = b"
      by (metis y ya assms(1,2) valid_int_same_bits wf_stamp_def)
    ultimately have "val[ya eq (IntVal b 0)] \<noteq> UndefVal"
      using y ya assms apply (auto)
      by (metis(full_types) Value.distinct(1) bool_to_val.simps(1,2))
    then have evalEq: "val[xa eq (xaa + ya)] = val[ya eq (new_int b 0)]"
      by (metis xaEq xaInt width yaInt widthB prems(1,2,4) xa y evalDet val_add_zero_equality)
    have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[ya eq (IntVal b 0)]"
      using \<open>intval_equals (ya::Value) (IntVal (b::nat) (0::64 word)) \<noteq> UndefVal\<close> 
            \<open>wf_value (IntVal (b::nat) (0::64 word))\<close> y by auto
    then show ?thesis
      by (metis xaEq evalEq evalDet new_int_zero_is_intval prems(1,3,4) y)
  qed
  done

lemma exp_add_zero_equality_swapped:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[y eq (x+y)] \<ge> exp[x eq const (IntVal b 0)]"
proof -
  have "exp[x+y] \<ge> exp[y+x]"
    using exp_commutative_addition assms by auto
  then have "exp[y eq (x+y)] \<ge> exp[y eq (y+x)]"
    using mono_binary by blast
  moreover have "exp[y eq (y+x)] \<ge> exp[x eq const (IntVal b 0)]"
    using exp_add_zero_equality assms(1) assms(2) assms(4) assms(3) by auto
  ultimately show ?thesis
    by auto 
qed

lemma exp_add_zero_equality_flipped:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[(x+y) eq x] \<ge> exp[y eq const (IntVal b 0)]"
proof -
  have "exp[x eq (x+y)] \<ge> exp[(x+y) eq x]"
    using exp_equals_commute by blast
  then have "exp[x eq (x+y)] \<ge> exp[y eq const (IntVal b 0)]"
    using assms(1) assms(2) assms(3) assms(4) exp_add_zero_equality by blast
  then show ?thesis
    using exp_equals_commute order.trans by blast
qed

lemma exp_add_zero_equality_flipped_swapped:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[(x+y) eq y] \<ge> exp[x eq const (IntVal b 0)]"
proof -
  have "exp[x+y] \<ge> exp[y+x]"
    using exp_commutative_addition assms by auto
  then have "exp[(x+y) eq y] \<ge> exp[(y+x) eq y]"
    using mono_binary by blast
  moreover have "exp[(y+x) eq y] \<ge> exp[x eq const (IntVal b 0)]"
    using assms(1) assms(2) assms(3) assms(4) exp_add_zero_equality_flipped by blast
  ultimately show ?thesis
    by auto 
qed

lemma exp_xor_zero_equality:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[x eq (x\<oplus>y)] \<ge> exp[y eq const (IntVal b 0)]"
  apply auto
  subgoal premises prems for m p xa xaa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(1) by auto
    have "val[xa eq (xaa \<oplus> ya)] \<noteq> UndefVal"
      using evalDet prems(1) prems(2) xa by blast
    have "xa = xaa"
      using evalDet prems(3) xa by auto
    obtain ya where y: "[m,p] \<turnstile> y \<mapsto> ya"
      using prems(4) by auto
    have "val[xaa \<oplus> ya] \<noteq> UndefVal"
      using evalDet prems(4) prems(5) y by blast
    obtain xn xv where "xa = IntVal xn xv"
      by (metis \<open>(xa::Value) = (xaa::Value)\<close> evalDet intval_equals.simps(2) intval_equals.simps(6) 
          intval_word.elims intval_xor.simps(3) intval_xor.simps(4) 
          intval_xor.simps(5) prems(1) prems(2) xa)
    then have "xa = new_int xn xv"
      using eval_unused_bits_zero xa by auto
    obtain yn yv where ya:"ya = IntVal yn yv"
      by (metis evalDet intval_logic_negation.cases intval_xor.simps(6) intval_xor.simps(7) 
          intval_xor.simps(8) intval_xor.simps(9) prems(4) prems(5) y)
    then have "ya = new_int yn yv"
      using eval_unused_bits_zero y by auto
    have "xn = yn"
      using \<open>(xa::Value) = (xaa::Value)\<close> \<open>(xa::Value) = IntVal (xn::nat) (xv::64 word)\<close> 
          \<open>(ya::Value) = IntVal (yn::nat) (yv::64 word)\<close> 
          \<open>intval_xor (xaa::Value) (ya::Value) \<noteq> UndefVal\<close> apply auto by meson
    have "wf_value (IntVal b 0)" 
      using wfZero assms(3) assms(4) by auto
    moreover have "yn = b" using calculation y ya assms
      by (metis valid_int_same_bits wf_stamp_def) 
    ultimately have "val[ya eq (IntVal b 0)] \<noteq> UndefVal"
      using y ya assms apply (auto)
      by (metis(full_types) Value.distinct(1) bool_to_val.simps(1,2))
    then have evalEq: "val[xa eq (xaa \<oplus> ya)] = val[ya eq (new_int b 0)]"
      using val_xor_zero_equality xa y
      by (metis \<open>(xa::Value) = (xaa::Value)\<close> \<open>(xa::Value) = new_int (xn::nat) (xv::64 word)\<close> 
          \<open>(xn::nat) = (yn::nat)\<close> \<open>(ya::Value) = new_int (yn::nat) (yv::64 word)\<close> 
          \<open>(yn::nat) = (b::nat)\<close> evalDet prems(1) prems(2) prems(4))
    have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[ya eq (IntVal b 0)]"
      using \<open>intval_equals (ya::Value) (IntVal (b::nat) (0::64 word)) \<noteq> UndefVal\<close> 
            \<open>wf_value (IntVal (b::nat) (0::64 word))\<close> y by auto
    then have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[xa eq (xaa \<oplus> ya)]"
      by (simp add: evalEq)
    then show ?thesis
      by (metis \<open>(xa::Value) = (xaa::Value)\<close> evalDet prems(1) prems(3) prems(4) y)
  qed
  done

lemma exp_xor_zero_equality_swapped:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[y eq (x\<oplus>y)] \<ge> exp[x eq const (IntVal b 0)]"
proof -
  have "exp[x\<oplus>y] \<ge> exp[y\<oplus>x]"
    using exp_commutative_xor assms by auto
  then have "exp[y eq (x\<oplus>y)] \<ge> exp[y eq (y\<oplus>x)]"
    using mono_binary by blast
  moreover have "exp[y eq (y\<oplus>x)] \<ge> exp[x eq const (IntVal b 0)]"
    using assms(1) assms(2) assms(3) assms(4) exp_xor_zero_equality by auto
  ultimately show ?thesis
    by auto 
qed

lemma exp_xor_zero_equality_flipped:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[(x\<oplus>y) eq x] \<ge> exp[y eq const (IntVal b 0)]"
proof -
  have "exp[x eq (x\<oplus>y)] \<ge> exp[(x\<oplus>y) eq x]"
    using exp_equals_commute by blast
  then have "exp[x eq (x\<oplus>y)] \<ge> exp[y eq const (IntVal b 0)]"
    using assms(1) assms(2) assms(3) assms(4) exp_xor_zero_equality by blast
  then show ?thesis
    using exp_equals_commute order.trans by blast
qed

lemma exp_xor_zero_equality_flipped_swapped:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[(x\<oplus>y) eq y] \<ge> exp[x eq const (IntVal b 0)]"
proof -
  have "exp[x\<oplus>y] \<ge> exp[y\<oplus>x]"
    using exp_commutative_xor assms by auto
  then have "exp[(x\<oplus>y) eq y] \<ge> exp[(y\<oplus>x) eq y]"
    using mono_binary by blast
  moreover have "exp[(y\<oplus>x) eq y] \<ge> exp[x eq const (IntVal b 0)]"
    using assms(1) assms(2) assms(3) assms(4) exp_xor_zero_equality_flipped by auto
  ultimately show ?thesis
    by auto 
qed

lemma exp_sub_zero_equality:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[x eq (x-y)] \<ge> exp[y eq const (IntVal b 0)]"
  apply auto
  subgoal premises prems for m p xa xaa ya
  proof - 
    obtain xa where x: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(1) by simp
    then have "val[xa eq (xaa - ya)] \<noteq> UndefVal"
      using evalDet prems(1) prems(2) by blast
    have "xaa = xa"
      using evalDet prems(3) x by auto
    obtain ya where y: "[m,p] \<turnstile> y \<mapsto> ya"
      using prems(4) by auto
    then have subNotUndef: "val[xaa - ya] \<noteq> UndefVal"
      using evalDet prems(4) prems(5) by blast
    obtain xn xv where xa: "xa = IntVal xn xv"
      by (metis \<open>(xaa::Value) = (xa::Value)\<close> intval_logic_negation.elims intval_sub.simps(2) 
          intval_sub.simps(3) intval_sub.simps(4) intval_sub.simps(5) prems(5))
    then have "xa = new_int xn xv"
      using eval_unused_bits_zero x by auto
    obtain yn yv where ya: "ya = IntVal yn yv"
      by (metis evalDet intval_logic_negation.cases intval_sub.simps(6) intval_sub.simps(7) 
          intval_sub.simps(8) intval_sub.simps(9) prems(4) prems(5) y)
    then have "ya = new_int yn yv"
      using eval_unused_bits_zero y by auto
    have "wf_value (IntVal b 0)"
      using wfZero assms by auto
    moreover have yBits: "yn = b"
      using calculation assms y
      by (metis valid_int_same_bits wf_stamp_def ya)
    ultimately have "val[ya eq (IntVal b 0)] \<noteq> UndefVal"
      using assms ya apply auto
      by (metis(full_types) Value.distinct(1) bool_to_val.simps(1,2))
    then have "val[xa eq (xaa - ya)] = val[ya eq (new_int b 0)]"
      by (metis \<open>xa = new_int xn xv\<close> \<open>xaa = xa\<close> \<open>(ya::Value) = new_int (yn::nat) (yv::64 word)\<close> 
          yBits subNotUndef evalDet y intval_sub.simps(1) new_int.simps new_int_bin.elims
          prems(1,2,3,4) val_sub_zero_equality)
    then have eq_value_level: "val[xa eq (xaa - ya)] = val[ya eq (new_int b 0)]"
      by auto
    have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[ya eq (IntVal b 0)]"
      using \<open>intval_equals (ya::Value) (IntVal (b::nat) (0::64 word)) \<noteq> UndefVal\<close> 
            \<open>wf_value (IntVal (b::nat) (0::64 word))\<close> y by auto
    then have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[xa eq (xaa - ya)]"
      using eq_value_level by auto
    then show ?thesis
      by (metis \<open>(xaa::Value) = (xa::Value)\<close> evalDet prems(1) prems(3) prems(4) y) 
    qed
    done

lemma exp_sub_zero_equality_flipped:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[(x-y) eq x] \<ge> exp[y eq const (IntVal b 0)]"
  using exp_equals_commute assms exp_sub_zero_equality order.trans by blast

lemma exp_not_self_equality:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[x eq (~x)] \<ge> exp[const (IntVal 32 0)]"
  apply auto
  subgoal premises prems for m p xa xaa
  proof -
    obtain xa where x: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(1) by auto
    then have "val[xa eq (~xa)] \<noteq> UndefVal"
      by (metis evalDet prems(1) prems(2) prems(3))
    have "xa = xaa"
      using evalDet prems(3) x by auto
    then have "val[~xa] \<noteq> UndefVal"
      by (simp add: prems(4))
    obtain xan xav where xa: "xa = IntVal xan xav"
      by (metis \<open>intval_not (xa::Value) \<noteq> UndefVal\<close> evaltree_not_undef intval_logic_negation.cases 
          intval_not.simps(3) intval_not.simps(4) intval_not.simps(5) x)
    then have "xa = new_int xan xav"
      using eval_unused_bits_zero x by auto
    then have "xan = b" using assms x xa
      by (metis valid_int_same_bits wf_stamp_def)
    then have eq_value_level: "val[xa eq (~xa)] = IntVal 32 0"
      using val_not_self_equality \<open>xa = new_int xan xav\<close> 
            \<open>intval_equals (xa::Value) (intval_not xa) \<noteq> UndefVal\<close> assms(3) assms(4) by auto
    have "[m,p] \<turnstile> exp[const (IntVal 32 0)] \<mapsto> (IntVal 32 0)"
      by (simp add: unfold_const)
    then have "[m,p] \<turnstile> exp[const (IntVal 32 0)] \<mapsto> val[xa eq (~xa)]"
      using eq_value_level by auto
    then show ?thesis
      by (metis \<open>(xa::Value) = (xaa::Value)\<close> evalDet prems(1) prems(3)) 
  qed
  done

lemma exp_equal_substraction:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[(x-y) eq const (IntVal b 0)] \<ge> exp[x eq y]"
  apply auto
  subgoal premises prems for m p xa ya
  proof -
    have h1: "val[(xa - ya) eq (IntVal b 0)] \<noteq> UndefVal"
      by (simp add: prems(1))
    obtain xa where x: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(2) by auto
    obtain ya where y: "[m,p] \<turnstile> y \<mapsto> ya"
      using prems(3) by auto
    have "val[xa - ya] \<noteq> UndefVal"
      by (metis evalDet prems(2) prems(3) prems(4) x y)
    have "wf_value (IntVal b 0)"
      using assms by simp
    then have "IntVal b 0 = new_int b 0"
      by simp
    obtain xn xv where xa: "xa = IntVal xn xv"
      using x assms apply auto
      by (metis valid_int wf_stamp_def)
    then have "xa = new_int xn xv"
      using eval_unused_bits_zero x by auto
    obtain yn yv where ya: "ya = IntVal yn yv"
      using xa \<open>val[xa - ya] \<noteq> UndefVal\<close>
      by (metis Value.exhaust intval_sub.simps(6) intval_sub.simps(7) 
          intval_sub.simps(8) intval_sub.simps(9))
    then have "ya = new_int yn yv"
      using eval_unused_bits_zero y by auto
    have "xn = yn"
      using xa ya \<open>val[xa - ya] \<noteq> UndefVal\<close> apply auto
      by metis
    then have "yn = b"
      using assms y apply auto
      by (metis valid_int_same_bits wf_stamp_def x xa)
    then have eq_value_level: "val[(xa - ya) eq (new_int b 0)] = val[xa eq ya]"
      using val_equal_substraction h1
            \<open>xa = new_int xn xv\<close> \<open>ya = new_int yn yv\<close> apply auto
      by (smt (z3) ValueThms.take_bit_dist_subR bin_equal_substraction diff_right_commute take_bit_of_0)
    have "[m,p] \<turnstile> exp[x eq y] \<mapsto> val[(xa - ya) eq (new_int b 0)]"
      by (metis \<open>IntVal (b::nat) (0::64 word) = new_int b (0::64 word)\<close> bin_eval.simps(13) 
          eq_value_level evalDet h1 prems(2) prems(3) unfold_binary x y)
    then show ?thesis
      by (metis \<open>IntVal (b::nat) (0::64 word) = new_int b (0::64 word)\<close> evalDet prems(2) 
          prems(3) x y) 
  qed
  done

(* New Optimisations - Not in Graal yet

  AndOrEquals
  (x & y) == (x | y) \<mapsto> (x == y)

  XorNotFallThrough
  (x \<oplus> y) == \<not>x \<mapsto> (y == -1)
*)

lemma exp_and_or_eq_64:
  assumes "stamp_expr x = IntegerStamp 64 xl xh"
  assumes "stamp_expr y = IntegerStamp 64 yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  shows "exp[(x & y) eq (x | y)] \<ge> exp[x eq y]"
  apply auto
  subgoal premises p for m p x1 y1 x2 y2
    proof -
      obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
        using p(2) by auto
      obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
        using p(3) by auto
      obtain xw where xw: "xv = IntVal 64 xw"
        by (metis assms(1,3) valid_int wf_stamp_def xv)
      have val: "val[intval_equals (xv & yv) (xv | yv) = intval_equals xv yv]"
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
      by (metis eval_bits_1_64 new_int.simps new_int_take_bits validDefIntConst wf_value_def xa)
    have rhs: "[m,p] \<turnstile> exp[y eq (const (new_int b (not 0)))] \<mapsto> val[ya eq (new_int b (not 0))]"
      by (metis (no_types, lifting) yaEval bin_eval.simps(13) val_xor_not_fall_through evalDet wfVal
          p(5,6) unfold_binary unfold_const xa xaaEquiv ya)
    have eval: "val[(xa \<oplus> ya) eq (\<not>xa)] = val[ya eq (new_int b (not 0))]"
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
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(7) by blast
    obtain xv xbb where xv: "xa = new_int xbb xv"
      using p(1,2) wf_integerstamp_eval_is_new_int xa by blast
    have width: "xbb = xb"
      using p(1,2) stamp_eval_same_bits xa xv by blast
    have rhsEval: "[m,p] \<turnstile> exp[false] \<mapsto> val[false]"
      by (simp add: false_always_evals)
    have absNotUndef: "val[abs(xa)] \<noteq> UndefVal"
      using evalDet p(7,8) xa by blast
    have evalEq: "val[(~xa) eq (abs(xa))] = val[false]"
      using absNotUndef assms(3) val_not_abs width xv by blast
    then show ?thesis
      by (metis evalDet p(5,7) rhsEval xa)
  qed
  done

lemma exp_negate_not_false:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  assumes "xb \<ge> 1"
  shows "exp[(-x) eq (~x)] \<ge> exp[false]"
  using assms apply auto
  subgoal premises p for m p xa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(7) by auto
    obtain xbb xv where xv: "xa = new_int xbb xv"
      using p(1,2) wf_integerstamp_eval_is_new_int xa by blast
    have width: "xbb = xb"
      using p(1,2) stamp_eval_same_bits xa xv by auto
    have "[m,p] \<turnstile> exp[false] \<mapsto> val[false]"
      by (simp add: false_always_evals)
    then show ?thesis
      by (metis assms(3) evalDet p(5,7) val_negate_false width xa xv)
  qed
  done

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
      using p(1) p(3) wf_integerstamp_eval_is_new_int xa by blast
    obtain yv ybb where yv: "ya = new_int ybb yv"
      using p(2) p(4) wf_integerstamp_eval_is_new_int ya by blast
    have yWidth: "ybb = yb"
      using p(2) p(4) stamp_eval_same_bits ya yv by blast
    have constEval: "[m,p] \<turnstile> exp[(const (new_int yb 0))] \<mapsto> val[(new_int yb 0)]"
      using p(2) p(4) wf_integerstamp_has_wf_value_zero yWidth ya yv by blast
    have lhsEval: "[m,p] \<turnstile> exp[(-x) eq (y - x)] \<mapsto> val[(-xa) eq (ya - xa)]"
      by (metis UnaryExpr evalDet xa ya unfold_binary bin_eval.simps(13) bin_eval.simps(2)
          p(5,6,7,8,9,10) unary_eval.simps(2))
    have lhsDef: "val[(-xa) eq (ya - xa)] \<noteq> UndefVal"
      apply auto using xa ya lhsEval by (simp add: evaltree_not_undef)
    have "val[(-xa) eq (ya - xa)] = val[(ya) eq (new_int yb 0)]"
      using lhsDef val_negate_sub_right xv yWidth yv by blast
    then show ?thesis
      by (metis (no_types, opaque_lifting) BinaryExpr bin_eval.simps(13) constEval evalDet xa ya
          new_int_zero_is_intval p(5,6,7,9))
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
    have constEval: "[m,p] \<turnstile> exp[(const (new_int b 0))] \<mapsto> val[new_int b 0]"
      by (simp add: p(6) unfold_const)
    have evalEq: "val[(-xa) eq (new_int b 0)] = val[(xa) eq (new_int b 0)]"
      using val_negate_eq_zero xv by auto
    then show ?thesis
      apply auto
      by (metis BinaryExpr bin_eval.simps(13) constEval evalDet new_int_zero_is_intval p(3,4) xa)
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
    have rhsEval: "[m,p] \<turnstile> exp[(x) eq (y)] \<mapsto> val[(xa) eq (ya)]"
      by (smt (verit, best) bin_eval.simps(13) evalDet p(1,2,3,4,5,6,8) unfold_binary val_negate_eq
          wf_integerstamp_eval_is_new_int xa ya)
    have evalEq: "val[(-xa) eq (-ya)] = val[(xa) eq (ya)]"
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
    have newIntEquiv: "new_int xb 0 = IntVal xb 0"
      by simp
    have zeroEval: "[m,p] \<turnstile> exp[(const new_int xb 0)] \<mapsto> val[new_int xb 0]"
      using p(6) by auto
    have negEval: "[m,p] \<turnstile> exp[(\<not>x)] \<mapsto> val[(\<not>xa)]"
      by (metis evalDet p(4,5) unary_eval.simps(3) unfold_unary xa)
    have lhsEval: "[m,p] \<turnstile> exp[(\<not>x) eq (const new_int xb 0)] \<mapsto> val[(\<not>xa) eq (new_int xb 0)]"
      by (metis BinaryExpr bin_eval.simps(13) evalDet negEval newIntEquiv p(3,4) xa zeroEval)
    have rhsEval: "[m,p] \<turnstile> exp[x eq (const new_int xb (not 0))] \<mapsto> val[xa eq (new_int xb (not 0))]"
      by (metis BinaryExpr ConstantExpr bin_eval.simps(13) evaltree_not_undef lhsEval p(1,2) xa xv
          val_not_zero_neg_one wf_integerstamp_has_wf_value_all_ones width)
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
    have maskDef: "(new_int xb (not 0)) = (new_int xb (mask xb))"
      by simp
    have zeroEval: "[m,p] \<turnstile> exp[(const new_int xb 0)] \<mapsto> val[new_int xb 0]"
      by (metis ConstantExpr xv p(1,2) stamp_eval_same_bits wf_integerstamp_has_wf_value_zero xa)
    have notEval: "[m,p] \<turnstile> exp[(\<not>x)] \<mapsto>  val[(\<not>xa)]"
      by (metis UnaryExpr evalDet p(4,5) unary_eval.simps(3) xa)
    have lhsEval: "[m,p] \<turnstile> exp[(\<not>x) eq (const new_int xb (not 0))] \<mapsto>
                           val[(\<not>xa) eq (new_int xb (not 0))]"
      by (metis notEval BinaryExpr ConstantExpr bin_eval.simps(13) evalDet maskDef neg_one.elims xa
          neg_one_value p(3,4,6))
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
    have evalEq: "val[(~xa) eq (~ya)] = val[(xa) eq (ya)]"
      using val_not_eq xv yv by blast
    then show ?thesis
      by (metis evalDet p(6,8) rhsEval xa ya)
  qed
  done

(* Optimizations *)

(* Auxiliary lemmas to help prove size *)
lemma canonical_size_binop_equality [simp]: "Canonicalization.size (BinaryExpr BinIntegerEquals y z)
    < Suc (Suc (Canonicalization.size (BinaryExpr op x y) + Canonicalization.size (BinaryExpr op x z)))"
  by (cases z; cases y; auto)

lemma canonical_size_binop_equality_2 [simp]: "Canonicalization.size (BinaryExpr BinIntegerEquals y z)
    < Suc (Suc (Canonicalization.size (BinaryExpr op x y) + Canonicalization.size (BinaryExpr op z x)))"
  by (cases z; cases y; cases x; auto)

lemma canonical_size_binop_equality_3 [simp]: " Canonicalization.size (BinaryExpr BinIntegerEquals y z)
    < Suc (Suc (Canonicalization.size (BinaryExpr op y x)+Canonicalization.size (BinaryExpr op x z)))"
  by (cases z; cases x; auto)

lemma canonical_size_binop_equality_4 [simp]: " Canonicalization.size (BinaryExpr BinIntegerEquals y z)
    < Suc (Suc (Canonicalization.size (BinaryExpr op y x)+Canonicalization.size (BinaryExpr op z x)))"
  by (cases z; cases x; auto)

lemma canonical_size_substraction_equality_flipped [simp]: "Canonicalization.size (BinaryExpr BinIntegerEquals y z)
    < Suc (Suc (Canonicalization.size (BinaryExpr BinSub y x)+Canonicalization.size(BinaryExpr BinSub z x)))"
  by (cases z; cases x; auto)

lemma canonical_size_binop_zero_equality_flipped [simp]: "Suc (Suc (Canonicalization.size y))
    < Canonicalization.size (BinaryExpr BinIntegerEquals (BinaryExpr op x y) x)"
  by (cases x; cases y; auto)

lemma canonical_size_binop_zero_equality_flipped_swapped [simp]: "Suc (Suc (Canonicalization.size x)) 
    < Canonicalization.size (BinaryExpr BinIntegerEquals (BinaryExpr op x y) y)"
  by (cases y; auto)

lemma canonical_size_sub_zero_equality_flipped [simp]:"Suc (Suc (Canonicalization.size y)) < Canonicalization.size
       (BinaryExpr BinIntegerEquals (BinaryExpr BinSub x y) x)"
  by (cases x; cases y; auto)

lemma canonical_size_equal_subtraction [simp]: "Canonicalization.size (BinaryExpr BinIntegerEquals x y) 
        < Suc (Suc (Canonicalization.size (BinaryExpr BinSub x y)))"
  by (cases y; auto)

text \<open>Optimisations\<close>

optimization AdditionEquality: "exp[(x+y) eq (x+z)] \<longmapsto> exp[(y eq z)]"
  using canonical_size_binop_equality apply simp
  using exp_addition_equality by (meson le_expr_def)

optimization AdditionEquality2: "exp[(x+y) eq (z+x)] \<longmapsto> exp[(y eq z)]"
  apply simp
  using exp_addition_equality exp_commutative_addition
  by (meson le_expr_def mono_binary)

optimization AdditionEquality3: "exp[(y+x) eq (x+z)] \<longmapsto> exp[(y eq z)]"
  apply simp
  using exp_addition_equality exp_commutative_addition
  by (meson le_expr_def mono_binary)

optimization AdditionEquality4: "exp[(y+x) eq (z+x)] \<longmapsto> exp[(y eq z)]"
  apply simp
  using exp_addition_equality exp_commutative_addition
  by (meson le_expr_def mono_binary)

optimization XorEquality: "exp[(x\<oplus>y) eq (x\<oplus>z)] \<longmapsto> exp[(y eq z)]"
  apply simp
  by (meson exp_xor_equality le_expr_def)

optimization XorEquality2: "exp[(x\<oplus>y) eq (z\<oplus>x)] \<longmapsto> exp[(y eq z)]"
  apply simp
  using exp_xor_equality exp_commutative_xor
  by (meson le_expr_def mono_binary)

optimization XorEquality3: "exp[(y\<oplus>x) eq (x\<oplus>z)] \<longmapsto> exp[(y eq z)]"
  apply simp
  using exp_xor_equality exp_commutative_xor
  by (meson le_expr_def mono_binary)

optimization XorEquality4: "exp[(y\<oplus>x) eq (z\<oplus>x)] \<longmapsto> exp[(y eq z)]"
  apply simp
  using exp_xor_equality exp_commutative_xor
  by (meson le_expr_def mono_binary)

optimization SubtractionEquality: "exp[(x-y) eq (x-z)] \<longmapsto> exp[(y eq z)]"
  apply simp
  using exp_subtraction_equality by (meson le_expr_def)

optimization SubtractionEqualityFlipped: "exp[(y-x) eq (z-x)] \<longmapsto> exp[(y eq z)]"
  apply simp
  using exp_subtraction_equality_swapped by (meson le_expr_def)

optimization EqualAddZero: "exp[x eq (x + y)] \<longmapsto> exp[y eq (const (IntVal b 0))] 
                 when wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  using exp_add_zero_equality by simp

optimization EqualAddZero_Swapped: "exp[y eq (x + y)] \<longmapsto> exp[x eq (const (IntVal b 0))] 
                 when wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  apply simp
  using exp_add_zero_equality_swapped by (metis One_nat_def le_expr_def)

optimization EqualAddZero_Flipped: "exp[(x + y) eq x] \<longmapsto> exp[y eq (const (IntVal b 0))] 
                 when wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  apply simp
  using exp_add_zero_equality_flipped by simp

optimization EqualAddZero_FlippedSwapped: "exp[(x + y) eq y] \<longmapsto> exp[x eq (const (IntVal b 0))] 
                 when wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  apply simp
  using exp_add_zero_equality_flipped_swapped
  by (metis One_nat_def le_expr_def)

optimization EqualXorZero: "exp[x eq (x \<oplus> y)] \<longmapsto> exp[y eq (const (IntVal b 0))] 
                 when wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  using exp_xor_zero_equality by simp

optimization EqualXorZero_Swapped: "exp[y eq (x \<oplus> y)] \<longmapsto> exp[x eq (const (IntVal b 0))] 
                 when wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  apply simp
  using exp_xor_zero_equality_swapped by (metis One_nat_def le_expr_def)

optimization EqualXorZero_Flipped: "exp[(x \<oplus> y) eq x] \<longmapsto> exp[y eq (const (IntVal b 0))] 
                  when wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  apply simp
  using exp_xor_zero_equality_flipped by simp

optimization EqualXorZero_FlippedSwapped: "exp[(x \<oplus> y) eq y] \<longmapsto> exp[x eq (const (IntVal b 0))] 
                  when wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  apply simp
  using exp_xor_zero_equality_flipped_swapped
  by (metis One_nat_def le_expr_def)

optimization EqualSubZero: "exp[x eq (x - y)] \<longmapsto> exp[y eq (const (IntVal b 0))] 
                  when wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  using exp_sub_zero_equality by simp

optimization EqualSubZeroFlipped: "exp[(x - y) eq x] \<longmapsto> exp[y eq (const (IntVal b 0))] 
                  when wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  using exp_sub_zero_equality_flipped by simp

optimization EqualNotSelf: "exp[x eq (~x)] \<longmapsto> exp[const (IntVal 32 0)] 
                  when wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  using exp_not_self_equality by force

optimization EqualSubtraction: "exp[(x-y) eq const (IntVal b 0)] \<longmapsto> exp[x eq y] 
                  when wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  apply simp
  using exp_equal_substraction by auto

(* New Optimisations - Not in Graal yet *)
optimization AndOrEquals1: "exp[(x & y) eq (x | y)] \<longmapsto> exp[x eq y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis less_SucI less_add_Suc1 size_binary_const size_non_add)
  using exp_and_or_eq_64 by blast

optimization AndOrEquals2: "exp[(x & y) eq (y | x)] \<longmapsto> exp[x eq y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis less_SucI less_add_Suc1 size_binary_const size_non_add)
  using AndOrEquals1 apply simp by (meson exp_or_commute le_expr_def mono_binary)

optimization AndOrEquals3: "exp[(x | y) eq (x & y)] \<longmapsto> exp[x eq y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis less_SucI less_add_Suc1 size_binary_const size_non_add)
  by (meson exp_equals_commute order.trans exp_and_or_eq_64)

optimization AndOrEquals4: "exp[(x | y) eq (y & x)] \<longmapsto> exp[x eq y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis less_SucI less_add_Suc1 size_binary_const size_non_add)
  using AndOrEquals3 apply simp by (meson exp_and_commute le_expr_def mono_binary)

optimization XorNotFallThrough1: "exp[(x \<oplus> y) eq (\<not>x)] \<longmapsto> exp[y eq (const (new_int b (not 0)))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  apply (simp add: less_SucI size_binary_rhs trans_less_add1)
  using exp_xor_not_fall_through by force

optimization XorNotFallThrough2: "exp[(y \<oplus> x) eq (\<not>x)] \<longmapsto> exp[y eq (const (new_int b (not 0)))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  apply (simp add: add.commute less_SucI pos_add_strict size_binary_lhs size_pos)
  using XorNotFallThrough1 apply simp by (meson exp_xor_commute le_expr_def mono_binary)

optimization XorNotFallThrough3: "exp[(\<not>x) eq (x \<oplus> y)] \<longmapsto> exp[y eq (const (new_int b (not 0)))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  apply (simp add: less_SucI size_binary_rhs trans_less_add2)
  using exp_xor_not_fall_through exp_equals_commute by force

optimization XorNotFallThrough4: "exp[(\<not>x) eq (y \<oplus> x)] \<longmapsto> exp[y eq (const (new_int b (not 0)))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  apply (simp add: less_SucI size_binary_lhs trans_less_add2)
  using XorNotFallThrough2 apply simp by (meson le_expr_def exp_equals_commute)

optimization NotAbs: "exp[(~x) eq (abs(x))] \<longmapsto> exp[false]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x \<and> xb \<ge> 1)"
  using exp_not_abs by (metis numeral_1_eq_Suc_0 numerals(1))

optimization NotAbsCommute: "exp[(abs(x)) eq (~x)] \<longmapsto> exp[false]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x \<and> xb \<ge> 1)"
  using exp_not_abs dual_order.trans exp_equals_commute by force

optimization NegateNotFalse: "exp[(-x) eq (~x)] \<longmapsto> false
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x \<and> (xb \<ge> 1))"
  using exp_negate_not_false by fastforce

optimization NegateNotFalseCommute: "exp[(~x) eq (-x)] \<longmapsto> false
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x \<and> (xb \<ge> 1))"
  using exp_negate_not_false by (metis exp_equals_commute numeral_1_eq_Suc_0 numerals(1) order.trans)

optimization NegateSubRight: "exp[(-x) eq (y - x)] \<longmapsto> exp[y eq (const new_int yb 0)]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  apply (simp add: less_SucI pos_add_strict size_binary_lhs size_pos)
  using exp_negate_sub_right by force

optimization NegateSubRightCommute: "exp[(y - x) eq (-x)] \<longmapsto> exp[y eq (const new_int yb 0)]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  apply (simp add: add.commute less_SucI pos_add_strict size_binary_lhs size_pos)
  using exp_negate_sub_right by (metis exp_equals_commute new_int_zero_is_intval order.trans)

optimization NegateEqZero: "exp[(-x) eq (const (new_int b 0))] \<longmapsto> exp[x eq (const (new_int b 0))]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x)"
  using exp_negate_eq_zero by auto

optimization NegateEqZeroCommute: "exp[(const (new_int b 0)) eq (-x)] \<longmapsto>
                                   exp[x eq (const (new_int b 0))]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x)"
  using exp_negate_eq_zero dual_order.trans exp_equals_commute new_int_zero_is_intval by auto

optimization NegateEq: "exp[(-x) eq (-y)] \<longmapsto> exp[x eq y]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  apply (metis add_2_eq_Suc' add_mono_thms_linordered_field(1) less_Suc_eq less_add_same_cancel1
               size_binary_const size_non_add size_pos)
  using exp_negate_eq by auto

optimization NotZeroNegOne: "exp[(\<not>x) eq (const new_int xb 0)] \<longmapsto>
                             exp[x eq (const new_int xb (not 0))]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  using exp_not_zero_neg_one by auto

optimization NotZeroNegOneCommute: "exp[(const new_int xb 0) eq (\<not>x)] \<longmapsto>
                                    exp[x eq (const new_int xb (not 0))]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  using exp_not_zero_neg_one exp_equals_commute by auto

optimization NotNegOneZero: "exp[(\<not>x) eq (const new_int xb (not 0))] \<longmapsto>
                             exp[x eq (const new_int xb 0)]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  using exp_not_neg_one_zero by simp

optimization NotNegOneZeroCommute: "exp[(const new_int xb (not 0)) eq (\<not>x)] \<longmapsto>
                                    exp[x eq (const new_int xb 0)]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  using exp_not_neg_one_zero exp_equals_commute by simp

optimization NotEq: "exp[(~x) eq (~y)] \<longmapsto> exp[x eq y]
                        when (stamp_expr x = IntegerStamp xb xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp yb yl yh \<and> wf_stamp y)"
  apply (metis add_2_eq_Suc' add_mono_thms_linordered_field(1) less_Suc_eq less_add_same_cancel1
         size_binary_const size_non_add size_pos)
  by (meson exp_not_eq)

end (* End of IntegerEqualsPhase *)

end (* End of file *)