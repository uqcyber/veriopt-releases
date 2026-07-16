subsection \<open>IntegerBelowNode Phase\<close>

theory IntegerBelowPhase
  imports
    Common
    AddPhase
    Proofs.StampEvalThms
begin

phase IntegerBelowNode
  terminating size
begin

(* Word level proofs *)
lemma pos_signed_unsigned:
  assumes "sint (x) \<ge> 0"
  shows "sint(x) = uint(x)"
proof -
  have bitUnset: "\<not>(bit x (LENGTH('a) - Suc(0)))"
    using assms bit_last_iff by force
  then have "signed_take_bit (LENGTH('a) - Suc(0)) x = take_bit (LENGTH('a) - Suc(0)) x"
    by (simp add: signed_take_bit_eq_if_positive)
  then show ?thesis
    by (metis bitUnset bit_uint_iff unsigned_take_bit_eq drop_bit_eq_zero_iff_not_bit_last sint_uint
        signed_take_bit_eq_if_positive take_bit_eq_self_iff_drop_bit_eq_0)
qed

lemma bin_below_eq_less:
  assumes "sint (x) \<ge> 0"
  assumes "sint (y) \<ge> 0"
  shows "bin[less x y] = bin[word_sless x y]"
proof -
  have "(sint(x) < sint(y)) = (uint(x) < uint(y))"
    by (metis assms pos_signed_unsigned)
  then show ?thesis
    by (simp add: word_less_iff_unsigned word_sless_alt)
qed

lemma bin_negate_below: "x \<noteq> y \<and> \<not>(x < y) \<Longrightarrow> y < x" for x y::int64
  by auto

lemma bin_negate_less: "x \<noteq> y \<and> \<not>(x <s y) \<Longrightarrow> y <s x" for x y::int64
  by auto

lemma bin_inverse_negate_less: "x \<noteq> y \<and> (x <s y) \<Longrightarrow> \<not>(y <s x)" for x y::int64
  by auto

lemma bin_below_sub:
  fixes x y :: int64
  assumes "0 \<le>s x"
  assumes "0 \<le>s y"
  shows "x <s y \<longleftrightarrow> (x - y) <s 0"
  using assms apply transfer apply auto
  apply (smt (verit, del_insts) signed_take_bit_diff signed_take_bit_int_greater_self_iff
         signed_take_bit_int_less_exp signed_take_bit_negative_iff)
  by (smt (verit) signed_take_bit_diff signed_take_bit_int_less_exp signed_take_bit_negative_iff
      signed_take_bit_int_less_self_iff)

(* Value level proofs *)
lemma newint_intval:
  assumes "x = IntVal n v"
  assumes "take_bit_val_eq (IntVal n v)"
  shows "x = new_int n v"
  using assms by auto

lemma tb_n1:
  assumes "x = new_int n v"
  assumes "take_bit_val_eq (IntVal n v)"
  assumes "positive_intval x"
  shows "take_bit (n - 1) v = v"
proof -
  have eq: "(take_bit n v - take_bit (n - 1) v) = push_bit (n - 1) (of_bool (bit v (n - 1)))"
    using assms apply auto
    by (smt (verit) One_nat_def bit_take_bit_iff eq_iff_diff_eq_0 positive_intval.simps not_gr_zero
        less_Suc_eq less_nat_zero_code linordered_semidom_class.add_diff_inverse zero_less_diff
        plus_1_eq_Suc signed_take_bit_eq_if_positive signed_take_bit_code)
  then have "... = 0"
    using assms by fastforce
  then show ?thesis
    using assms(2) eq by force
qed

lemma pos_greater_zero:
  assumes "x = new_int n v"
  assumes "n \<le> 64"
  assumes "positive_intval x"
  shows "val[x < (IntVal n 0)] = val[false]"
  using assms val_pos_def apply (cases x; auto) by fastforce

lemma neg_less_zero:
  assumes "x = IntVal n v"
  assumes "n \<le> 64"
  assumes "\<not>positive_intval x"
  shows "val[x < (IntVal n 0)] = val[true]"
proof -
  have "sint (signed_take_bit (n - 1) v) < 0"
    using assms val_neg_def by auto
  then have "sint (signed_take_bit (n - 1) v) < sint (signed_take_bit (n - 1) 0)"
    by auto
  then show ?thesis
    using assms(1) by simp
qed

(* Should be move to Less than phase *)
lemma pos_less_neg:
  assumes "x = IntVal n vx"
  assumes "y = IntVal n vy"
  assumes "take_bit_val_eq x"
  assumes "n \<le> 64"
  assumes "positive_intval x"
  assumes "\<not>positive_intval y"
  shows "val[x < y] = val[false]"
proof -
  have "val[y < IntVal n 0] = val[true]"
    using assms(2,4,6) by (meson neg_less_zero intval_bits_in_bounds.simps(1))
  then have sint1: "sint (signed_take_bit (n - 1) vy) < sint (signed_take_bit (n - 1) 0)"
    using assms(2,6) val_neg_def by fastforce
  have "val[x < IntVal n 0] = val[false]"
    by (metis assms(1,3,4,5) newint_intval pos_greater_zero)
  then have sint2: "sint (signed_take_bit (n - 1) 0) \<le> sint (signed_take_bit (n - 1) vx)"
    using assms(1,2,3,4,5) val_pos_def by auto
  have "sint (signed_take_bit (n - 1) vy) < sint (signed_take_bit (n - 1) vx)"
    using sint1 sint2 by auto
  then show ?thesis
    using assms(1,2) by simp
qed

lemma verify_isValPositive:
  assumes "x = IntVal n v"
  assumes "intval_bits_in_bounds x 2 64"
  assumes "take_bit_val_eq x"
  assumes "positive_intval x"
  shows "sint(v) \<ge> 0"
  using assms apply auto
  by (metis One_nat_def assms(3,4) new_int.simps signed_take_bit_eq_if_positive tb_n1 val_pos_def)

lemma verify_pos_val_leq64:
  assumes "x = IntVal n v"
  assumes "n \<le> 64"
  assumes "take_bit_val_eq x"
  assumes "positive_intval x"
  shows "sint(v) \<ge> 0"
  using assms verify_isValPositive apply auto
  by (metis assms(3,4) newint_intval numeral_1_eq_Suc_0 numerals(1) signed_take_bit_eq_if_positive
      tb_n1 val_pos_def)

(* This is here mainly so that the word level can be lifted into the value level *)
lemma prot2:
  assumes "x = IntVal n vx"
  assumes "y = IntVal n vy"
  assumes "intval_bits_in_bounds x 2 64"
  assumes "take_bit_val_eq x"
  assumes "intval_bits_in_bounds y 2 64"
  assumes "take_bit_val_eq y"
  assumes "positive_intval x"
  assumes "positive_intval y"
  shows "(vx - vy) <s 0 \<longleftrightarrow> signed_take_bit (n - 1) (take_bit n (vx - vy)) <s 0"
  using assms apply auto
  sorry

lemma below_sub_inv:
  assumes "y = IntVal n vy"
  assumes "z = IntVal n vz"
  assumes "positive_intval y"
  assumes "positive_intval z"
  assumes "intval_bits_in_bounds y 2 64"
  assumes "take_bit_val_eq y"
  assumes "take_bit_val_eq z"
  assumes "val_to_bool val[y |<| z]"
  shows "\<not>positive_intval val[y - z]"
proof -
  have zBounds: "intval_bits_in_bounds z 2 64"
    using assms(1,2,5) by auto
  have yPos: "0 \<le>s vy"
    by (metis assms(1,3,5,6) signed_0 verify_isValPositive word_sle_eq)
  have subUnfold: "val[y - z] = IntVal n (take_bit n (vy - vz))"
    by (simp add: assms(1,2))
  have "vy < vz"
    using assms(1,2,8) val_to_bool.elims(2) by fastforce
  then have "vy <s vz"
    using assms bin_below_eq_less verify_isValPositive zBounds by blast
  then have "signed_take_bit (n - 1) (take_bit n (vy - vz)) <s 0"
    using assms(1,2,3,4,5,6,7,8)
    by (meson bin_below_sub prot2 signed.dual_order.strict_trans2 width_eq_implies_bitbounds_eq yPos
        word_sless_eq)
  then have "\<not>(0 \<le> sint(signed_take_bit (n - 1) (take_bit n (vy - vz))))"
    by (simp add: word_sless_alt)
  then show ?thesis
    using subUnfold val_pos_def assms(1,5) by force
qed

lemma below_sub:
  assumes "y = IntVal n vy"
  assumes "z = IntVal n vz"
  assumes "positive_intval y"
  assumes "positive_intval z"
  assumes "intval_bits_in_bounds y 2 64"
  assumes "take_bit_val_eq y"
  assumes "take_bit_val_eq z"
  assumes "\<not>val_to_bool val[y |<| z]"
  shows "positive_intval val[y - z]"
proof (cases "y = z")
  case True
  then have "val[y - z] = IntVal n 0"
    using assms(1,2) by simp
  then show ?thesis
    by force
next
  case False
  have notEq: "vz \<noteq> vy"
    using False assms(1,2) by auto
  then have geq: "\<not>(vy < vz)"
    using False assms by auto
  have zBounds: "intval_bits_in_bounds z 2 64"
    using assms(1,2,5) by auto
  moreover have vPos: "sint(vz) \<ge> 0"
    using assms verify_isValPositive zBounds by presburger
  ultimately have "vz <s vy"
    by (metis geq assms(1,3,5,6) bin_below_eq_less bin_negate_less notEq verify_isValPositive)
  then have subNotNeg: "\<not>((vy - vz) <s 0)"
    by (metis (no_types, opaque_lifting) bin_below_sub order.strict_trans2 order_less_imp_not_eq2
        signed.less_trans signed.not_le signed_0 vPos word_sless_alt)
  have subUnfold: "val[y - z] = IntVal n (take_bit n (vy - vz))"
    by (simp add: assms(1,2))
  have "\<not>(signed_take_bit (n - 1) (take_bit n (vy - vz)) <s 0)"
    using assms prot2 subNotNeg zBounds by blast
  then have "0 \<le> sint(signed_take_bit (n - 1) (take_bit n (vy - vz)))"
    by (simp add: word_sless_alt)
  then show ?thesis
    using subUnfold val_pos_bit assms(1,5) by auto
qed

lemma val_below_eq_less_self:
  assumes "x = IntVal n vx"
  shows "val[x |<| x] = val[x < x]"
  by (simp add: assms(1))

lemma val_below_eq_less:
  assumes "x = IntVal n vx"
  assumes "y = IntVal n vy"
  assumes "n \<le> 64"
  assumes "take_bit_val_eq x"
  assumes "take_bit_val_eq y"
  assumes "positive_intval x"
  assumes "positive_intval y"
  shows "val[x |<| y] = val[x < y]"
  using assms apply (cases x; cases y; auto)
  by (smt (verit) assms(4,5,6,7) bin_below_eq_less new_int.elims numerals(1) numeral_1_eq_Suc_0
      signed_take_bit_eq_if_positive tb_n1 verify_pos_val_leq64 word_sless_alt)

lemma below_zero: 
  shows "val[(new_int b v) |<| (new_int b 0)] = val[false]"
  by auto

lemma val_below_less:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "z = new_int n vz"
  assumes "intval_bits_in_bounds x 2 64"
  assumes "take_bit_val_eq x"
  assumes "take_bit_val_eq y"
  assumes "take_bit_val_eq z"
  assumes "positive_intval x"
  assumes "positive_intval y"
  assumes "positive_intval z"
  assumes "val[y - z] \<noteq> UndefVal"
  shows "val[(x |<| ((y |<| z)? (IntVal n 0) : (y - z)))] = val[x < (y - z)]"
proof (cases "val_to_bool val[y |<| z]")
  case True
  then have "\<not>positive_intval val[y - z]"
    by (metis assms(1,2,3,4,6,7,9,10) below_sub_inv intval_bits_in_bounds.simps(1) new_int.simps)
  then have "val[x < (y - z)] = val[false]"
    using assms pos_less_neg by simp
  then show ?thesis
    by (simp add: True assms(1))
next
  case False
  then have yzPos: "positive_intval val[y - z]"
    by (metis assms(1,10,2,3,4,6,7,9) below_sub new_int.elims width_eq_implies_bitbounds_eq)
  obtain vyz where yz: "val[y - z] = new_int n vyz"
    using assms(2,3) by auto
  then show ?thesis
    using False assms(1,8,4,5) val_below_eq_less yzPos by auto
qed

(* Exp level proofs *)
lemma exp_below_less:
  assumes "is_stamp_positive (stamp_expr x)"
  assumes "is_stamp_positive (stamp_expr y)"
  assumes "is_stamp_positive (stamp_expr z)"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  assumes "wf_stamp z"
  assumes "width_in_bounds (stamp_expr x) 2 64"
  assumes "width_in_bounds (stamp_expr y) 2 64"
  assumes "width_in_bounds (stamp_expr z) 2 64"
  assumes "stamp_expr y = IntegerStamp b lo hi"
  shows "exp[x |<| ((y |<| z)? const (IntVal b 0) : (y - z))] \<ge> exp[x < (y - z)]"
  apply auto
  subgoal premises p for m p xa cond ya za yaa zaa
  proof -
    have xa: "[m,p] \<turnstile> x \<mapsto> xa"
      by (simp add: p(1))
    have ya: "[m,p] \<turnstile> y \<mapsto> ya"
      by (simp add: p(7))
    have za: "[m,p] \<turnstile> z \<mapsto> za"
      by (simp add: p(8))
    have cond: "[m,p] \<turnstile> (if (val_to_bool val[ya |<| za])
                         then exp[const (IntVal b 0)] else exp[y - z]) \<mapsto> cond"
      by (simp add: p(4))
    have sub: "[m,p] \<turnstile> exp[y - z] \<mapsto> val[ya - za]"
      by (metis BinaryExpr bin_eval.simps(2) evalDet p(10,6,9) ya za)
    have xaPos: "positive_intval xa"
      using pos_stamp_eval_is_pos_intval assms(1,4,7) xa by auto
    have yaPos: "positive_intval ya"
      using pos_stamp_eval_is_pos_intval assms(2,5,8) ya by blast
    have zaPos: "positive_intval za"
      using pos_stamp_eval_is_pos_intval assms(3,6,9) za by blast
    have lhsDef: "val[xa |<| cond] \<noteq> UndefVal"
      using xa evalDet p(1,2) by blast
    obtain cb cv where cv: "cond = IntVal cb cv"
      by (metis Value.collapse(1) bin_eval.simps(15) defined_eval_is_intval lhsDef)
    obtain xb xv where xv: "xa = IntVal xb xv"
      by (metis ExpIntBecomesIntVal assms(1,4) is_stamp_positive.elims(2) wf_stamp_def xa)
    obtain yb yv where yv: "ya = IntVal yb yv"
      by (metis assms(10,5) valid_int wf_stamp_def ya)
    obtain zb zv where zv: "za = IntVal zb zv"
      by (metis ExpIntBecomesIntVal assms(3,6) is_stamp_positive.elims(2) wf_stamp_def za)
    have xcWidth: "xb = cb"
      by (metis cv bool_to_val_bin.simps intval_below.simps(1) lhsDef xv)
    have yzWidth: "yb = zb"
      using bool_to_val_bin.simps yv zv intval_below.simps(1) p(3) by presburger
    have sub_iv: "val[ya - za] = new_int b (yv - zv)"
      by (metis assms(10,5) intval_sub.simps(1) new_int_bin.simps valid_int_same_bits wf_stamp_def
          yv ya zv yzWidth)
    then obtain vdiff where xysub: "val[ya - za] = IntVal b vdiff"
      by simp
    have width: "xb = b"
      by (smt (verit, best) Value.inject(1) evalDet unfold_const cond sub xcWidth xysub cv)
    then have rhsDef: "val[xa < (ya - za)] \<noteq> UndefVal"
      using bool_to_val.elims xv xysub by auto
    then have wf_rhs: "[m,p] \<turnstile> exp[x < (y - z)] \<mapsto> val[xa < (ya - za)]"
      by (metis BinaryExpr bin_eval.simps(14) p(1) sub)
    have integerstamp: "is_IntegerStamp (stamp_expr x) \<and> is_IntegerStamp (stamp_expr z) \<and>
                        is_IntegerStamp (stamp_expr y)"
      using stamp_pos_neg_implies_integerstamp by (simp add: assms(1,2,3))
    have "[m,p] \<turnstile> exp[x < (y - z)] \<mapsto> val[xa |<| cond]"
    proof (cases "val_to_bool val[ya |<| za]")
      case True
      have subBitEq: "take_bit_val_eq val[ya - za]"
        using sub_iv by auto
      then have geq: "val[xa < (ya - za)] = val[false]"
        using assms apply simp
        by (metis True below_sub_inv bit_bound_maintained eval_int_implies_take_bit_eq yzWidth yv za
            intval_bits_in_bounds.simps(1) pos_less_neg width xa xaPos xv xysub ya yaPos zaPos zv)
      then show ?thesis
        using True cond unfold_const wf_rhs width xv by auto
    next
      case False
      then have subPos: "positive_intval val[ya - za]"
        by (metis stamp_width_eval_is_eq_intval xysub zv yzWidth za pos_stamp_eval_is_pos_intval ya
            assms(2,3,5,6,8,9) below_sub yv)
      then have "val[xa |<| (ya - za)] = val[xa < (ya - za)]"
        by (smt (verit, ccfv_threshold) False bit_bound_maintained evalDet eval_unused_bits_zero xv
            intval_bits_in_bounds.simps p(1) subPos take_bit_val_eq.simps(1) cond sub wf_rhs xaPos
            assms xcWidth val_below_eq_less cv)
      then show ?thesis
        by (metis (full_types) False evalDet cond wf_rhs sub)
    qed
    then show ?thesis
      by auto
  qed
  done

lemma exp_below_less_equiv:
  assumes "is_stamp_positive (stamp_expr z)"
  assumes "wf_stamp y"
  assumes "wf_stamp z"
  shows "exp[x |<| ((y |<| z)? const (IntVal b 0) : (y + (-z)))] \<ge>
         exp[x |<| ((y |<| z)? const (IntVal b 0) : (y - z))]"
  by (meson assms exp_add_right_negate_to_sub is_stamp_positive.elims(2) mono_conditional order_refl
      mono_binary)

lemma exp_below_less_add:
  assumes "is_stamp_positive (stamp_expr x)"
  assumes "is_stamp_positive (stamp_expr y)"
  assumes "is_stamp_positive (stamp_expr z)"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  assumes "wf_stamp z"
  assumes "width_in_bounds (stamp_expr x) 2 64"
  assumes "width_in_bounds (stamp_expr y) 2 64"
  assumes "width_in_bounds (stamp_expr z) 2 64"
  assumes "stamp_expr y = IntegerStamp b lo hi"
  shows "exp[(x |<| ((y |<| z)? const (IntVal b 0) : (y + (-z))))] \<ge> exp[x < (y - z)]"
proof -
  have ltSub: "exp[x |<| ((y |<| z)? const (IntVal b 0) : (y + (-z)))] \<ge>
               exp[x |<| ((y |<| z)? const (IntVal b 0) : (y - z))]"
    by (meson assms(3,5,6) exp_add_right_negate_to_sub is_stamp_positive.elims(2) mono_binary
        mono_conditional order_refl)
  have "exp[x |<| ((y |<| z)? const (IntVal b 0) : (y - z))] \<ge> exp[x < (y - z)]"
    using assms exp_below_less by blast
  then show ?thesis
    using dual_order.trans ltSub by blast
qed

text \<open>Optimisations\<close>

(* x |<| (n |<| c ? 0 : n + (-c)) \<mapsto> (x < n - c) *)
optimization BelowLess: "(x |<| ((y |<| z) ? const (IntVal b 0) : (y + (-z)))) \<longmapsto> x < (y - z)
 when ((is_stamp_positive (stamp_expr x)) \<and> (wf_stamp x) \<and> (width_in_bounds (stamp_expr x) 2 64) \<and>
       (is_stamp_positive (stamp_expr y)) \<and> (wf_stamp y) \<and> (width_in_bounds (stamp_expr y) 2 64) \<and>
       (is_stamp_positive (stamp_expr z)) \<and> (wf_stamp z) \<and> (width_in_bounds (stamp_expr z) 2 64) \<and>
        stamp_expr y = IntegerStamp b lo hi)"
  apply (metis (mono_tags, lifting) add_strict_increasing bin_cycles.simps(15,4) zero_less_numeral
         size_bin_eq_cycles_eq_iff le_add1)
  using exp_below_less_add by blast

end (* End of IntegerBelowPhase *)

end (* End of file *)