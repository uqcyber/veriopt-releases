subsection \<open>Evaluation Stamp Theorems\<close>

theory StampEvalThms
  imports
    Graph.ValueThms
    Semantics.IRTreeEvalThms
begin

lemma strict_pos_implies_pos: "is_stamp_strictly_positive s \<Longrightarrow> is_stamp_positive s"
  by (metis is_stamp_positive.simps(1) is_stamp_strictly_positive.elims(2) order_less_imp_le)

lemma strict_neg_implies_neg: "is_stamp_strictly_negative s \<Longrightarrow> is_stamp_negative s"
  using is_stamp_strictly_negative.elims(2) by fastforce

lemma take_bit_eq_signed: "take_bit b v = v \<Longrightarrow> signed_take_bit b v = v"
  by (metis(full_types) eq_imp_le signed_take_bit_take_bit)

lemma unwrap_signed_take_bit:
  fixes v :: int64
  assumes "0 < b \<and> b \<le> 64"
  assumes "signed_take_bit (b - 1) v = v"
  shows "signed_take_bit 63 (Word.rep (signed_take_bit (b - Suc 0) v)) = sint v"
  using assms by (simp add: signed_def)

lemma unrestricted_new_int_always_valid [simp]:
  assumes "0 < b \<and> b \<le> 64"
  shows "valid_value (new_int b v) (unrestricted_stamp (IntegerStamp b lo hi))"
  by (simp; metis One_nat_def assms int_power_div_base int_signed_value.simps int_signed_value_range
      linorder_not_le not_exp_less_eq_0_int zero_less_numeral)

lemma unary_undef: "val = UndefVal \<Longrightarrow> unary_eval op val = UndefVal"
  by (cases op; auto)

lemma unary_obj:
  "val = ObjRef x \<Longrightarrow> (if (op = UnaryIsNull) then
                           unary_eval op val \<noteq> UndefVal else
                           unary_eval op val = UndefVal)"
  by (cases op; auto)

lemma unrestricted_stamp_valid:
  assumes "s = unrestricted_stamp (IntegerStamp b lo hi)"
  assumes "0 < b \<and> b \<le> 64"
  shows "valid_stamp s"
  using assms apply auto by (simp add: pos_imp_zdiv_pos_iff self_le_power)

lemma unrestricted_stamp_valid_value [simp]:
  assumes "result = IntVal b v"
  assumes "take_bit b v = v"
  assumes "0 < b \<and> b \<le> 64"
  shows "valid_value result (unrestricted_stamp (IntegerStamp b lo hi))"
proof -
  have "valid_stamp (unrestricted_stamp (IntegerStamp b lo hi))"
    using assms unrestricted_stamp_valid by blast
  then show ?thesis
    unfolding unrestricted_stamp.simps using assms int_signed_value_bounds valid_value.simps
    by presburger
qed

(* TODO: update to allow any bit size? 
lemma unrestricted_stamp32_always_valid [simp]:
  assumes "fst (bit_bounds bits) \<le> sint ival \<and> sint ival \<le> snd (bit_bounds bits)"
  assumes "bits = 32 \<or> bits = 16 \<or> bits = 8 \<or> bits = 1"
  assumes "result = IntVal32 ival"
  shows "valid_value result (unrestricted_stamp (IntegerStamp bits lo hi))"
  using assms valid_value.simps(1) unrestricted_stamp.simps(2) by presburger

lemma larger_stamp32_always_valid [simp]:
  assumes "valid_value result (unrestricted_stamp (IntegerStamp inBits lo hi))"
  assumes "result = IntVal32 ival"
  assumes "outBits = 32 \<or> outBits = 16 \<or> outBits = 8 \<or> outBits = 1"
  assumes "inBits \<le> outBits"
  shows "valid_value result (unrestricted_stamp (IntegerStamp outBits lo hi))"
  using assms by (smt (z3)  bit_bounds.simps diff_le_mono linorder_not_less lower_bounds_equiv not_numeral_le_zero numerals(1) power_increasing_iff prod.sel(1) prod.sel(2) unrestricted_stamp.simps(2) valid_value.simps(1))
*)

subsubsection \<open>Support Lemmas for Integer Stamps and Associated IntVal values\<close>
(* TODO: these do not use eval so could go up into a StampThms.thy? *)

text \<open>Valid int implies some useful facts.\<close>
lemma valid_int_gives:
  assumes "valid_value (IntVal b v) stamp"
  obtains lo hi
  where "stamp = IntegerStamp b lo hi \<and>
         valid_stamp (IntegerStamp b lo hi) \<and>
         take_bit b v = v \<and>
         lo \<le> int_signed_value b v \<and> int_signed_value b v \<le> hi"
  using assms apply (cases stamp; auto) by (metis that)

text \<open>And the corresponding lemma where we know the stamp rather than the value.\<close>
lemma valid_int_stamp_gives:
  assumes "valid_value v (IntegerStamp b lo hi)"
  obtains ival
  where "v = IntVal b ival \<and>
         valid_stamp (IntegerStamp b lo hi) \<and>
         take_bit b ival = ival \<and>
         lo \<le> int_signed_value b ival \<and> int_signed_value b ival \<le> hi"
  by (metis assms valid_int valid_value.simps(1))

text \<open>A valid int must have the expected number of bits.\<close>
lemma valid_int_same_bits: "valid_value (IntVal b val) (IntegerStamp bits lo hi) \<Longrightarrow> b = bits"
  by (meson valid_value.simps(1))

text \<open>A valid value means a valid stamp.\<close>
lemma valid_int_valid_stamp:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "valid_stamp (IntegerStamp bits lo hi)"
  by (metis assms valid_value.simps(1))

text \<open>A valid int means a valid non-empty stamp.\<close>
lemma valid_int_not_empty: "valid_value (IntVal b val) (IntegerStamp bits lo hi) \<Longrightarrow> lo \<le> hi"
  by (metis order.trans valid_value.simps(1))

text \<open>A valid int fits into the given number of bits (and other bits are zero).\<close>
lemma valid_int_fits: "valid_value (IntVal b v) (IntegerStamp bits lo hi) \<Longrightarrow> take_bit bits v = v"
  by (metis valid_value.simps(1))

lemma valid_int_is_zero_masked:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "and val (not (mask bits)) = 0"
  by (metis (no_types, lifting) assms bit.conj_cancel_right take_bit_eq_mask valid_int_fits
      word_bw_assocs(1) word_log_esimps(1))

text \<open>Unsigned ints have bounds $0$ up to $2^bits$.\<close>
lemma valid_int_unsigned_bounds:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "uint val < 2 ^ bits"
  by (metis assms mask_eq_iff take_bit_eq_mask valid_value.simps(1))

text \<open>Signed ints have the usual two-complement bounds.\<close>
lemma valid_int_signed_upper_bound:
  assumes "valid_value (IntVal b v) (IntegerStamp bits lo hi)"
  shows "int_signed_value bits v < 2 ^ (bits - 1)"
  using assms int_signed_value_range by blast

lemma valid_int_signed_lower_bound:
  assumes "valid_value (IntVal b v) (IntegerStamp bits lo hi)"
  shows "-(2 ^ (bits - 1)) \<le> int_signed_value bits v"
  using assms One_nat_def ValueThms.int_signed_value_range by auto

text \<open>and $bit\_bounds$ versions of the above bounds.\<close>
lemma valid_int_signed_upper_bit_bound:
  assumes "valid_value (IntVal b v) (IntegerStamp bits lo hi)"
  shows "int_signed_value bits v \<le> snd (bit_bounds bits)"
proof -
  have "b = bits"
    using assms valid_int_same_bits by blast
  then show ?thesis
    using assms by auto
qed

lemma valid_int_signed_lower_bit_bound:
  assumes "valid_value (IntVal b v) (IntegerStamp bits lo hi)"
  shows " fst (bit_bounds bits) \<le> int_signed_value bits v"
proof -
  have "b = bits"
    using assms valid_int_same_bits by blast
  then show ?thesis
    using assms by auto
qed

text \<open>Valid values satisfy their stamp bounds.\<close>

lemma valid_int_signed_range:
  assumes "valid_value (IntVal b v) (IntegerStamp bits lo hi)"
  shows "lo \<le> int_signed_value bits v \<and> int_signed_value bits v \<le> hi"
  by (metis assms valid_value.simps(1))

subsubsection \<open>Validity of all Unary Operators\<close>

text \<open>We split the validity proof for unary operators into two lemmas,
  one for normal unary operators whose output bits equals their input bits,
  and the other case for the widen and narrow operators.\<close>

lemma eval_normal_unary_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes "op \<in> normal_unary"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
proof -
  obtain b1 v1 where v1: "val = IntVal b1 v1"
    using assms by (meson is_IntVal_def unary_eval_int unary_normal_bitsize)
  then obtain b2 v2 where v2: "result = IntVal b2 v2"
    by (metis Value.collapse(1) assms(2,4) unary_eval_int)
  then obtain vtmp where vtmp: "result = new_int b2 vtmp"
    by (metis assms(2) new_int.elims unary_eval_unused_bits_zero)
  obtain b' lo' hi' where expr: "stamp_expr expr = IntegerStamp b' lo' hi'"
    by (metis assms(5) v1 valid_int_gives)
  then have "stamp_unary op (stamp_expr expr) = unrestricted_stamp
            (IntegerStamp (if op \<in> normal_unary then b' else ir_resultBits op) lo' hi')"
    using assms(3) by force
  then obtain lo2 hi2 where s: "(stamp_expr (UnaryExpr op expr)) =
                                 unrestricted_stamp (IntegerStamp b2 lo2 hi2)"
    unfolding stamp_expr.simps
    by (smt (verit) expr assms(2,3,5) unary_normal_bitsize v2 valid_int_same_bits)
  then show ?thesis
    apply auto
    by (metis s vtmp assms(1,2) eval_bits_1_64 stamp_expr.simps(1) unary_eval_bitsize v1 v2
        unrestricted_new_int_always_valid)
qed

lemma narrow_widen_output_bits:
  assumes "unary_eval op val \<noteq> UndefVal"
  assumes "op \<notin> normal_unary"
  assumes "op \<notin> boolean_unary"
  assumes "op \<notin> unary_fixed_32_ops"
  shows "0 < (ir_resultBits op) \<and> (ir_resultBits op) \<le> 64"
proof -
  consider ib ob where "op = UnaryNarrow ib ob"
         | ib ob where "op = UnarySignExtend ib ob"
         | ib ob where "op = UnaryZeroExtend ib ob"
    using IRUnaryOp.exhaust_sel assms(2,3,4) by blast
  then show ?thesis
  proof (cases)
    case 1
    then show ?thesis
      using assms intval_narrow_ok by force
  next
    case 2
    then show ?thesis
      using assms intval_sign_extend_ok by force
  next
    case 3
    then show ?thesis
      using assms intval_zero_extend_ok by force
  qed
qed

lemma eval_widen_narrow_unary_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes "op \<notin> normal_unary"
  assumes "op \<notin> boolean_unary"
  assumes "op \<notin> unary_fixed_32_ops"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
proof -
  obtain b1 v1 where v1: "val = IntVal b1 v1"
    by (metis Value.exhaust_disc insertCI is_ArrayVal_def is_IntVal_def is_ObjRef_def is_ObjStr_def
        unary_obj valid_value.simps(3,11,12) assms(2,4,6,7))
  then obtain v2 where v2: "result = new_int (ir_resultBits op) v2"
    using assms(2,3,4,5,6) unary_eval_new_int by presburger
  then obtain v3 where v3: "result = IntVal (ir_resultBits op) v3"
    by simp
  then obtain b lo2 hi2 where eval: "stamp_expr expr = IntegerStamp b lo2 hi2"
    by (metis assms(7) v1 valid_int_gives)
  then have "(stamp_expr (UnaryExpr op expr)) =
              unrestricted_stamp (IntegerStamp (ir_resultBits op) lo2 hi2)"
    using assms(3,4,5) by (cases op; auto)
  then show ?thesis
    by (metis v1 assms(1,2) eval_bits_1_64 unary_eval_bitsize unrestricted_new_int_always_valid v2
        v3)
qed

lemma eval_boolean_unary_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes "op \<in> boolean_unary"
  assumes "result \<noteq> UndefVal"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
proof -
  obtain b1 where v1: "val = ObjRef (b1)"
    by (metis singletonD unary_eval.simps(8) intval_is_null.elims assms(2,3,4))
  then have eval: "result = unary_eval op (ObjRef (b1))"
    using assms(2) by blast
  have vBounds: "result \<in> {bool_to_val True, bool_to_val False}"
    by (metis insertI1 insertI2 intval_is_null.simps(1) assms(3) singleton_iff unary_eval.simps(8)
        eval)
  then have "stamp_expr (UnaryExpr op expr) = IntegerStamp 32 0 1"
    using assms(3) by (cases op; auto)
  then show ?thesis
    using vBounds by (cases result; auto)
qed

lemma eval_fixed_unary_32_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes "op \<in> unary_fixed_32_ops"
  assumes "op \<notin> normal_unary"
  assumes "op \<notin> boolean_unary"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
  proof -
  obtain b1 v1 where v1: "val = IntVal b1 v1"
    by (metis Value.exhaust_sel insert_iff intval_bit_count.simps(3,4,5) unary_eval.simps(10)
        valid_value.simps(3) assms(2,3,5,6,7))
  then obtain v2 where v2: "result = new_int 32 v2"
    using assms(2,3,4,6) unary_eval_new_int by presburger
  then obtain b lo2 hi2 where eval: "stamp_expr expr = IntegerStamp b lo2 hi2"
    by (metis assms(7) v1 valid_int_gives)
  then have "(stamp_expr (UnaryExpr op expr)) = unrestricted_stamp (IntegerStamp 32 lo2 hi2)"
    using assms(3,5) by (cases op; auto)
  then show ?thesis
    by (metis (no_types, lifting) assms(1,2) eval_bits_1_64 new_int.simps unary_eval_bitsize v1 v2
        unrestricted_new_int_always_valid)
qed

lemma eval_unary_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
  proof (cases "op \<in> normal_unary")
    case True
    then show ?thesis
      using assms eval_normal_unary_implies_valid_value by blast
  next
    case False
    then show ?thesis
  proof (cases "op \<in> boolean_unary")
    case True
    then show ?thesis
      using assms eval_boolean_unary_implies_valid_value by blast
  next
    case False
    then show ?thesis
  proof (cases "op \<in> unary_fixed_32_ops")
    case True
    then show ?thesis
      using assms eval_fixed_unary_32_implies_valid_value by auto
  next
    case False
    then show ?thesis
      using assms
      by (meson eval_boolean_unary_implies_valid_value eval_normal_unary_implies_valid_value
          eval_widen_narrow_unary_implies_valid_value unary_ops_distinct(2))
  qed
 qed
qed

subsubsection \<open>Support Lemmas for Binary Operators\<close>

lemma binary_undef: "v1 = UndefVal \<or> v2 = UndefVal \<Longrightarrow> bin_eval op v1 v2 = UndefVal"
  by (cases op; auto)

lemma binary_obj: "v1 = ObjRef x \<or> v2 = ObjRef y \<Longrightarrow> bin_eval op v1 v2 = UndefVal"
  by (cases op; auto)

text \<open>Some lemmas about the three different output sizes for binary operators.\<close>

lemma bin_eval_bits_binary_shift_ops:
  assumes "result = bin_eval op (IntVal b1 v1) (IntVal b2 v2)"
  assumes "result \<noteq> UndefVal"
  assumes "op \<in> binary_shift_ops"
  shows "\<exists>v. result = new_int b1 v"
  using assms apply (cases op; simp) prefer 2
  apply (smt (z3) new_int.simps take_bit_eq_mask word_bw_comms(2)) by blast+

lemma bin_eval_bits_fixed_32_ops:
  assumes "result = bin_eval op (IntVal b1 v1) (IntVal b2 v2)"
  assumes "result \<noteq> UndefVal"
  assumes "op \<in> binary_fixed_32_ops"
  shows "\<exists>v. result = new_int 32 v"
  using assms apply (cases op; simp)
  apply (metis (no_types, opaque_lifting) bin_eval_unused_bits_zero bool_to_val.elims assms(1))
  prefer 5
  using IntVal1 Value.inject(1) new_int.simps take_bit_minus_one_eq_mask take_bit_of_0 assms(1)
        bin_eval_unused_bits_zero bool_to_val.elims apply (metis, metis)
  by (metis (full_types) assms(1) bin_eval_unused_bits_zero bool_to_val.simps(1,2))+

lemma bin_eval_bits_normal_ops:
  assumes "result = bin_eval op (IntVal b1 v1) (IntVal b2 v2)"
  assumes "result \<noteq> UndefVal"
  assumes "op \<notin> binary_fixed_32_ops"
  shows "\<exists>v. result = new_int b1 v"
  by (metis assms bin_eval_new_int intval_bits.simps)

lemma bin_eval_input_bits_equal:
  assumes "result = bin_eval op (IntVal b1 v1) (IntVal b2 v2)"
  assumes "result \<noteq> UndefVal"
  assumes "op \<notin> binary_shift_ops"
  shows "b1 = b2"
  using assms apply (cases op; simp) by (meson new_int_bin.simps)+

lemma bin_eval_implies_valid_value:
  assumes "[m,p] \<turnstile> expr1 \<mapsto> val1"
  assumes "[m,p] \<turnstile> expr2 \<mapsto> val2"
  assumes "result = bin_eval op val1 val2"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val1 (stamp_expr expr1)"
  assumes "valid_value val2 (stamp_expr expr2)"
  shows "valid_value result (stamp_expr (BinaryExpr op expr1 expr2))"
proof -
  obtain b1 v1 where v1: "val1 = IntVal b1 v1"
    by (metis Value.collapse(1) assms(3,4) bin_eval_inputs_are_ints bin_eval_int)
  obtain b2 v2 where v2: "val2 = IntVal b2 v2"
    by (metis Value.collapse(1) assms(3,4) bin_eval_inputs_are_ints bin_eval_int)
  then obtain lo1 hi1 where s1: "stamp_expr expr1 = IntegerStamp b1 lo1 hi1"
    by (metis assms(5) v1 valid_int_gives)
  then obtain lo2 hi2 where s2: "stamp_expr expr2 = IntegerStamp b2 lo2 hi2"
    by (metis assms(6) v2 valid_int_gives)
  then have r: "result = bin_eval op (IntVal b1 v1) (IntVal b2 v2)"
    using assms(3) v1 v2 by presburger
  then obtain bres vtmp where vtmp: "result = new_int bres vtmp"
    using assms by (meson bin_eval_new_int)
  then obtain vres where vres: "result = IntVal bres vres"
    by force
  (* now calculate the result stamp for the three classes of operators. *)
  then have sres: "stamp_expr (BinaryExpr op expr1 expr2) =
             unrestricted_stamp (IntegerStamp bres lo1 hi1)
           \<and> 0 < bres \<and> bres \<le> 64"
    proof (cases "op \<in> binary_shift_ops")
      case True
      then show ?thesis
        unfolding stamp_expr.simps
        by (metis Value.inject(1) eval_bits_1_64 new_int.simps r assms(1,4) stamp_binary.simps(1)
            bin_eval_bits_binary_shift_ops s2 s1 v1 vres)
    next
      case False
      then have beq: "b1 = b2"
        using v1 v2 assms bin_eval_input_bits_equal by blast
      then show ?thesis
      proof (cases "op \<in> binary_fixed_32_ops")
        case True
        then show ?thesis
          unfolding stamp_expr.simps
          by (metis (no_types, lifting) False Value.inject(1) beq bin_eval_new_int zero_less_numeral
              le_add_same_cancel1 new_int.simps s2 s1 numeral_Bit0 vres zero_le_numeral assms(3,4)
              stamp_binary.simps(1))
      next
        case False
        then show ?thesis
          unfolding s1 s2 stamp_binary.simps stamp_expr.simps
          by (metis assms(1,3,4) beq bin_eval_bits_normal_ops eval_bits_1_64 intval_bits.simps vres
              new_int.elims v1 v2)
      qed
    qed
  then show ?thesis
    using unrestricted_new_int_always_valid vres vtmp by presburger
qed

subsubsection \<open>Validity of Stamp Meet and Join Operators\<close>

lemma stamp_meet_integer_is_valid_stamp:
  assumes "valid_stamp stamp1"
  assumes "valid_stamp stamp2"
  assumes "is_IntegerStamp stamp1"
  assumes "is_IntegerStamp stamp2"
  shows "valid_stamp (meet stamp1 stamp2)"
proof -
  obtain b1 l1 h1 where stamp1: "stamp1 = IntegerStamp b1 l1 h1"
    using assms(3) is_IntegerStamp_def by fastforce
  obtain b2 l2 h2 where stamp2: "stamp2 = IntegerStamp b2 l2 h2"
    using assms(4) is_IntegerStamp_def by auto
  have stamp1_bounds: "fst (bit_bounds b1) \<le> l1 \<and> l1 \<le> snd (bit_bounds b1) \<and>
                       fst (bit_bounds b1) \<le> h1 \<and> h1 \<le> snd (bit_bounds b1)"
    using assms(1) stamp1 valid_stamp.simps(1) by blast
  have stamp2_bounds: "fst (bit_bounds b2) \<le> l2 \<and> l2 \<le> snd (bit_bounds b2) \<and>
                       fst (bit_bounds b2) \<le> h2 \<and> h2 \<le> snd (bit_bounds b2)"
    using assms(2) stamp2 valid_stamp.simps(1) by blast
  then show ?thesis
  proof (cases "b1 = b2")
    case True
    have "meet stamp1 stamp2 = IntegerStamp b1 (min l1 l2) (max h1 h2)"
      by (simp add: True stamp1 stamp2)
    then show ?thesis
      by (smt (verit) True assms(1) stamp1 stamp2_bounds valid_stamp.simps(1))
  next
    case False
    then show ?thesis
      using meet.simps(2) stamp1 stamp2 by simp
  qed
qed

lemma stamp_meet_is_valid_stamp:
  assumes 1: "valid_stamp stamp1"
  assumes 2: "valid_stamp stamp2"
  shows "valid_stamp (meet stamp1 stamp2)"
  by (cases stamp1; cases stamp2; insert stamp_meet_integer_is_valid_stamp[OF 1 2]; auto)

lemma stamp_meet_commutes: "meet stamp1 stamp2 = meet stamp2 stamp1"
  by (cases stamp1; cases stamp2; auto)

lemma stamp_meet_is_valid_value1:
  assumes "valid_value val stamp1" (*  \<or> valid_value val stamp2" *)
  assumes "valid_stamp stamp2"
  assumes "stamp1 = IntegerStamp b1 lo1 hi1"
  assumes "stamp2 = IntegerStamp b2 lo2 hi2"
  assumes "meet stamp1 stamp2 \<noteq> IllegalStamp"
  shows "valid_value val (meet stamp1 stamp2)"
proof -
  have m: "meet stamp1 stamp2 = IntegerStamp b1 (min lo1 lo2) (max hi1 hi2)"
    by (metis assms(3,4,5) meet.simps(2))
  obtain ival where val: "val = IntVal b1 ival"
    using assms(1,3) valid_int by blast
  then show ?thesis
    by (smt (verit) assms(1,2,3) m stamp_meet_is_valid_stamp valid_value.simps(1))
qed

text \<open>and the symmetric lemma follows by the commutativity of meet.\<close>

lemma stamp_meet_is_valid_value:
  assumes "valid_value val stamp2"
  assumes "valid_stamp stamp1"
  assumes "stamp1 = IntegerStamp b1 lo1 hi1"
  assumes "stamp2 = IntegerStamp b2 lo2 hi2"
  assumes "meet stamp1 stamp2 \<noteq> IllegalStamp"
  shows "valid_value val (meet stamp1 stamp2)"
  by (metis stamp_meet_is_valid_value1 stamp_meet_commutes assms)

subsubsection \<open>Validity of conditional expressions\<close>

lemma conditional_eval_implies_valid_value:
  assumes "[m,p] \<turnstile> cond \<mapsto> condv"
  assumes "expr = (if val_to_bool condv then expr1 else expr2)"
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "val \<noteq> UndefVal"
  assumes "valid_value condv (stamp_expr cond)"
  assumes "valid_value val (stamp_expr expr)"
  assumes "compatible (stamp_expr expr1) (stamp_expr expr2)"
  shows "valid_value val (stamp_expr (ConditionalExpr cond expr1 expr2))"
proof -
  have "meet (stamp_expr expr1) (stamp_expr expr2) \<noteq> IllegalStamp"
    using assms apply auto
    by (smt (verit, ccfv_threshold) Stamp.distinct(13,25) compatible.elims(2) meet.simps(1,2))
  then show ?thesis
    using assms apply auto
    by (smt (verit) compatible.elims(2) stamp_meet_commutes stamp_meet_is_valid_value1
        valid_value.simps(13))
qed

subsubsection \<open>Validity of Whole Expression Tree Evaluation\<close>

text \<open> TODO: find a way to encode that conditional expressions must have
  compatible (and valid) stamps?  One approach would be for all the 
  stamp\_expr operators to require that all input stamps are valid.\<close>

(*
experiment begin
lemma stamp_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  shows "valid_value val (stamp_expr expr)"
  using assms proof (induction expr val)
  case (UnaryExpr expr val result op)
  then show ?case using eval_unary_implies_valid_value by simp
  next
    case (BinaryExpr expr1 val1 expr2 val2 result op)
    then show ?case using bin_eval_implies_valid_value by simp
  next
    case (ConditionalExpr cond condv expr expr1 expr2 val)
    have "compatible (stamp_expr expr1) (stamp_expr expr2)"
      using assms sorry
    then show ?case 
      using assms conditional_eval_implies_valid_value
      using ConditionalExpr.IH(1) ConditionalExpr.IH(2) ConditionalExpr.hyps(1) ConditionalExpr.hyps(2) ConditionalExpr.hyps(3) ConditionalExpr.hyps(4) by blast
  next
    case (ParameterExpr x1 x2)
    then show ?case by auto
  next
    case (LeafExpr x1 x2)
    then show ?case by auto
  next
    case (ConstantExpr x)
    then show ?case by auto
qed

lemma value_range:
  assumes "[m, p] \<turnstile> e \<mapsto> v"
  shows "v \<in> {val . valid_value val (stamp_expr e)}"
  using assms sorry
end
*)

lemma ExpIntBecomesIntVal:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "wf_stamp x"
  assumes "valid_value v (IntegerStamp b xl xh)"
  assumes "[m,p] \<turnstile> x \<mapsto> v"
  shows "\<exists>xv. v = IntVal b xv"
  using assms by (simp add: IRTreeEvalThms.valid_value_elims(3))

lemma stamp_of_default:
  assumes "stamp_expr x = default_stamp"
  assumes "wf_stamp x"
  shows "([m, p] \<turnstile> x \<mapsto> v) \<longrightarrow> (\<exists>vv. v = IntVal 32 vv)"
  by (metis assms default_stamp valid_value_elims(3) wf_stamp_def)

lemma wf_integerstamp_eval_is_new_int:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "[m,p] \<turnstile> x \<mapsto> xa"
  shows "\<exists>b xv. xa = new_int b xv"
  by (metis assms eval_int_implies_take_bit_eq new_int.simps take_bit_val_eq.simps(1) wf_stamp_def
      valid_int)

lemma eval_new_int_has_wf_value_zero:
  assumes "[m,p] \<turnstile> x \<mapsto> xa"
  assumes "xa = new_int xb xv"
  shows "wf_value (new_int xb 0)"
  by (metis assms eval_bits_1_64 new_int.elims validIntConst wf_value_def)

lemma eval_new_int_has_wf_value_all_ones:
  assumes "[m,p] \<turnstile> x \<mapsto> xa"
  assumes "xa = new_int xb xv"
  shows "wf_value (new_int xb (not 0))"
  unfolding wf_value_def
  by (metis assms eval_bits_1_64 new_int.elims new_int_unused_bits_zero validDefIntConst)

lemma wf_integerstamp_implies_zero_evals:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  assumes "[m,p] \<turnstile> x \<mapsto> xa"
  shows "[m,p] \<turnstile> (ConstantExpr (new_int xb 0)) \<mapsto> new_int xb 0"
  using assms(1) unfolding wf_stamp_def
  by (metis assms(2,3) eval_new_int_has_wf_value_zero eval_unused_bits_zero new_int.simps valid_int
      unfold_const)

lemma wf_integerstamp_implies_nonzero_bits:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "wf_stamp x"
  assumes "[m, p] \<turnstile> x \<mapsto> v"
  shows "b \<noteq> 0"
  using assms apply auto subgoal
proof -
  have invalidStamp: "b = 0 \<Longrightarrow> \<not>(valid_stamp (stamp_expr x))"
    unfolding assms(1) using valid_stamp.simps(1) by blast
  have "\<not>(valid_stamp (stamp_expr x)) \<Longrightarrow> \<not>wf_stamp x"
    unfolding wf_stamp_def by (metis assms(1,3) valid_int valid_value.simps(1))
  then show ?thesis
    using assms(2) invalidStamp by blast
qed
  done

lemma true_always_evals: "[m,p] \<turnstile> ConstantExpr (IntVal 32 1) \<mapsto> IntVal 32 1"
  by (simp add: unfold_const wf_value_true)

lemma false_always_evals: "[m,p] \<turnstile> ConstantExpr (IntVal 32 0) \<mapsto> IntVal 32 0"
  by auto

lemma stamp_eval_same_bits:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  assumes "[m,p] \<turnstile> x \<mapsto> xa"
  assumes "xa = new_int xbb xv"
  shows "xbb = xb"
  by (metis assms new_int.elims valid_value.simps(1) wf_stamp_def)

lemma stamp_eval_int:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp xb xl xh"
  assumes "[m,p] \<turnstile> x \<mapsto> xa"
  assumes "xa = new_int xbb xv"
  shows "[m,p] \<turnstile> ConstantExpr (new_int xb v) \<mapsto> (new_int xb v)"
  using assms apply auto
  by (metis (no_types, lifting) ConstantExpr assms(4) eval_bits_1_64 stamp_eval_same_bits
      take_bit_not_iff take_bit_not_take_bit validDefIntConst wf_value_def)

lemma isNonZero_defn:
  assumes "is_stamp_strictly_positive (stamp_expr x)"
  assumes "wf_stamp x"
  shows "([m, p] \<turnstile> x \<mapsto> v) \<longrightarrow>
         (\<exists>vv b. (v = IntVal b vv \<and> val_to_bool (intval_less_than (IntVal b 0) v)))"
  apply (rule impI) subgoal premises eval
proof -
  obtain b lo hi where xstamp: "stamp_expr x = IntegerStamp b lo hi"
    by (meson is_stamp_strictly_positive.elims(2) assms)
  obtain vv where vdef: "v = IntVal b vv"
    by (metis xstamp assms(2) eval valid_int wf_stamp_def)
  then have "int_signed_value b vv > 0"
    by (metis assms dual_order.strict_trans1 eval is_stamp_strictly_positive.simps(1) wf_stamp_def
        valid_int_signed_range xstamp)
  then show ?thesis
    by (simp add: vdef)
qed
  done

lemma evalSubStamp:
  assumes "[m, p] \<turnstile> BinaryExpr BinSub x y \<mapsto> v"
  assumes "wf_stamp (BinaryExpr BinSub x y)"
  shows "\<exists>b lo hi. stamp_expr (BinaryExpr BinSub x y) = IntegerStamp b lo hi"
proof -
  have "valid_value v (stamp_expr (BinaryExpr BinSub x y))"
    using assms unfolding wf_stamp_def by auto
  then have "stamp_expr (BinaryExpr BinSub x y) \<noteq> IllegalStamp"
    by force
  then show ?thesis
    unfolding stamp_expr.simps using stamp_binary.simps(1)
    by (smt (z3) stamp_binary.simps stamp_binary.elims unrestricted_stamp.simps(2))
qed

lemma bit_bound_maintained:
  assumes "width_in_bounds (stamp_expr x) xl xh"
  assumes "wf_stamp x"
  assumes "[m,p] \<turnstile> x \<mapsto> xv"
  assumes "xv = IntVal n v"
  shows "intval_bits_in_bounds xv xl xh"
  by (metis intval_bits_in_bounds.simps(1) valid_int_same_bits wf_stamp_def width_in_bounds.elims(2)
      assms)

lemma bit_width_maintained:
  assumes "wf_stamp x"
  assumes "[m,p] \<turnstile> x \<mapsto> xv"
  assumes "xv = IntVal n v"
  shows "n = stp_bits (stamp_expr x)"
  by (metis Stamp.sel(1) assms valid_int_gives wf_stamp_def)

lemma stamp_pos_neg_implies_integerstamp:
  assumes "is_stamp_positive s          \<or> is_stamp_negative s \<or>
           is_stamp_strictly_positive s \<or> is_stamp_strictly_negative s \<or>
           can_stamp_be_positive s      \<or> can_stamp_be_negative s"
  shows "is_IntegerStamp s"
  by (metis Stamp.disc(2) assms can_stamp_be_negative.elims(2) can_stamp_be_positive.elims(2)
      is_stamp_negative.elims(2) is_stamp_positive.elims(2) strict_neg_implies_neg
      strict_pos_implies_pos)

lemma width_in_bounds_implies_integerstamp:
  assumes "width_in_bounds s l h"
  shows "is_IntegerStamp s"
  by (metis Stamp.discI(1) assms width_in_bounds.elims(2))

lemma integerstamp_implies_bounds:
  assumes "is_IntegerStamp s"
  shows "\<exists>l h. width_in_bounds s l h"
  using assms is_IntegerStamp_def by fastforce

lemma stamp_width_eval_is_eq_intval:
  assumes "width_in_bounds (stamp_expr x) l h"
  assumes "wf_stamp x"
  assumes "[m,p] \<turnstile> x \<mapsto> xv"
  shows "(is_IntVal xv) \<and> (intval_bits_in_bounds xv l h) \<and> (take_bit_val_eq xv)"
proof -
  have "is_IntegerStamp (stamp_expr x)"
    using width_in_bounds_implies_integerstamp assms(1) by auto
  then show ?thesis
    by (metis ExpIntBecomesIntVal Stamp.collapse(1) Value.disc(2) assms bit_bound_maintained
        eval_int_implies_take_bit_eq wf_stamp_def)
qed

lemma pos_stamp_eval_is_pos_intval:
  assumes "is_stamp_positive (stamp_expr x)"
  assumes "wf_stamp x"
  assumes "[m, p] \<turnstile> x \<mapsto> xv"
  shows "positive_intval xv"
proof -
  obtain xb xvv where xv: "xv = IntVal xb xvv"
    by (metis ExpIntBecomesIntVal assms is_stamp_positive.elims(2) wf_stamp_def)
  then have valid: "valid_value xv (stamp_expr x)"
    using assms(2,3) wf_stamp_def by auto
  obtain xb' xl xh where stamp: "IntegerStamp xb' xl xh = stamp_expr x"
    by (metis assms(1) is_stamp_positive.elims(2))
  have "xb = xb'"
    by (metis stamp valid valid_value.simps(1) xv)
  then have "0 \<le> sint (signed_take_bit (xb - 1) xvv)"
    by (smt (verit) valid int_signed_value.elims is_stamp_positive.simps(1) valid_value.simps(1) xv
        assms(1) stamp)
  then have "\<not> (bit xvv (xb - 1))"
    using val_neg_def by force
  then show ?thesis
    using bit_take_bit_iff xv by auto
qed

lemma stamp_width_in_bounds_expand_lower:
  assumes "width_in_bounds s l h"
  assumes "l' < l"
  shows "width_in_bounds s l' h"
proof -
  have stamp: "is_IntegerStamp s"
    using assms(1) width_in_bounds_implies_integerstamp by auto
  obtain b sl sh where s: "s = IntegerStamp b sl sh"
    by (meson stamp is_IntegerStamp_def)
  then show ?thesis
    using assms by auto
qed

lemma stamp_width_in_bounds_expand_upper:
  assumes "width_in_bounds s l h"
  assumes "h' > h"
  shows "width_in_bounds s l h'"
proof -
  have stamp: "is_IntegerStamp s"
    using assms(1) width_in_bounds_implies_integerstamp by auto
  obtain b sl sh where s: "s = IntegerStamp b sl sh"
    by (meson stamp is_IntegerStamp_def)
  then show ?thesis
    using assms by auto
qed

lemma const_intval_stamp: "\<exists> l h . (constantAsStamp (IntVal b v)) = IntegerStamp b l h"
  using constantAsStamp.simps by simp

lemma stamp_under_defn:
  assumes "stamp_under (stamp_expr x) (stamp_expr y)"
  assumes "wf_stamp x \<and> wf_stamp y"
  assumes "([m, p] \<turnstile> x \<mapsto> xv) \<and> ([m, p] \<turnstile> y \<mapsto> yv)"
  shows "val_to_bool (bin_eval BinIntegerLessThan xv yv) \<or>
        (bin_eval BinIntegerLessThan xv yv) = UndefVal"
proof -
  have yval: "valid_value yv (stamp_expr y)"
    using assms wf_stamp_def by blast
  obtain b lx hx where xstamp: "stamp_expr x = IntegerStamp b lx hx"
    by (metis stamp_under.elims(2) assms(1))
  obtain b' ly hy where ystamp: "stamp_expr y = IntegerStamp b' ly hy"
    by (meson stamp_under.elims(2) assms(1))
  obtain xvv where xvv: "xv = IntVal b xvv"
    by (metis assms(2,3) valid_int wf_stamp_def xstamp)
  obtain yvv where yvv: "yv = IntVal b' yvv"
    by (metis valid_int ystamp yval)
  have xunder: "int_signed_value b xvv \<le> hx"
    by (metis assms(2,3) wf_stamp_def xstamp valid_value.simps(1) xvv)
  have "int_signed_value b xvv < int_signed_value b' yvv"
    by (smt (verit) assms(1) stamp_under.simps(1) valid_int_signed_range xstamp xunder ystamp yval
        yvv)
  then have "(intval_less_than xv yv) = IntVal 32 1 \<or> (intval_less_than xv yv) = UndefVal"
    by (simp add: yvv xvv)
  then show ?thesis
    by force
qed

lemma stamp_under_defn_inverse:
  assumes "stamp_under (stamp_expr y) (stamp_expr x)"
  assumes "wf_stamp x \<and> wf_stamp y"
  assumes "([m, p] \<turnstile> x \<mapsto> xv) \<and> ([m, p] \<turnstile> y \<mapsto> yv)"
  shows "\<not>(val_to_bool (bin_eval BinIntegerLessThan xv yv)) \<or>
          (bin_eval BinIntegerLessThan xv yv) = UndefVal"
proof -
  have yval: "valid_value yv (stamp_expr y)"
    using assms wf_stamp_def by blast
  obtain b lx hx where xstamp: "stamp_expr x = IntegerStamp b lx hx"
    by (metis stamp_under.elims(2) assms(1))
  then obtain b' ly hy where ystamp: "stamp_expr y = IntegerStamp b' ly hy"
    by (meson stamp_under.elims(2) assms(1))
  obtain xvv where xvv: "xv = IntVal b xvv"
    by (metis assms(2,3) valid_int wf_stamp_def xstamp)
  then have xval: "valid_value (IntVal b xvv) (stamp_expr x)"
    using assms(2,3) wf_stamp_def by blast
  obtain yvv where yvv: "yv = IntVal b' yvv"
    by (metis valid_int ystamp yval)
  have "int_signed_value b' yvv < int_signed_value b xvv"
    by (smt (verit) assms(1) stamp_under.simps(1) valid_int_signed_range xstamp xval ystamp yval
        yvv)
  then have "(intval_less_than xv yv) = IntVal 32 0 \<or> (intval_less_than xv yv) = UndefVal"
    by (auto simp add: yvv xvv)
  then show ?thesis
    by force
qed

subsection \<open>Stamp mask lemmas\<close>

context stamp_mask
begin

lemma stamp_mask_up_1_implies_only_lsb_set:
  assumes "\<up>x = 1"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal xb xvv"
  shows "\<forall> i . i \<noteq> 0 \<longrightarrow> \<not>bit xvv i"
  by (metis assms bit_1_iff not_may_implies_false)

lemma stamp_mask_up_1_implies_0_1:
  assumes "\<up>x = 1"
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  assumes "[m, p] \<turnstile> x \<mapsto> xv"
  shows "\<exists> xvv . xv = IntVal b xvv \<and> (xvv \<in> {0, 1})"
proof -
  obtain m p where eval: "[m, p] \<turnstile> x \<mapsto> xv"
    using assms(4) by auto
  obtain xb xvv where xvv: "xv = IntVal xb xvv"
    by (metis Value.collapse(1) assms(2,3) dual_order.refl eval stamp_width_eval_is_eq_intval
        width_in_bounds.simps(1))
  have "xb = b"
    by (metis Stamp.sel(1) assms(2,3) bit_width_maintained eval xvv)
  then show ?thesis
    by (metis assms(1) insertCI stamp_mask_up_1_implies_only_lsb_set upper_bits_unset_implies_0_1
        xvv eval)
qed

lemma stamp_mask_up_1_32_implies_boolean:
  assumes "\<up>x = 1"
  assumes "stamp_expr x = IntegerStamp 32 lo hi"
  assumes "wf_stamp x"
  assumes "[m, p] \<turnstile> x \<mapsto> xv"
  shows "xv = IntVal 32 0 \<or> xv = IntVal 32 1"
  using stamp_mask_up_1_implies_0_1 assms by blast

end

end