section \<open>Integer Stamp Functions from GraalVM Java Code\<close>

text \<open>
This theory corresponds as closely as possible to IntegerStamp.java
in the GraalVM source code.

An IntegerStamp defines the number of bits in an integer value,
the allowable min-max range of that value,
and additional range information in the form of bit masks.
Each IntegerStamp has an up mask and a down mask,
corresponding to a the bits that may be set and the bits that must be set.

Examples:
  A stamp where no range information is known will have;
    an up mask of -1 as all bits may be set, and
    a down mask of 0 as no bits must be set.

  A stamp known to be one should have;
    an up mask of 1 as only the first bit may be set, no others, and
    a down mask of 1 as the first bit must be set and no others.

NOTE 1: like the Java, we use int64 for the min-max ranges.
So any large unsigned range with upper bound above
$2^63-1$ is converted into the universal range: $(- 2^63, 2^63 - 1)$.

NOTE 2: we do not yet model the canBeZero flag.
\<close>

theory JavaIntegerStamp
  imports JavaLong
begin

context
  includes bit_operations_syntax
begin


subsection \<open>The bit-subset relationship between values or masks\<close>

text \<open>The Java code often has 'm2 & ~m1 == 0' to check that mask m1 is a subset (or equal) of m2.
  To improve readability, we define this pattern as the following infix abbreviation.
\<close>  
abbreviation mask_subset :: "'a :: len word \<Rightarrow> 'a :: len word \<Rightarrow> bool" (infix "\<subseteq>'_m" 70) where
  "mask_subset m1 m2 \<equiv> (m1 AND NOT m2 = 0)"

lemma mask_implies:
  assumes "mask_subset m1 m2"
  assumes "bit m1 b"
  shows "bit m2 b"
  by (metis assms(1) assms(2) bit_0_eq bit_and_iff bit_int_code(1) bit_not_iff impossible_bit)

lemma mask_implies_rev:
  assumes "mask_subset m1 m2"
  assumes "\<not> bit m2 b"
  shows "\<not> bit m1 b"
  using assms(1) assms(2) mask_implies by blast

lemma mask_subset_reflexive:
  shows "m1 \<subseteq>_m m1"
  by auto

lemma mask_subset_transitive:
  assumes "m1 \<subseteq>_m m2"
  assumes "m2 \<subseteq>_m m3"
  shows "m1 \<subseteq>_m m3"
  by (rule bit_word_eqI; metis assms bit_and_iff mask_implies)

lemma mask_subset_mono_and:
  assumes "m1 \<subseteq>_m m2"
  shows "(m1 AND m) \<subseteq>_m (m2 AND m)"
  by (rule bit_word_eqI; metis assms bit_and_iff mask_implies mask_subset_reflexive)

lemma mask_subset_mono_or:
  assumes "m1 \<subseteq>_m m2"
  shows "(m1 OR m) \<subseteq>_m (m2 OR m)"
  by (rule bit_word_eqI; metis assms bit.compl_zero bit_and_iff bit_not_iff bit_or_iff negone_set)

lemma mask_subset_ge:
  assumes "m1 \<subseteq>_m m2"
  shows "m1 \<le> m2"
  by (metis assms disjunctive_diff mask_implies_rev uint_minus_simple_alt uint_minus_simple_iff word_and_le2)


subsection \<open>Java Integer Stamps and Invariants\<close>

text \<open>These Stamp values simulate the Java IntegerStamp class closely.\<close>

datatype JavaIntegerStamp = 
  JIS
    (jis_bits: nat)
    (jis_lowerBound: int64)
    (jis_upperBound: int64)
    (jis_downMask: int64)
    (jis_upMask: int64)


text \<open>These stamp invariants are from the IntegerStamp.java constructor,
  plus we add the check that $0 < bits <= 64$.
  TODO: add canBeZero and its invariant.
\<close>
fun JIS_valid :: "JavaIntegerStamp \<Rightarrow> bool" where
  "JIS_valid (JIS bits lo hi downMask upMask) =
    (0 < bits \<and> bits \<le> 64 \<and>
     int_signed_value bits lo \<ge> fst (bit_bounds bits) \<and>
     int_signed_value bits hi \<le> snd (bit_bounds bits) \<and>
     downMask AND mask bits = downMask \<and>
     upMask AND mask bits = upMask \<and>
     (downMask \<subseteq>_m upMask \<or> (upMask = 0 \<and> downMask = mask bits)))"

fun isEmpty :: "JavaIntegerStamp \<Rightarrow> bool" where
  "isEmpty (JIS bits lo hi downMask upMask) =
    (hi <s lo \<or>
     \<not> (downMask \<subseteq>_m upMask) \<or>
     (upMask = 0 \<and> (0 <s lo \<or> hi <s 0)))"


subsection \<open>Significant bit\<close>

text \<open>Returns the most significant bit of a given width, as either 0 or 1.\<close>
definition significantBit :: "nat \<Rightarrow> int64 \<Rightarrow> int64" where
  "significantBit bits value = ((value >>> (bits - 1)) AND 1)"

corollary "significantBit 8 0x80 = 1" by code_simp


lemma significantBitValue:
  "significantBit bits value = (if bit value (bits - 1) then 1 else 0)"
  unfolding significantBit_def
  by (simp add: and_one_eq bit_word_iff_drop_bit_and shiftr_def)

lemma significantBitFalse[simp]:
  "(significantBit bits value = 0) = (\<not> bit value (bits - (Suc 0)))"
  unfolding significantBit_def
  using significantBitValue significantBit_def by force

lemma significantBitTrue[simp]:
  "(significantBit bits value = 1) = (bit value (bits - (Suc 0)))"
  unfolding significantBit_def
  using significantBitValue significantBit_def by force


lemma mask_subset_pos64_ge_signed:
  fixes m1 m2 :: "int64"
  assumes "m1 \<subseteq>_m m2"
  assumes "significantBit 64 m2 = 0"
  shows "m1 \<le>s m2"
proof -
  have "0 \<le> sint m2"
    by (metis assms(2) bit_unsigned_iff signed_take_bit_nonnegative_iff significantBitFalse sint_uint size64 wsst_TYs(3))
  have "significantBit 64 m1 = 0"
    using assms mask_implies significantBitValue by fastforce
  then have "0 \<le> sint m1"
    by (metis bit_unsigned_iff signed_take_bit_nonnegative_iff significantBitFalse sint_uint size64 wsst_TYs(3))
  then show ?thesis
    by (metis (no_types, opaque_lifting) AND_upper2 \<open>(0::int) \<le> sint (m2::64 word)\<close> assms(1) bit.conj_disj_distrib or.right_neutral signed_and_eq word_and_max word_or_not word_sle_eq)
qed

lemma mask_subset_neg64_ge_signed:
  fixes m1 m2 :: "int64"
  assumes "m1 \<subseteq>_m m2"
  assumes "significantBit 64 m1 = 1"
  shows "m1 \<le>s m2"
proof -
  have "sint m1 < 0"
    using assms(2) bit_last_iff significantBitValue by fastforce
  then have "sint m2 < 0"
    using assms(1) bit_last_iff mask_implies by blast
  then show ?thesis
    by (metis (no_types, lifting) \<open>sint (m1::64 word) < (0::int)\<close> and.commute and_less_eq assms(1) bit.conj_disj_distrib or.right_neutral signed_and_eq word_and_max word_or_not word_sle_eq)
qed

text \<open>Now we generalise the above results for any bit size, using int_signed_value.\<close>
lemma mask_subset_pos_ge_signed:
  fixes m1 m2 :: "int64"
  assumes "m1 \<subseteq>_m m2"
  assumes "0 < bits"
  assumes "bits \<le> 64"
  assumes "significantBit bits m2 = 0"
  shows "int_signed_value bits m1 \<le> int_signed_value bits m2"
proof -
  have m1_0: "\<not> bit m1 (bits - (Suc 0))"
    using assms(1) assms(4) mask_implies significantBitFalse by blast
  then have "0 \<le> take_bit (bits - (Suc 0)) m1"
    by simp
  then have m2_0: "\<not> bit m2 (bits - (Suc 0))"
    using assms significantBitFalse by auto
  then have "0 \<le> take_bit (bits - (Suc 0)) m2"
    by simp
  then have m2: "0 \<le> int_signed_value bits m2"
    by (metis (mono_tags, opaque_lifting) One_nat_def Suc_le_lessD Suc_pred' m2_0 assms(2) assms(3) bit.conj_cancel_left int_signed_value.simps mult_zero_left of_bool_eq(1) or_eq_not_not_and signed_take_bit_def size64 take_bit_smaller_range word_and_max word_not_not wsst_TYs(3))
  then have "take_bit (bits - (Suc 0)) m1 \<le> take_bit (bits - (Suc 0)) m2"
    using mask_subset_ge
    by (metis (no_types, opaque_lifting) assms(1) bit.conj_disj_distrib take_bit_and word_and_max word_and_not word_not_dist(2) word_not_not)
  then show ?thesis
    unfolding int_signed_value.simps signed_take_bit_def
    by (smt (verit, ccfv_threshold) AND_upper2 One_nat_def m1_0 and.commute and.idem and.right_neutral and_zero_eq assms(1) bit.conj_disj_distribs(2) int_signed_value.elims m2 m2_0 mult_zero_left of_bool_eq(1) signed_and_eq signed_take_bit_def take_bit_and word_ao_equiv word_bw_assocs(1) word_or_not)
qed

lemma bit_not_iff_word:
  fixes w :: "'a :: len word"
  assumes "n < LENGTH('a)"
  shows "bit (NOT w) n = (\<not> bit w n)"
  by (simp add: assms bit_not_iff)

lemma bit_subset_and_or_not:
  "((a AND m) OR (NOT m)) \<subseteq>_m ((b AND m) OR (NOT m)) = ((a AND m) \<subseteq>_m (b AND m))"
  by (smt (verit, del_insts) and.assoc bit.conj_cancel_left word_ao_absorbs(7) word_ao_dist word_bw_comms(1) word_not_dist(1) word_not_not)

lemma mask_subset_neg_ge_signed:
  fixes m1 m2 :: "int64"
  assumes "m1 \<subseteq>_m m2"
  assumes "0 < bits"
  assumes "bits \<le> 64"
  assumes "significantBit bits m1 = 1"
  shows "int_signed_value bits m1 \<le> int_signed_value bits m2"
proof -
  have 1: "of_bool (bit m1 (bits - 1)) = 1"
    using assms(4) by fastforce
  then have 2: "signed_take_bit (bits - 1) m1 = (take_bit (bits - 1) m1 OR NOT (mask (bits - 1)))"
    by (simp add: signed_take_bit_def)
  then have "int_signed_value bits m1 < 0"
    unfolding int_signed_value.simps signed_take_bit_def
    by (metis Suc_le_eq Suc_pred' assms(2) assms(3) diff_0 dual_order.refl not_less or_negative_int_iff signed_or_eq sint_n1 size64 take_bit_minus_one_eq_mask take_bit_smaller_range word_or_not wsst_TYs(3) zle_diff1_eq)
  then have "significantBit bits (signed_take_bit (bits - 1) m1) = 1"
    unfolding 2 significantBitTrue
    by (metis "1" One_nat_def bit_1_0 bit_and_iff bit_not_iff bit_of_bool_iff bit_or_iff impossible_bit take_bit_eq_mask)
  then have "bits - 1 < 64"
    using assms by arith
  then have "\<not> bit (mask (bits - 1) :: int64) (64 - 1)"
    by (simp add: bit_mask_iff)
  then have "bit (NOT (mask (bits - 1) :: int64)) (64 - 1)"
    by (metis bit_not_iff_word diff_less len_gt_0 less_numeral_extra(1) size64 wsst_TYs(3))
  then have 64: "significantBit 64 (signed_take_bit (bits - 1) m1) = 1"
    unfolding 2 significantBitTrue
    by (metis One_nat_def bit_or_iff)
  have 2: "of_bool (bit m2 (bits - 1)) = 1"
    using "1" assms(1) mask_implies by auto
  then have "signed_take_bit (bits - 1) m1 \<subseteq>_m signed_take_bit (bits - 1) m2"
    unfolding signed_take_bit_def 1 2 mult_1 take_bit_eq_mask bit_subset_and_or_not
    using mask_subset_mono_and
    using assms(1) by blast
  then have "signed_take_bit (bits - 1) m1 \<le>s signed_take_bit (bits - 1) m2"
    using 64 mask_subset_neg64_ge_signed by blast
  then show ?thesis
    by (simp add: word_sle_eq)
qed

(*
fun sf_contains:: "Stamp \<Rightarrow> Value \<Rightarrow> bool" where
  "sf_contains (IntegerStamp b l h d u) (IntVal64 val) = ((sint val \<ge> l) \<and> (sint val \<le> h))" |
  "sf_contains _ _ = False"

fun sf_is_positive:: "Stamp \<Rightarrow> bool" where
  "sf_is_positive (IntegerStamp b l h d u) = (l \<ge> 0) " |
  "sf_is_positive _ = False"

fun sf_is_negative:: "Stamp \<Rightarrow> bool" where
  "sf_is_negative (IntegerStamp b l h d u) = (h \<le> 0) " |
  "sf_is_negative _ = False"

fun sf_is_strictly_positive:: "Stamp \<Rightarrow> bool" where
  "sf_is_strictly_positive (IntegerStamp b l h d u) = (l > 0) " |
  "sf_is_strictly_positive _ = False"

fun sf_is_strictly_negative:: "Stamp \<Rightarrow> bool" where
  "sf_is_strictly_negative (IntegerStamp b l h d u) = (h < 0) " |
  "sf_is_strictly_negative _ = False"

fun sf_can_be_positive:: "Stamp \<Rightarrow> bool" where
  "sf_can_be_positive (IntegerStamp b l h d u) = (h > 0) " |
  "sf_can_be_positive _ = False"

fun sf_can_be_negative:: "Stamp \<Rightarrow> bool" where
  "sf_can_be_negative (IntegerStamp b l h d u) = (l < 0) " |
  "sf_can_be_negative _ = False"

fun sf_is_compatible1:: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where 
  "sf_is_compatible1 (IntegerStamp b1 l1 h1 d1 u1) (IntegerStamp b2 l2 h2 d2 u2) = (b1 = b2)" |
  "sf_is_compatible1 _ _ = False"

fun sf_is_compatible2:: "Stamp \<Rightarrow> Value \<Rightarrow> bool" where 
  "sf_is_compatible2 this (IntVal32 val) = True" |
  "sf_is_compatible2 this (IntVal64 val) = True" |
  "sf_is_compatible2 _ _ = False"

fun sf_same_sign_bounds:: "Stamp \<Rightarrow> bool" where 
  "sf_same_sign_bounds (IntegerStamp b l h d u) = ((l < 0) = (h < 0))" |
  "sf_same_sign_bounds _ = False"




fun stamp_for_mask:: "Value \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Stamp" where
  "stamp_for_mask (IntVal64 bits) (IntVal64 down) (IntVal64 up) = (
    let lo = (minValueForMasks (IntVal64 bits) (IntVal64 down) (IntVal64 up)) in
    let hi = (maxValueForMasks (IntVal64 bits) (IntVal64 down) (IntVal64 up)) in 
    IntegerStamp (unat bits) (val_to_int lo) (val_to_int hi))" | 
  "stamp_for_mask _ _ _ = IllegalStamp"

value "val_to_int (minValueForMasks (IntVal64 1) (IntVal64 2) (IntVal64 3))"

value " 2::int64"

value "max (42::nat) 3"
*)

value "sint ((-1 :: int8) << 2)"


subsection \<open>Calculate minimum bound from masks\<close>

text \<open>If the sign bit MUST be zero, then the value is positive and $downMask$ bits give us a
  minimum (positive) value.  
  Otherwise, the sign bit MIGHT be set, so the minimum value is $- 2^{bits-1}$
  plus all the bits (in $downMask$) that are known to be set.
  Precondition: $significantBit upMark = 0 \<longrightarrow> significantBit downMask = 1$.\<close>
definition minValueForMasks:: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64" where
  "minValueForMasks bits downMask upMask = (
    if significantBit bits upMask = (0::int64)
    then downMask
    else downMask OR ((-1) << (bits - 1))
  )"

lemma less_bits_less_than:
  fixes down val :: "'a :: len word"
  assumes "down \<subseteq>_m val"
  shows "down \<le> val"
  by (metis assms disjunctive_diff mask_implies word_and_le2 word_sub_le_iff)

lemma top_bit_false_if_le:
  fixes a b :: "'a :: len word"
  assumes "a \<le> b"
  assumes "\<not> bit b (LENGTH('a) - Suc 0)"
  shows "\<not> bit a (LENGTH('a) - Suc 0)"
proof (induction "LENGTH('a)")
  case 0
  then show ?case by auto
next
  case (Suc x)
  then have "uint b < 2 ^ (LENGTH('a) - (Suc 0))"
    by (smt (verit, ccfv_threshold) One_nat_def assms bit_last_iff diff_Suc_1 signed_take_bit_int_less_eq sint_uint unsigned_less)
  then have "uint a < 2 ^ (LENGTH('a) - (Suc 0))"
    by (smt (verit) assms(1) word_less_eq_iff_unsigned)
  then show ?case
    by (smt (verit) bit_last_iff signed_take_bit_int_eq_self sint_uint unsigned_greater_eq) 
qed


text \<open>When we have a subset relation between the bits of two words, we can show signed
  less-than-or-equal when they are both positive, or both negative.\<close>

lemma less_bits_signed_leq_pos:
  fixes down val :: "'a :: len word"
  assumes "down \<subseteq>_m val"
  assumes "\<not> bit val (LENGTH('a) - Suc 0)"
  shows "down \<le>s val"
proof -
  have uval: "sint val = uint val"
    by (metis (no_types, lifting) assms(2) bintr_uint bit_unsigned_iff le_eq_less_or_eq signed_take_bit_eq_if_positive sint_uint uint_sint unsigned_take_bit_eq)
  have "\<not> bit down (LENGTH('a) - Suc 0)"
    using assms(1) assms(2) mask_implies by blast
  then have udown: "sint down = uint down"
    by (smt (verit, ccfv_threshold) bit_last_iff signed_take_bit_int_eq_self sint_less sint_uint take_bit_int_greater_self_iff uint_sint unsigned_greater_eq)
  then show ?thesis
    unfolding word_sle_eq udown uval word_less_eq_iff_unsigned[symmetric]
    using assms(1) less_bits_less_than by simp 
qed

lemma less_bits_signed_leq_neg:
  fixes down val :: "'a :: len word"
  assumes "down \<subseteq>_m val"
  assumes "bit down (LENGTH('a) - Suc 0)"
  shows "down \<le>s val"
proof -
  have "bit val (LENGTH('a) - Suc 0)"
    using assms mask_implies by auto
  then show ?thesis
    unfolding word_sle_eq sint_uint signed_take_bit_eq_take_bit_minus
    using assms bit_uint_iff mask_subset_ge word_of_int_less_eq_iff by fastforce
qed

value "of_bool False :: 1 word"
value "horner_sum of_bool 2 (map (\<lambda>x. True) [0 :: int64, 1, 0, 1]) :: int64"
value "map (bit (0x14 :: int8)) [0 ..< 8]"

(* Just an experiment with horner_sum *)
lemma to_bits_test:
  assumes "w < 2 ^ a"
  shows "(w :: nat) = of_nat (horner_sum of_bool 2 (map (bit w) [0..<a]))"
  by (simp add: assms horner_sum_bit_eq_take_bit take_bit_nat_eq_self)


lemma signed_leq_if_pos_leq:
  fixes a b :: "'a :: len word"
  assumes "a \<le> b"
  assumes "0 < LENGTH('a)"
  assumes "\<not> bit b (LENGTH('a) - Suc 0)"
  shows "a \<le>s b"
proof -
  have b: "0 \<le> sint b"
    using assms(3) bit_last_iff by fastforce
  then have "\<not> bit a (LENGTH('a) - Suc 0)"
    using assms(1) assms(3) top_bit_false_if_le by fastforce
  then have a: "0 \<le> sint a"
    by (simp add: bit_last_iff)
  then show ?thesis
    unfolding word_sle_eq
    by (smt (verit) Suc_diff_Suc assms(1) assms(2) b diff_zero signed_take_bit_int_eq_self signed_take_bit_int_less_eq sint_uint uint_add_lem unsigned_greater_eq word_le_exists')
qed

lemma neg1_shifted_is_not_mask:
  "((-1) << n) = NOT (mask n)"
  by (simp add: shiftl_def)

(* Maybe not needed, since it is just neg1_shifted_is_not_mask plus minus_exp_eq_not_mask *)
lemma neg1_shifted_is_min_value:
  "((-1 :: int64) << bits) = - (2 ^ bits)"
  unfolding neg1_shifted_is_not_mask
  by (simp add: minus_exp_eq_not_mask)


text \<open>This is a helper lemma for when minValueForMasks returns a negative value.
  In that case the bits above $n$ are all true, and we only need a subset
  relationship on the bits below $n$ in order to prove signed less-than-or-equal.\<close>
lemma neg_subset_leq:
  fixes a b :: int64
  assumes "0 \<le> n"
  assumes "n < 64"
  assumes "a = (((-1) << n) OR aLow)"
  assumes "aLow \<subseteq>_m b"
  shows "signed_take_bit n a \<le>s signed_take_bit n b"
proof -
  have an: "bit a n"
    by (simp add: assms(2) assms(3) bit_mask_iff bit_not_iff bit_or_iff shiftl_def)
  then have a: "signed_take_bit n a = (take_bit n a OR NOT (mask n))"
    unfolding signed_take_bit_def by simp
  then have a63: "bit (signed_take_bit n a) (64 - 1)"
    by (smt (z3) One_nat_def Suc_leI Suc_pred' assms(1) assms(2) bit.compl_zero bit_last_iff bit_mask_iff bit_not_iff_eq bit_or_iff linorder_not_le order_le_less_trans sint_n1 size64 wsst_TYs(3))
  then have a0: "signed_take_bit n a \<le>s 0"
    by (metis One_nat_def bit_last_iff dual_order.strict_iff_not sint_0 size64 word_sle_eq wsst_TYs(3))
  then show ?thesis
  proof (cases "bit b n")
    case True
    then have b: "signed_take_bit n b = (take_bit n b OR NOT (mask n))"
      by (simp add: signed_take_bit_eq_if_negative)
    then have "signed_take_bit n a \<subseteq>_m signed_take_bit n b"
      using a b
      by (metis (no_types, lifting) assms(3) assms(4) bit.double_compl mask_subset_mono_and mask_subset_mono_or mask_subset_reflexive neg1_shifted_is_not_mask or.right_neutral take_bit_eq_mask take_bit_or word_bw_comms(2))
    then show ?thesis
      using a63 One_nat_def mask_subset_neg64_ge_signed significantBitTrue by presburger
  next
    case False
    then have b: "signed_take_bit n b = take_bit n b"
      by (simp add: signed_take_bit_eq_if_positive)
    then have "0 \<le>s signed_take_bit n b"
      by (metis an bit_imp_le_length signed_0 take_bit_smaller_range word_sle_eq)
    then show ?thesis
      using a0 by auto
  qed
qed


text \<open>The main correctness result for minValueForMasks is that all values that have
  the required bits set will be greater than (or equal to) the lower bound that
  minValueForMasksCorrect returns.\<close> 
lemma minValueForMasksCorrect:
  assumes "minValueForMasks bits downMask upMask = m"
  assumes "0 < bits"
  assumes "bits \<le> 64"
  assumes "val \<subseteq>_m upMask"
  assumes "downMask \<subseteq>_m val"
  shows "int_signed_value bits m \<le> int_signed_value bits val"
proof (cases "significantBit bits upMask = 0")
  case True
  then have 10: "\<not> bit upMask (bits - Suc 0)"
    using significantBitFalse by simp
  then have 11: "\<not> bit val (bits - Suc 0)"
    using assms(4) mask_implies by blast
  then have 12: "\<not> bit downMask (bits - Suc 0)"
    using assms(5) mask_implies by blast
  then have m: "m = downMask"
    using True assms(1) minValueForMasks_def by fastforce
  then have mval: "m \<le> val"
    using assms(5) less_bits_less_than by blast
(* strange that unsigned is easier to prove here than signed! *)
  then have "0 \<le> signed_take_bit (bits - Suc 0) val"
    using word_zero_le by blast
  then have valpos: "0 \<le> int_signed_value bits val"
    unfolding int_signed_value.simps One_nat_def
    by (metis (mono_tags, opaque_lifting) "11" assms(3) bit_uint_iff less_imp_diff_less nat_less_le signed_take_bit_eq_if_positive sint_uint size64 take_bit_nonnegative take_bit_smaller_range wsst_TYs(3))
  then have "0 \<le> int_signed_value bits m"
    by (smt (verit, best) "11" "12" One_nat_def valpos mval bit_last_iff bit_take_bit_iff int_signed_value.simps m signed_take_bit_eq_if_positive top_bit_false_if_le)
  then show ?thesis
    using "11" assms(2) assms(3) assms(5) m mask_subset_pos_ge_signed significantBitFalse by blast
next
  case False
  then have 10: "bit upMask (bits - Suc 0)"
    using significantBitFalse by simp
  then have m1: "m = (downMask OR ((-1) << (bits - Suc 0)))"
    using assms(1) minValueForMasks_def by fastforce
  then have 11: "bit ((-1 :: int64) << (bits - Suc 0)) (bits - Suc 0)"
    unfolding neg1_shifted_is_not_mask
    using "10" bit_mask_iff bit_not_iff impossible_bit by blast
  then have 12: "bit m (bits - 1)"
    by (metis m1 bit_or_iff One_nat_def)
  then have 13: "of_bool (bit m (bits - 1)) = 1"
    by simp
  then have m2: "int_signed_value bits m = 
     sint (take_bit (bits - (1::nat)) m OR (NOT (mask (bits - (1::nat)))))"
    by (simp add: signed_take_bit_def)
  then have "bit (int_signed_value bits m) (size m - Suc 0)"
    by (smt (z3) "12" bit_imp_le_length bit_last_iff bit_not_iff bit_or_iff bit_sint_iff impossible_bit sint_n1 take_bit_minus_one_eq_mask take_bit_smaller_range wsst_TYs(3))
  then have "int_signed_value bits m < 0"
    by (metis One_nat_def bit_last_iff bit_sint_iff int_signed_value.simps wsst_TYs(3))
  then have m3: "m = (((-1) << (bits - Suc 0)) OR downMask)"
    using m1 or.commute by blast
  then show ?thesis
    using assms(2) assms(3) assms(5) neg_subset_leq
    by (simp add: word_sle_eq)
qed

value "((-1 :: int8) << (8 - Suc 0))"


subsection \<open>Calculate maximum bound from masks\<close>

text \<open>Precondition: $significantBit downMask = 1 \<longrightarrow> significantBit upMask = 1$.\<close>
fun maxValueForMasks:: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64" where
  "maxValueForMasks bits downMask upMask = (
    if significantBit bits downMask = (1::int64)
    then (signed_take_bit (bits - 1) upMask)
    else (upMask AND (mask bits >>> 1))
  )"

value "maxValueForMasks 32 0 1"
value "sint(minValueForMasks 32 (-1) (-1))"

value "maxValueForMasks 32 0 4294967295"
value "sint(maxValueForMasks 32 (-1) 4294967295)"

value "numberOfLeadingZeros (5 :: int64)"


value "min 2 3::int"

value "(word_of_int (-1)::int64)"

value "((-1) :: int64) >>> nat (4 - 8)"
value "- (1 :: int64)"

definition neg_one64 :: "int64" where
  "neg_one64 = ((-1) :: int64)"

fun createJIS:: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> JavaIntegerStamp" where
  "createJIS bits lo hi down up = (
    let minValue = minValueForMasks bits down up in
    let loTemp = max lo minValue :: int64 in
    let maxValue = maxValueForMasks bits down up in 
    let hiTemp = min hi maxValue :: int64 in
    let defaultMask = mask bits :: int64 in
    let (boundedUpMask, boundedDownMask) = (
      if loTemp = hiTemp then
        (loTemp, loTemp)
      else
        if loTemp \<ge> 0 then
          let upperBoundLeadingZeros = numberOfLeadingZeros hiTemp in
          let differentBits = (loTemp XOR hiTemp) in
          let sameBitCount = numberOfLeadingZeros (differentBits >> upperBoundLeadingZeros) in
          let x = (neg_one64 >>> nat (upperBoundLeadingZeros + sameBitCount)) in
          (hiTemp OR x, hiTemp AND (NOT x))
        else
          if hiTemp \<ge> 0 then
            (defaultMask, 0 :: int64)
          else
            let lowerBoundLeadingOnes = numberOfLeadingZeros (NOT loTemp) in
            let differentBits = (loTemp XOR hiTemp) in
            let sameBitCount = numberOfLeadingZeros (differentBits >> lowerBoundLeadingOnes) in
            let x = (neg_one64 >>> nat (lowerBoundLeadingOnes + sameBitCount)) in
            let y = (NOT (neg_one64 >>> nat lowerBoundLeadingOnes)) in
            (loTemp OR x OR y, loTemp AND (NOT x) OR y)
    ) in
    JIS bits loTemp hiTemp (defaultMask AND down OR boundedDownMask) (defaultMask AND up AND boundedUpMask)
  )"

fun create_without_masks:: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> JavaIntegerStamp" where
  "create_without_masks bits lo hi = (createJIS bits lo hi 0 (mask bits))"


value "JIS_valid (createJIS 32 (-1000) 10000 0xF0F 0x3FFF)"
value "JIS_valid (create_without_masks 32 (-1000) 10000)"




(* TODO:
fun create_integer_stamp:: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> JavaIntegerStamp" where
  "create_integer_stamp bits lo hi down up = (
    if lo > hi \<or> ~ ((down AND (NOT up)) = 0) \<or> (up = 0 \<and> (lo > 0 \<or> hi < 0))
    then empty_stamp (IntegerStamp bits 0 0 0 0)
    else createJIS bits lo hi down up
  ) "
*)

value "~(nat 2 = 3) "
value "~ nat 3 AND NOT 2 = 0 "

(* Call with an integer stamp, and a new constant value. *) 
(* TODO:
fun sf_constant :: "JavaIntegerStamp \<Rightarrow> int \<Rightarrow> Value \<Rightarrow> JavaIntegerStamp" where
  "sf_constant this bits (IntVal64 val) = (
    if bits = 1 \<and> val = 1
    then create_without_masks (IntVal64 (word_of_int (stp_bits this))) (IntVal64 (-1)) (IntVal64 (-1))
    else create_without_masks (IntVal64 (word_of_int (stp_bits this))) (IntVal64 val) (IntVal64 val)
  )" |
  "sf_constant this _ _ = this"

value "sf_constant (IntegerStamp 32 1 2 1 2) 1  UndefVal"

value "sf_constant (IntegerStamp 32 1 2 1 2) 64 (IntVal64 5)"


fun sf_contains:: "JavaInJavaIntegerStamptStamp \<Rightarrow> Value \<Rightarrow> bool" where
  "sf_contains (IntegerStamp b l h d u) (IntVal64 val) = ((sint val \<ge> l) \<and> (sint val \<le> h))" |
  "sf_contains _ _ = False"
*)


fun sf_is_positive:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_is_positive (JIS b l h d u) = (l \<ge> 0) "

fun sf_is_negative:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_is_negative (JIS b l h d u) = (h \<le> 0) "

fun sf_is_strictly_positive:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_is_strictly_positive (JIS b l h d u) = (l > 0) "

fun sf_is_strictly_negative:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_is_strictly_negative (JIS b l h d u) = (h < 0) "

fun sf_can_be_positive:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_can_be_positive (JIS b l h d u) = (h > 0) "

fun sf_can_be_negative:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_can_be_negative (JIS b l h d u) = (l < 0) "

fun sf_is_compatible1:: "JavaIntegerStamp \<Rightarrow> JavaIntegerStamp \<Rightarrow> bool" where 
  "sf_is_compatible1 (JIS b1 l1 h1 d1 u1) (JIS b2 l2 h2 d2 u2) = (b1 = b2)"

(* TODO:
fun sf_is_compatible2:: "JavaIntegerStamp \<Rightarrow> Value \<Rightarrow> bool" where 
  "sf_is_compatible2 this (IntVal32 val) = True" |
  "sf_is_compatible2 this (IntVal64 val) = True" |
  "sf_is_compatible2 _ _ = False"
*)

fun sf_same_sign_bounds:: "JavaIntegerStamp \<Rightarrow> bool" where 
  "sf_same_sign_bounds (JIS b l h d u) = ((l < 0) = (h < 0))"



(* TODO:
fun stamp_for_mask:: "Value \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> JavaIntegerStamp" where
  "stamp_for_mask (IntVal64 bits) (IntVal64 down) (IntVal64 up) = (
    let lo = (minValueForMasks (IntVal64 bits) (IntVal64 down) (IntVal64 up)) in
    let hi = (maxValueForMasks (IntVal64 bits) (IntVal64 down) (IntVal64 up)) in 
    IntegerStamp (unat bits) (val_to_int lo) (val_to_int hi))" | 
  "stamp_for_mask _ _ _ = IllegalStamp"

value "val_to_int (minValueForMasks (IntVal64 1) (IntVal64 2) (IntVal64 3))"
*)

value "max (42::nat) 3"

end (* bit_operations_syntax for infix AND, OR, XOR, and prefix NOT *)
end
