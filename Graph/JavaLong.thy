section \<open>java.lang.Long\<close>

text \<open>Utility functions from the Java Long class that Graal occasionally makes use of.\<close>

theory JavaLong
  imports
    JavaWords
    "HOL-Library.FSet"
begin

lemma negative_all_set_32: "n < 32 \<Longrightarrow> bit (-1::int32) n"
  apply transfer by fastforce

(* TODO: better handle empty *)
definition MaxOrNeg :: "nat set \<Rightarrow> int" where
  "MaxOrNeg s = (if s = {} then -1 else Max s)"

definition MinOrHighest :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "MinOrHighest s m = (if s = {} then m else Min s)"

lemma MaxOrNegEmpty: "MaxOrNeg s = -1 \<longleftrightarrow> s = {}"
  unfolding MaxOrNeg_def by auto

lemma MaxOrNeg_neg: "MaxOrNeg {} = -1"
  by (simp add: MaxOrNeg_def)

lemma MaxOrNeg_max: "s \<noteq> {} \<Longrightarrow> MaxOrNeg s = Max s"
  by (simp add: MaxOrNeg_def)

subsection \<open>Helpful lemmas\<close>

fun bin_is_even :: "'a::len word \<Rightarrow> bool" where
  "bin_is_even v = (\<not>bit v 0)"

subsubsection \<open>Nat lemmas\<close>

lemma nat_bot_set: "(0::nat) \<in> xs \<longrightarrow> (\<forall>x \<in> xs . 0 \<le> x)"
  by fastforce

lemma nat_add_zero: "\<forall>w. word_of_nat (unat (w::'a :: len word) + unat (0::'a :: len word)) = w"
  by simp

lemma size_len_eq: "LENGTH('a) = Nat.size (v::'a::len word)"
  by (simp add: size_word.rep_eq)

lemma unat_word_of_nat_unfold: "v < (2 ^ LENGTH('a)) \<Longrightarrow> unat (word_of_nat (v)::'a::len word) = v"
  using le_unat_uoi by (simp add: of_nat_inverse)

lemma unat_word_of_nat_unfold_64: "v < (2 ^ LENGTH(64)) \<Longrightarrow> unat (word_of_nat (v)::64word) = v"
  using unat_word_of_nat_unfold by blast

lemma lt_word_of_nat:
  assumes "v < b"
  assumes "b < 2 ^ LENGTH('a)"
  shows "((word_of_nat v):: 'a::len word) < word_of_nat b"
  by (smt (verit) assms nat_int_comparison(2) unat_word_of_nat_unfold word_less_iff_unsigned)

lemma of_nat_gt0_implies_eq: "n > 0 \<Longrightarrow> (n::int) = of_nat (nat n)"
  by simp

lemma word_of_nat_leq_len_1_64:
  fixes n :: nat
  assumes "n \<le> (63::nat)"
  shows "(word_of_nat n::64word) \<le> (63::64word)"
  by (metis (mono_tags, lifting) assms size64 add_lessD1 le_eq_less_or_eq lt_word_of_nat word_size
      less_exp numeral_plus_numeral of_nat_numeral semiring_norm(2,8) word_le_less_eq)

subsubsection \<open>Bit lemmas\<close>

lemma union_bit_sets:
  "{n . n < Nat.size a \<and> bit a n} \<union> {n . n < Nat.size a \<and> \<not>(bit a n)} = {n . n < Nat.size a}"
  by fastforce

lemma disjoint_bit_sets: "{n . n < Nat.size a \<and> bit a n} \<inter> {n . n < Nat.size a \<and> \<not>(bit a n)} = {}"
  by blast

lemma zero_no_bits: "{n . bit 0 n} = {}"
  by simp

lemma max_bit: "bit (v::('a::len) word) n \<Longrightarrow> n < size v"
  by (simp add: bit_imp_le_length size_word.rep_eq)

lemma max_set_bit: "MaxOrNeg {n . bit (v::('a::len) word) n} < Nat.size v"
  unfolding MaxOrNeg_def apply auto by (simp add: max_bit)

lemma higherBitsFalse:
  fixes v :: "'a :: len word"
  shows "i > size v \<Longrightarrow> \<not>(bit v i)"
  by (simp add: bit_word.rep_eq size_word.rep_eq)

lemma bit_lsb_set_in_all_ones: "bit (-1::'a::len word) 0"
  by auto

lemma bit_set_not: "bit v n \<Longrightarrow> \<not>bit (not v) n"
  by (simp add: bit_not_iff)

lemma negone_set: "bit (-1::('a::len) word) n \<longleftrightarrow> n < LENGTH('a)"
  by simp

lemma negone_all_bits: "{n . bit (-1::('a::len) word) n} = {n . 0 \<le> n \<and> n < LENGTH('a)}"
  using negone_set by auto

lemma bits_finite: "finite {n . bit (v::('a::len) word) n}"
  by simp

lemma zero_bits_card_0: "\<forall>i . \<not>bit v i \<Longrightarrow> card {i . bit v i} = 0"
  by auto

lemma empty_zero_bits_iff: "{i . bit v i} = {} \<longleftrightarrow> (\<forall>i . \<not>bit v i)"
  by auto

lemma zero_empty_bits: "v = 0 \<Longrightarrow> {i . bit v i} = {}"
  by simp

lemma no_bits_implies_zero: "\<forall> i . \<not>bit v i \<Longrightarrow> v = 0"
  by (simp add: bit_eqI)

lemma bits_1_set: "{n . bit 1 n} = {0}"
  by (simp add: bit_1_iff)

lemma bits_set_in_range: "bit (v::'a::len word) n \<Longrightarrow> n < LENGTH('a)"
  by (simp add: bit_imp_le_length)

lemma bits_bound_eq: "{n . bit (v::'a::len word) n} = {n . n < Nat.size v \<and> bit v n}"
  using max_bit by auto

lemma bits_card_bound_eq: "card {n . bit (v::'a::len word) n} = card {n . n < Nat.size v \<and> bit v n}"
  by (meson max_bit)

lemma all_ones_card: "card {n . bit (-1::'a::len word) n} = LENGTH('a)"
  by fastforce

lemma forall_eq_bits: "(\<forall> n . bit v n  = bit v' n) \<longleftrightarrow> {n . bit v n} = {n . bit v' n}"
  by blast

lemma bits_same_implies_val_same: "(\<forall> n . bit v n  = bit v' n) \<Longrightarrow> v = v'"
  by (simp add: bit_eqI)

lemma bits_same_set_implies_val_same: "{n . bit v n} = {n . bit v' n} \<Longrightarrow> v = v'"
  by (simp add: bits_same_implies_val_same forall_eq_bits)

lemma upper_bits_unset_implies_0_1: "\<forall> i . i \<noteq> 0 \<longrightarrow> \<not>bit v i \<Longrightarrow> v = 0 \<or> v = 1"
  by (metis bit_1_iff bits_same_implies_val_same no_bits_implies_zero)

lemma nonzero_nonempty_iff: "v \<noteq> 0 \<longleftrightarrow> {i . bit v i} \<noteq> {}"
  by (metis bits_same_set_implies_val_same zero_no_bits)

lemma take_bit_leq: "take_bit b (v::'a::len word) \<le> v"
  by (simp add: unsigned_take_bit_eq word_le_nat_alt)

lemma word_lt: "\<forall> (v::64word) . v \<noteq> -1 \<longrightarrow> v < -1"
  using word_order.not_eq_extremum by auto

lemma bit_set_implies_atleast_pow2:
  fixes v :: "'a :: len word"
  shows "bit v i \<Longrightarrow> v - (2 ^ i) \<ge> 0"
  by simp

lemma single_bit_set:
  fixes v :: "'a::len word"
  assumes "{n . bit v n} = {b}"
  shows "bit v b \<and> (\<forall> i . i \<noteq> b \<longrightarrow> \<not>bit v i)"
  using assms by auto

lemma bit_set_implies_range:
  fixes v :: "'a::len word"
  assumes "b \<in> {n . bit v n}"
  shows "b < LENGTH('a)"
proof -
  have "\<forall> i . bit v i \<longrightarrow> i < LENGTH('a)"
    by (simp add: bit_imp_le_length)
  then show ?thesis
    using assms by blast
qed

lemma unset_above:
  fixes v :: "'a::len word"
  shows "\<forall> i . i \<ge> LENGTH('a) \<longrightarrow> \<not>bit v i"
  using bit_imp_le_length verit_comp_simplify1(3) by blast

lemma set_bits_in_range:
  fixes v :: "'a::len word"
  shows "\<forall> i . bit v i \<longrightarrow> i \<ge> 0 \<and> i < LENGTH('a)"
  apply auto by (simp add: bit_imp_le_length)

lemma horner_sum_word:
  fixes v :: "'a::len word"
  shows "v = (horner_sum of_bool 2 (map (\<lambda>i. bit v i) [0..<LENGTH('a)]) :: 'a word)"
  by (simp add: horner_sum_bit_eq_take_bit)

lemma horner_sum_word_push_bit:
  fixes v :: "'a::len word"
  shows "v = (\<Sum>i=0..LENGTH('a) . (push_bit i (of_bool (bit v i))))"
  by (metis atLeastLessThanSuc_atLeastAtMost take_bit_sum take_bit_word_beyond_length_eq nat_less_le
      lessI)

lemma sum_word_rewrite:
  fixes v :: "'a::len word"
  shows "(\<Sum>i=0..LENGTH('a) . (push_bit i (of_bool (bit v i)))) =
         (\<Sum>i=0..LENGTH('a) . of_bool (bit v i) * (push_bit i 1))"
  by (metis (lifting) lambda_one lambda_zero push_bit_of_0 of_bool_eq_0_iff of_bool_eq_1_iff)

lemma sum_push_bit_distrib_sub:
  assumes "finite s"
  assumes "S \<in> s"
  shows "(\<Sum>i \<in> s - {S} . push_bit i 1) = (\<Sum>i \<in> s . push_bit i 1) - (\<Sum>i \<in> {S} . push_bit i 1)"
  using assms apply auto by (simp add: sum.remove)

lemma map_set_bits:
  fixes v :: "'a::len word"
  assumes "bool_list = (map (\<lambda>i. bit v i) [0..<LENGTH('a)])"
  shows "\<forall> i . i < LENGTH('a) \<longrightarrow> (nth bool_list i \<longleftrightarrow> (i \<in> {n . bit v n}))"
  using assms by simp

lemma mask_range_64:
  fixes x :: "64word"
  assumes "x < 64"
  shows "(and x 63) = x"
proof -
  have "(63::64 word) = mask 6"
    by eval
  then show ?thesis
    by (metis assms inc_mask_eq_exp less_mask_eq numeral_plus_one semiring_norm(2,8))
qed

lemma mask_range_32:
  fixes x :: "64word"
  assumes "x < 32"
  shows "(and x 31) = x"
proof -
  have "(31::64 word) = mask 5"
    by eval
  then show ?thesis
    by (metis assms inc_mask_eq_exp less_mask_eq numeral_plus_one semiring_norm(2,8))
qed

text \<open>Shifting and $push_bit$ lemmas\<close>

lemma shift_succ: "\<forall> v i . (v << (Suc i)) = ((v << i) << 1)"
  unfolding shiftl_def by fastforce

lemma pow2_1_shift: "2 ^ j = 1 << j"
  by (simp add: shiftl_def)

lemma max_shift_pow2_minus_1: "((n :: ('a :: len) word) << LENGTH('a)) - 1 = (2 ^ LENGTH('a)) - 1"
  by (metis cancel_comm_monoid_add_class.diff_cancel right_diff_distrib word_exp_length_eq_0
      shiftl_power)

lemma max_minus_1_shift_pow2: "(1 :: ('a :: len) word) << (LENGTH('a) - 1) = 2 ^ (LENGTH('a) - 1)"
  by (simp add: pow2_1_shift)

lemma zero_shift: "(n :: ('a :: len) word) << 0 = n"
  unfolding shiftl_def by simp

lemma len_shift_zero: "(n :: ('a :: len) word) << LENGTH('a) = 0"
  unfolding shiftl_def by simp

lemma bit_shift_upper:
  fixes n :: "'a::len word"
  assumes "(i + j) < LENGTH('a)"
  shows "bit n i = bit (n << j) (i + j)"
  unfolding shiftl_def by (simp add: assms bit_push_bit_iff)

lemma bit_shift_overflow:
  fixes n :: "'a::len word"
  assumes "(i + j) \<ge> LENGTH('a)"
  shows "\<not>bit (n << j) (i + j)"
  unfolding shiftl_def using assms bit_imp_le_length leD by auto

lemma shift_zeros_below:
  fixes v :: "'a::len word"
  assumes "i < j"
  shows "\<not>bit (v << j) i"
proof -
  have "\<forall>n. \<not> bit (int (n << j)) i"
    by (metis assms bit_push_bit_iff_int push_bit_of_nat shiftl_def verit_comp_simplify1(3))
  then have "\<forall>n. \<not> bit (word_of_nat (n << j)::'a word) i"
    using bit_of_nat_iff bit_of_nat_iff_bit by blast
  then show ?thesis
    by (metis nat_add_zero of_nat_push_bit shiftl_def)
qed

lemma shift_zero_card: "card {n . bit 0 n} = card {n . bit (0 << i) n}"
  unfolding shiftl_def by simp

lemma non_shiftbit_unset: "\<forall> i . i \<noteq> j \<longrightarrow> \<not>bit (1 << j) i"
  by (metis bit_and_iff bit_iff_and_push_bit_not_eq_0 bit_unset_bit_iff shiftl_def)

lemma shift_set_implies_shiftbit: "bit ((1::'a::len word) << j) i \<Longrightarrow> i = j"
  using non_shiftbit_unset by auto

lemma bitset_shift_is_shift: "j < LENGTH('a) \<Longrightarrow> {n . bit ((1 << j)::('a::len) word) n} = {j}"
  using non_shiftbit_unset apply auto by (metis bit_1_0 bit_shift_upper plus_nat.add_0)

lemma card_shift_one: "j < LENGTH('a) \<Longrightarrow> card {n . bit ((1 << j)::('a::len) word) n} = 1"
  using bitset_shift_is_shift [of j] apply auto by fastforce

lemma shift_never_all_ones:
  fixes v :: "'a::len word"
  shows "\<forall> j . j > 0 \<longrightarrow> v << j \<noteq> -1"
  unfolding shiftl_def by (metis shift_zeros_below bit_lsb_set_in_all_ones shiftl_def)

lemma pow2_add_to_shift: "2 ^ j + 2 ^ k = (1 << j) + (1 << k)"
  by (simp add: pow2_1_shift)

lemma shift_one_def:
  fixes v :: "'a::len word"
  assumes "v = 1 << b"
  assumes "b < LENGTH('a)"
  shows "bit v b \<and> (\<forall> i . i \<noteq> b \<longrightarrow> \<not>bit v i)"
  by (metis add_0 assms bit_1_0 bit_shift_upper shift_set_implies_shiftbit)

lemma pow2_succ_eq_2shift: "(2::'a :: len word) ^ Suc i = (2 << i)"
  by simp

lemma push_bit_pos: "b < LENGTH('a) \<Longrightarrow> ((push_bit b 1)::'a::len word) > 0"
  apply (induction b; auto)
  by (metis exp_eq_zero_iff pow2_succ_eq_2shift verit_comp_simplify1(3) word_neq_0_conv)

text \<open>Power of 2 lemmas\<close>

lemma bitset_pow2_is_pow: "j < LENGTH('a) \<Longrightarrow> {n . bit ((2 ^ j)::('a::len) word) n} = {j}"
  unfolding pow2_1_shift by (simp add: bitset_shift_is_shift)

lemma card_pow2_one: "j < LENGTH('a) \<Longrightarrow> card {n . bit ((2 ^ j)::('a::len) word) n} = 1"
  by (simp add: pow2_1_shift card_shift_one)

lemma bitset_pow2_shift_eq:
  assumes "j < LENGTH('a)"
  shows "{n . bit ((2 ^ j)::('a::len) word) n} = {n . bit ((1 << j)::('a::len) word) n}"
  by (simp add: pow2_1_shift)

lemma pow2_even: "k > 0 \<Longrightarrow> bin_is_even (2 ^ k)"
  apply (induction k; auto)
  by (metis bot_nat_0.not_eq_extremum not_bit_numeral_Bit0_0 shift_zeros_below zero_shift)

text \<open>mask lemmas\<close>

lemma mask_geq_n_unset: "\<forall> i . i \<ge> n \<longrightarrow> \<not>bit ((mask n)::'a::len word) i"
  using bit_mask_iff linorder_not_less by blast

lemma mask_lt_n_set: "n \<le> LENGTH('a) \<Longrightarrow> \<forall> i . i < n \<longrightarrow> bit ((mask n)::'a::len word) i"
  using bit_mask_iff dual_order.strict_trans possible_bit_word by fastforce

lemma mask_succ_push_bit: "(mask n) + 1 = push_bit n 1"
  by (simp add: inc_mask_eq_exp)

lemma mask_lt_push_bit:
  assumes "n < LENGTH('a)"
  shows "mask n < ((push_bit n 1)::'a::len word)"
proof -
  have "(mask n) + 1 = push_bit n 1"
    by (simp add: mask_succ_push_bit)
  then have "(mask n) = (push_bit n 1) - 1"
    using add_implies_diff by blast
  then show ?thesis
    by (metis add_cancel_right_right antisym_conv3 assms mask_succ_push_bit push_bit_pos word_less_1
        word_not_simps(1) word_sub_less_iff)
qed

lemma mask_all_ones_iff:
  assumes "v \<le> LENGTH('a)"
  shows "(mask v::'a::len word) = (-1) \<longleftrightarrow> v = LENGTH('a)"
  by (smt (z3) minus_1_eq_mask nat_less_le negative_zle of_nat_mask_eq take_bit_minus_one_eq_mask
      signed_take_bit_eq signed_minus_1 assms)

lemma leq_mask_implies_lt_push_bit:
  assumes "n < LENGTH('a)"
  assumes "v \<le> mask n"
  shows "v < ((push_bit n 1)::'a::len word)"
  using assms order_le_less_trans mask_lt_push_bit by auto

lemma mask_lt:
  assumes "n \<le> LENGTH(64)"
  assumes "m < n"
  shows "((mask m)::64word) < ((mask n)::64word)"
  by (metis (no_types, lifting) assms dual_order.strict_trans1 mask_mono nless_le possible_bit_word
      bit_mask_iff)

lemma push_bit_gt_less_mask:
  assumes "n < LENGTH(64)"
  assumes "m < n"
  shows "((push_bit n 1)::64word) > ((mask m)::64word)"
proof -
  have m_lt_len: "m < LENGTH(64)"
    using assms by auto
  have "((push_bit m 1)::64word) - 1 < ((push_bit n 1)::64word)"
    by (metis add_diff_cancel assms diff_numeral_special(9) leq_mask_implies_lt_push_bit m_lt_len
        mask_succ_push_bit nat_less_le push_bit_pos word_less_imp_diff_less word_minus_one_le_leq
        mask_lt)
  then show ?thesis
    by (metis add_diff_cancel mask_succ_push_bit)
qed

text \<open>LENGTH lemmas\<close>

lemma lt_64_iff: "v < 64 \<longleftrightarrow> v < LENGTH(64)"
  by auto

lemma leq_64_iff: "v \<le> 64 \<longleftrightarrow> v \<le> LENGTH(64)"
  by auto

lemma len_64: "64 = LENGTH(64)"
  by auto

subsubsection \<open>Set lemmas\<close>

lemma card_eq:
  assumes "finite x \<and> finite y \<and> finite z"
  assumes "x \<union> y = z"
  assumes "y \<inter> x = {}"
  shows "card z - card y = card x"
  by (metis inf.commute card_Un_disjoint add_diff_cancel_right' assms)

lemma card_add:
  assumes "finite x \<and> finite y \<and> finite z"
  assumes "x \<union> y = z"
  assumes "y \<inter> x = {}"
  shows "card x + card y = card z"
  by (metis inf.commute assms card_Un_disjoint)

lemma card_add_inverses:
  assumes "finite {n. Q n \<and> \<not>(P n)} \<and> finite {n. Q n \<and> P n} \<and> finite {n. Q n}"
  shows "card {n. Q n \<and> P n} + card {n. Q n \<and> \<not>(P n)} = card {n. Q n}"
  apply (rule card_add) using assms by auto

lemma Max_range_upper:
  fixes lower :: nat
  assumes "lower < upper"
  shows "Max {lower..upper} = upper"
  by (metis atLeastatMost_empty_iff2 cSup_atLeastAtMost cSup_eq_Max finite_atLeastAtMost assms
      nat_less_le)

lemma Max_or_lt:
  fixes s :: "nat set"
  assumes "finite s"
  shows "\<forall> i . i \<in> s \<longrightarrow> i = Max s \<or> i < Max s"
  using Max_ge assms order_le_imp_less_or_eq by auto

lemma Min_or_gt:
  fixes s :: "nat set"
  assumes "finite s"
  shows "\<forall> i . i \<in> s \<longrightarrow> i = Min s \<or> i > Min s"
  using Min_le assms le_neq_implies_less by blast

lemma subset_sum:
  assumes "B \<subseteq> A"
  assumes "finite A"
  shows "(\<Sum>i \<in> A . f i) = ((\<Sum>i \<in> B . f i) + (\<Sum>i \<in> (A - B) . f i))"
  using assms by (simp add: add.commute sum.subset_diff)

lemma subset_property:
  assumes "\<forall> i . i \<in> S \<longrightarrow> P i"
  assumes "s \<subseteq> S"
  shows "\<forall> i . i \<in> s \<longrightarrow> P i"
  using assms(1,2) by auto

lemma distribute_sum_singular: "(\<Sum>i \<in> {A} . f i) = f A"
  unfolding sum_def
  by (metis add.right_neutral comm_monoid_add_class.sum_def finite.emptyI insert_absorb sum.empty
      sum.insert insert_not_empty)

subsubsection \<open>Range lemmas\<close>

lemma card_of_range: "x = card {n . 0 \<le> n \<and> n < x}"
  by simp

lemma range_of_nat: "{(n::nat) . 0 \<le> n \<and> n < x} = {n . n < x}"
  by simp

lemma finite_range: "finite {n::nat . n < x}"
  by simp

lemma range_eq:
  fixes x y :: nat
  shows "card {y..<x} = card {y<..x}"
  using card_atLeastLessThan card_greaterThanAtMost by presburger

lemma card_of_range_bound:
  fixes x y :: nat
  assumes "x > y"
  shows "x - y = card {n . y < n \<and> n \<le> x}"
proof -
  have simprep: "{n . y < n \<and> n \<le> x} = {y<..x}"
    by fastforce
  then show ?thesis
    unfolding simprep by fastforce
qed

subsection \<open>Long.highestOneBit\<close>

(* This is a different definition to Long.highestOneBit *)
definition highestOneBit :: "('a::len) word \<Rightarrow> int" where
  "highestOneBit v = MaxOrNeg {n. bit v n}"

lemma highestOneBitInvar: "highestOneBit v = j \<Longrightarrow> (\<forall>i::nat. (int i > j \<longrightarrow> \<not> (bit v i)))"
  apply (induction "size v"; auto) unfolding highestOneBit_def
  by (metis linorder_not_less MaxOrNeg_def empty_iff finite_bit_word mem_Collect_eq of_nat_mono
      Max_ge)

lemma highestOneBitNeg: "highestOneBit v = -1 \<longleftrightarrow> v = 0"
  unfolding highestOneBit_def MaxOrNeg_def
  by (metis Collect_empty_eq_bot bit_0_eq bit_word_eqI int_ops(2) negative_eq_positive one_neq_zero)

lemma highestOneBitN:
  assumes "bit v n"
  assumes "\<forall> i . (int i > n \<longrightarrow> \<not>(bit v i))"
  shows "highestOneBit v = n"
  unfolding highestOneBit_def MaxOrNeg_def
  by (metis Max_ge Max_in all_not_in_conv assms finite_bit_word mem_Collect_eq of_nat_less_iff
      order_less_le)

lemma highestOneBitSize:
  assumes "bit v n"
  assumes "n = size v"
  shows "highestOneBit v = n"
  by (metis assms higherBitsFalse highestOneBitN nat_int_comparison(2))

lemma highestOneBitMax: "highestOneBit v < size v"
  unfolding highestOneBit_def MaxOrNeg_def by (simp add: bit_imp_le_length size_word.rep_eq)

lemma highestOneBitAtLeast: "bit v n \<Longrightarrow> highestOneBit v \<ge> n"
  using highestOneBitInvar verit_comp_simplify1(3) by blast

lemma highestOneBitElim: "highestOneBit v = n \<Longrightarrow> ((n = -1 \<and> v = 0) \<or> (n \<ge> 0 \<and> bit v n))"
  unfolding highestOneBit_def MaxOrNeg_def
  by (metis Max_in finite_bit_word le0 le_minus_one_simps(3) mem_Collect_eq of_nat_0_le_iff
      of_nat_eq_iff)

lemma zerosAboveHighestOne: "n > highestOneBit a \<Longrightarrow> \<not>(bit a n)"
  unfolding highestOneBit_def MaxOrNeg_def
  by (metis (mono_tags, opaque_lifting) Collect_empty_eq Max_ge finite_bit_word less_le_not_le
      mem_Collect_eq of_nat_le_iff)

lemma "highestOneBit (0::64 word) = -1"
  by (simp add: MaxOrNeg_neg highestOneBit_def)

lemma highestOneBit_top: "Max {highestOneBit (v::64 word)} < 64"
  unfolding highestOneBit_def by (metis Max_singleton int_eq_iff_numeral max_set_bit size64)

lemma highestOneBit_gtzero_range: "(v::64 word) > 0 \<Longrightarrow> 0 \<le> highestOneBit v \<and> highestOneBit v < 64"
  subgoal premises p
proof -
  have bit_set: "\<exists> n . bit v n \<and> n \<ge> 0"
    using no_bits_implies_zero p by auto
  have geq0: "0 \<le> highestOneBit v"
    using bit_set zerosAboveHighestOne by force
  have "highestOneBit v < 64"
    by (metis of_nat_numeral size64 highestOneBitMax)
  then show ?thesis
    by (simp add: geq0)
qed
  done

text \<open>A recursive implementation of highestOneBit that is suitable for code generation.\<close>

fun highestOneBitRec :: "nat \<Rightarrow> ('a::len) word \<Rightarrow> int" where
  "highestOneBitRec n v =
    (if bit v n then n
     else if n = 0 then -1
     else highestOneBitRec (n - 1) v)"

lemma highestOneBitRecTrue: "highestOneBitRec n v = j \<Longrightarrow> j \<ge> 0 \<Longrightarrow> bit v j"
  using highestOneBitRec.simps apply auto apply (induction n)
  apply (metis less_minus_one_simps(1) of_nat_eq_iff of_nat_less_0_iff)
  by (metis (no_types, lifting) diff_Suc_1 highestOneBitRec.elims less_Suc_eq_0_disj of_nat_eq_iff
      less_numeral_extra(3))

lemma highestOneBitRecN: "bit v n \<Longrightarrow> highestOneBitRec n v = n"
  by simp

lemma highestOneBitRecMax: "highestOneBitRec n v \<le> n"
  by (induction n; simp)

lemma highestOneBitRecElim: "highestOneBitRec n v = j \<Longrightarrow> (j = -1 \<and> v = 0) \<or> (j \<ge> 0 \<and> bit v j)"
  using highestOneBitRecTrue by blast

lemma highestOneBitRecZero: "v = 0 \<Longrightarrow> highestOneBitRec (size v) v = -1"
  by (induction rule: "highestOneBitRec.induct"; simp)

lemma highestOneBitRecLess: "\<not>bit v n \<Longrightarrow> highestOneBitRec n v = highestOneBitRec (n - 1) v"
  by force

text \<open>Some lemmas that use masks to restrict highestOneBit
      and relate it to highestOneBitRec.\<close>

lemma highestOneBitMask: "size v = n \<Longrightarrow> highestOneBit v = highestOneBit (and v (mask n))"
  by (metis dual_order.refl lt2p_lem mask_eq_iff size_word.rep_eq)

lemma maskSmaller: "\<not>bit v n \<Longrightarrow> and v (mask (Suc n)) = and v (mask n)"
  unfolding bit_eq_iff by (metis bit_and_iff bit_mask_iff less_Suc_eq)

lemma highestOneBitSmaller:
  assumes "size v = Suc n"
  assumes "\<not>bit v n"
  shows "highestOneBit v = highestOneBit (and v (mask n))"
  by (metis assms highestOneBitMask maskSmaller)

lemma highestOneBitRecMask: "highestOneBit (and v (mask (Suc n))) = highestOneBitRec n v"
proof (induction n)
  case 0
  have "highestOneBit (and v (mask (Suc 0))) = highestOneBitRec 0 v"
    apply auto
    apply (smt (verit, ccfv_threshold) neg_equal_zero negative_eq_positive bit_1_iff bit_and_iff
           highestOneBitN)
    by (simp add: bit_iff_and_push_bit_not_eq_0 highestOneBitNeg)
  then show ?case
    by presburger
next
  case (Suc n)
  then show ?case
  proof (cases "bit v (Suc n)")
    case True
    have "\<forall>i::nat. (int i > (Suc n) \<longrightarrow> \<not> (bit (and v (mask (Suc (Suc n)))) i))"
      by (simp add: bit_and_iff bit_mask_iff)
    then have "highestOneBit (and v (mask (Suc (Suc n)))) = Suc n"
      by (metis bit_take_bit_iff lessI take_bit_eq_mask highestOneBitN True)
    then show ?thesis
      by (simp add: True)
  next
    case False
    then show ?thesis
      by (simp add: Suc maskSmaller)
  qed
qed

text \<open>Finally - we can use the mask lemmas to relate highestOneBitRec to its spec.\<close>

lemma highestOneBitImpl[code]: "highestOneBit v = highestOneBitRec (size v) v"
  by (metis highestOneBitMask highestOneBitRecMask maskSmaller not_bit_length wsst_TYs(3))

lemma "highestOneBit (0x5 :: int8) = 2" by code_simp

subsubsection \<open>Long.highestOneBit (v2)\<close>

text \<open>A highestOneBit definition mimicing the Long.java implementation\<close>

definition highestOneBit_long :: "('a::len) word \<Rightarrow> int" where
  "highestOneBit_long v = (let bit = highestOneBit v in (if (bit = -1) then 0 else (2 ^ nat bit)))"

lemma highestOneBit_long_pos:
  fixes v :: "'a::len word"
  shows "(highestOneBit_long v) \<ge> 0"
  unfolding highestOneBit_long_def apply (cases "highestOneBit v = (-1)") by simp+

subsection \<open>Long.lowestOneBit\<close>

definition lowestOneBit :: "('a::len) word \<Rightarrow> nat" where
  "lowestOneBit v = MinOrHighest {n . bit v n} (size v)"

lemma zerosBelowLowestOne:
  assumes "n < lowestOneBit a"
  shows "\<not>(bit a n)"
proof (cases "{i. bit a i} = {}")
  case True
  then show ?thesis
    by simp
next
  case False
  have "n < Min (Collect (bit a)) \<Longrightarrow> \<not> bit a n"
    using False by auto
  then show ?thesis
    by (metis False MinOrHighest_def assms lowestOneBit_def)
qed

lemma lowestOneBit_bot: "lowestOneBit (0::64 word) = 64"
  unfolding lowestOneBit_def MinOrHighest_def by (simp add: size64)

subsection \<open>Long.numberOfLeadingZeros\<close>

definition numberOfLeadingZeros :: "('a::len) word \<Rightarrow> nat" where
  "numberOfLeadingZeros v = nat (Nat.size v - highestOneBit v - 1)"

lemma "numberOfLeadingZeros (0::64 word) = 64"
  unfolding numberOfLeadingZeros_def by (simp add: highestOneBitImpl size64)

lemma numberOfLeadingZeros_top: "Max {numberOfLeadingZeros (v::64 word)} \<le> 64"
  unfolding numberOfLeadingZeros_def by (simp add: MaxOrNeg_def highestOneBit_def nat_le_iff size64)

lemma numberOfLeadingZeros_range:
  "0 \<le> numberOfLeadingZeros a \<and> numberOfLeadingZeros a \<le> Nat.size a"
  unfolding numberOfLeadingZeros_def apply auto
  apply (induction "highestOneBit a") unfolding highestOneBit_def MaxOrNeg_def by (linarith, auto)

lemma leadingZerosAddHighestOne: "numberOfLeadingZeros v + highestOneBit v = Nat.size v - 1"
  unfolding numberOfLeadingZeros_def highestOneBit_def
  using MaxOrNeg_def int_nat_eq int_ops(6) max_bit order_less_irrefl by fastforce

subsection \<open>Long.numberOfTrailingZeros\<close>

definition numberOfTrailingZeros :: "('a::len) word \<Rightarrow> nat" where
  "numberOfTrailingZeros v = lowestOneBit v"

lemma numberOfTrailingZeros_0: "numberOfTrailingZeros (0::64 word) = 64"
  unfolding numberOfTrailingZeros_def by (simp add: lowestOneBit_bot)

subsection \<open>Long.reverseBytes\<close>

(* Recursive version of reverseBytes for code generation *)
fun reverseBytes_fun :: "('a::len) word \<Rightarrow> nat \<Rightarrow> ('a::len) word \<Rightarrow> ('a::len) word" where
  "reverseBytes_fun v b flip = (if (b = 0) then (flip) else
                       (reverseBytes_fun (v >> 8) (b - 8) (or (flip << 8) (take_bit 8 v))))"

subsection \<open>Long.bitCount\<close>

definition bitCount :: "('a::len) word \<Rightarrow> nat" where
  "bitCount v = card {n . bit v n}"

(* Recursive version of bitCount for code generation *)
fun bitCount_fun :: "('a::len) word \<Rightarrow> nat \<Rightarrow> nat" where
  "bitCount_fun v n = (if (n = 0) then
                          (if (bit v n) then 1 else 0) else
                       if (bit v n) then (1 + bitCount_fun (v) (n - 1))
                                    else (0 + bitCount_fun (v) (n - 1)))"

lemma bitCount_0: "bitCount 0 = 0"
  unfolding bitCount_def by (metis card.empty zero_no_bits)

lemma bitCount_1: "bitCount 1 = 1"
  unfolding bitCount_def using bits_1_set card_1_singleton_iff by auto

lemma bitCount_range: "0 \<le> bitCount n \<and> bitCount n \<le> Nat.size n"
  unfolding bitCount_def
  by (metis bot_nat_0.extremum max_bit mem_Collect_eq subsetI subset_eq_atLeast0_lessThan_card
      atLeastLessThan_iff)

lemma card_bits_leq_len: "card {n . bit (v::'a::len word) n} \<le> LENGTH('a)"
  by (metis bitCount_def bitCount_range word_size)

lemma bitCount_all_ones: "bitCount (-1::('a::len) word) = LENGTH('a)"
  unfolding bitCount_def by (metis (no_types, lifting) Collect_cong negone_all_bits card_of_range)

lemma qualified_bitCount: "bitCount v = card {n . n < Nat.size v \<and> bit v n}"
  by (metis (no_types, lifting) Collect_cong bitCount_def max_bit)

lemma bitCount_card: "card {n . bit v n} = m \<Longrightarrow> bitCount v = m"
  unfolding bitCount_def by simp

lemma bitCount_card_set_equiv: "card {n . bit v n} = bitCount v"
  by (simp add: bitCount_card)

lemma bitCount_shift1: "j < LENGTH('a) \<Longrightarrow> bitCount ((1 :: 'a :: len word) << j) = 1"
  unfolding bitCount_def by (simp add: card_shift_one)

lemma bitCount_pow2: "j < LENGTH('a) \<Longrightarrow> bitCount ((2 :: 'a :: len word) ^ j) = 1"
  unfolding bitCount_def using card_pow2_one by blast

lemma bitCount_leq_len: "bitCount (v::'a::len word) \<le> LENGTH('a)"
  unfolding bitCount_def using card_bits_leq_len by blast

lemma bitCount_pos_implies_bit_set: "bitCount v > 0 \<Longrightarrow> \<exists> n . bit v n"
  by (metis bitCount_0 less_irrefl_nat no_bits_implies_zero)

lemma bitCount_pos_implies_highestOneBit_set:
  assumes "bitCount v > 0"
  shows "bit v (nat (highestOneBit v))"
proof -
  have "\<exists> n . bit v n"
    by (simp add: assms bitCount_pos_implies_bit_set)
  then show ?thesis
    using highestOneBitAtLeast highestOneBitElim by force
qed

lemma bitCount_1_equiv:
  fixes v :: "'a::len word"
  shows "bitCount v = 1 \<longleftrightarrow> (\<exists> b . {n . bit v n} = {b})"
  by (metis bitCount_card_set_equiv is_singletonI is_singleton_altdef is_singleton_the_elem)

subsubsection \<open> bitSum - a summation-based implementation of bitCount \<close>

definition bitSum :: "'a::len word \<Rightarrow> nat" where
  "bitSum v = (\<Sum>i=0::nat..LENGTH('a)-1 . (if bit v i then 1 else 0))"

lemma bitSum_all_ones_len: "bitSum (-1::'a::len word) = LENGTH('a)"
  unfolding bitSum_def by auto

lemma bitSum_zero: "bitSum (0::'a::len word) = 0"
  unfolding bitSum_def by auto

subsection \<open>Long.zeroCount\<close>

definition zeroCount :: "('a::len) word \<Rightarrow> nat" where
  "zeroCount v = card {n . n < Nat.size v \<and> \<not>(bit v n)}"

lemma zeroCount_finite: "finite {n. n < Nat.size v \<and> \<not>(bit v n)}"
  using finite_nat_set_iff_bounded by blast

lemma ones_zero_sum_to_width: "bitCount a + zeroCount a = Nat.size a"
proof -
  have add_cards: "card {n. (\<lambda>n. n < size a) n \<and> (bit a n)} +
                   card {n. (\<lambda>n. n < size a) n \<and> \<not>(bit a n)} = card {n. (\<lambda>n. n < size a) n}"
    apply (rule card_add_inverses) by simp
  then have "... = Nat.size a"
    by auto
  then show ?thesis
    unfolding bitCount_def zeroCount_def by (simp add: add_cards bits_bound_eq)
qed

lemma intersect_bitCount_helper:
  "card {n . n < Nat.size a} - bitCount a = card {n . n < Nat.size a \<and> \<not>(bit a n)}"
  by (metis card_Collect_less_nat diff_add_inverse ones_zero_sum_to_width zeroCount_def)

lemma intersect_bitCount: "Nat.size a - bitCount a = card {n . n < Nat.size a \<and> \<not>(bit a n)}"
  using card_of_range intersect_bitCount_helper by auto

hide_fact intersect_bitCount_helper

subsection \<open> Word definitions and properties \<close>

definition bin_log2 :: "'a::len word \<Rightarrow> nat" where
  "bin_log2 v = (LENGTH('a) - 1 - numberOfLeadingZeros v)"

text \<open> bitCount = 2 ==> {i . bit v i} = {lowestSetBit, highestSetBit} \<close>

lemma bin_log2_highestOneBit_eq_64:
  fixes v :: "64word"
  assumes "v > 0"
  shows "bin_log2 v = highestOneBit v"
  using assms unfolding bin_log2_def numberOfLeadingZeros_def apply auto
  subgoal premises p
  proof -
    have size_v: "int (size_class.size v) = 64"
      by (simp add: size64)
    have "int (63 - nat (63 - highestOneBit v)) = highestOneBit v"
      using highestOneBit_gtzero_range [of v] assms by linarith
    then show ?thesis
      by (simp add: size_v)
  qed
  done


lemma sum_eq_card:
  fixes N :: nat
  shows "(\<Sum>i=0..N. of_bool (P i)) = card {i. 0 \<le> i \<and> i \<le> N \<and> P i}"
proof -
  have fin: "finite {0..N}" by simp
  have set_eq: "{i. 0 \<le> i \<and> i \<le> N \<and> P i} = {0..N} \<inter> {i. P i}"
    by auto
  have "(\<Sum>i=0..N. of_bool (P i)) = (\<Sum>i=0..N. if P i then 1 else 0)"
    by (simp add: of_bool_def)
  also have "\<dots> = (\<Sum>i \<in> {0..N} \<inter> {i. P i}. (1::nat))
                 + (\<Sum>i \<in> {0..N} \<inter> {i. \<not> P i}. 0)"
    using sum.If_cases
    by (smt (verit, best) fin group_cancel.rule0 mem_Collect_eq sum.cong sum.inter_restrict sum.neutral_const)
  also have "\<dots> = (\<Sum>i \<in> {0..N} \<inter> {i. P i}. (1::nat))"
    by simp
  also have "\<dots> = card ({0..N} \<inter> {i. P i})"
    by auto
  also have "\<dots> = card {i. 0 \<le> i \<and> i \<le> N \<and> P i}"
    using set_eq by simp
  finally show ?thesis .
qed

section \<open>Bounded Rings\<close>

text \<open>
Extending the @{locale ring_bit_operations} locale to be bounded by some limit.
On machine words for example, this is the word width.
\<close>

locale bounded_ring_bit_operations = ring_bit_operations +
  fixes bound :: "'a \<Rightarrow> nat"
  assumes bounded: "\<forall>i > bound w. \<not>(bit w i)"
begin

lemma finite_bits: "finite {i. bit w i}"
  by (metis bounded finite_Collect_le_nat finite_subset linorder_le_less_linear mem_Collect_eq subsetI)

end

subsection \<open>Support\<close>

text \<open>
Defining a function, supp, that provides the set of all set (on) bits.
@{url "https://en.wikipedia.org/wiki/Support_(mathematics)"}
\<close>

context bounded_ring_bit_operations
begin

definition supp :: "'a \<Rightarrow> nat set" where
  "supp w = {i. bit w i}"

lemma supp_finite: "finite (supp w)"
  unfolding supp_def by (rule finite_bits)

lemma supp_zero: "supp zero = {}"
  unfolding supp_def by simp

lemma supp_one: "supp one = {0}"
  unfolding supp_def using local.bit_1_iff by auto

lemma supp_eq_iff: "a = b \<longleftrightarrow> supp a = supp b"
  unfolding supp_def by (metis local.bit_eq_iff mem_Collect_eq)

lemma supp_and: "supp (and a b) = supp a \<inter> supp b"
  unfolding supp_def by (auto simp: local.bit_and_iff)

lemma supp_or: "supp (or a b) = supp a \<union> supp b"
  unfolding supp_def by (auto simp: local.bit_or_iff)

lemma supp_xor: "supp (xor a b) = (supp a - supp b) \<union> (supp b - supp a)"
  unfolding supp_def by (auto simp: local.bit_xor_iff)

lemma supp_subset: "supp w \<subseteq> {0..bound w}"
  unfolding supp_def using bounded apply auto using linorder_le_less_linear by auto

lemma supp_unset: "{0..bound w} - (supp w) = {i. \<not>bit w i} \<inter> {0..bound w}"
  using supp_def by auto

definition inverse :: "nat set \<Rightarrow> nat \<Rightarrow> nat set" where
  "inverse s b = {i \<in> {0..b} . i \<notin> s}"

(*
lemma supp_not: "supp (not w) = inverse (supp w) (bound w)"
  unfolding supp_def inverse_def using bit_not_iff  sorry

lemma supp_push_bit: "supp (push_bit n w) = {i + n | i . i \<in> supp w}"
  unfolding supp_def using bit_push_bit_iff sorry

lemma supp_subtract:
  assumes "supp b \<subset> supp a"
  shows "supp (minus a b) = (supp a - supp b)"
  sorry
*)

end

section \<open>Population Count\<close>

text \<open>The `pop' of a word, the count of set bits.\<close>

locale bit_count = bounded_ring_bit_operations
begin

definition bitCount :: "'a \<Rightarrow> nat" where
  "bitCount w = card (supp w)"

lemma bc: "bitCount w = (\<Sum>i=0..bound w. of_bool (bit w i))"
proof -
  have "{i. bit w i} = ({i. i \<le> bound w \<and> bit w i} \<union> {i. i > bound w \<and> bit w i})"
    by fastforce
  also have "{i. i > bound w \<and> bit w i} = {}"
    using bounded by blast
  ultimately have set_eq: "{i. bit w i} = {i. 0 \<le> i \<and> i \<le> bound w \<and> bit w i}"
    by blast
  then show ?thesis using sum_eq_card
    using local.bitCount_def supp_def by presburger
qed

lemma of_bool: "of_bool a = (if a then 1 else 0)"
  by auto

lemma count_zero: "bitCount zero = 0"
  using bc by fastforce

lemma count_one: "bitCount one = 1"
  unfolding bc of_bool using bit_1_iff by simp

lemma count_union_inter:
  "bitCount (or a b) + bitCount (and a b) = bitCount a + bitCount b"
  by (metis card_Un_Int local.bitCount_def supp_and supp_finite supp_or)

lemma card_count: "bitCount w = card {i. bit w i}"
proof -
  have "{i. bit w i} = ({i. i \<le> bound w \<and> bit w i} \<union> {i. i > bound w \<and> bit w i})"
    by fastforce
  also have "{i. i > bound w \<and> bit w i} = {}"
    using bounded by blast
  ultimately have set_eq: "{i. bit w i} = {i. 0 \<le> i \<and> i \<le> bound w \<and> bit w i}"
    by blast
  then show ?thesis unfolding bc using sum_eq_card
    by (metis (no_types, lifting) ext)
qed

lemma power_of_two_ex:
  assumes "bitCount w = 1"
  shows "\<exists>n. w = push_bit n one"
proof -
  obtain n where "bit w n"
    using assms card_count
    by force
  then have "{i. bit w i} = {n}"
    using assms card_count
    by (metis card_1_singletonE mem_Collect_eq singletonD)
  then have "\<forall> i. bit w i \<longleftrightarrow> i = n"
    by blast
  then have "w = push_bit n one"
    using bit_exp_iff local.bit_eq_iff by auto
  then show ?thesis by blast
qed
end

locale bit_top_bot = bounded_ring_bit_operations
begin

definition topBit :: "'a \<Rightarrow> nat" ("\<top>") where
  "topBit w = Max (supp w)"
definition botBit :: "'a \<Rightarrow> nat" ("\<bottom>") where
  "botBit w = Min (supp w)"

definition ntz :: "'a \<Rightarrow> nat" where "ntz w = \<bottom> w"
definition nlz :: "'a \<Rightarrow> nat" where "nlz w = bound w - \<top> w"

definition highestOneBit :: "'a \<Rightarrow> 'a" where
  "highestOneBit w = push_bit (\<top> w) one"

definition lowestOneBit :: "'a \<Rightarrow> 'a" where
  "lowestOneBit w = push_bit (\<bottom> w) one"

lemma top_one: "\<top> one = 0"
  using topBit_def supp_def bit_1_iff by simp

lemma bot_one: "\<bottom> one = 0"
  using botBit_def supp_def bit_1_iff by simp

lemma top_set: 
  assumes "w \<noteq> zero"
  shows "bit w (\<top> w)"
  using assms finite_bits unfolding topBit_def supp_def
  by (metis Collect_empty_eq_bot Max_in local.bit_0_eq local.bit_eq_iff mem_Collect_eq)

lemma bot_set: "w \<noteq> zero \<Longrightarrow> bit w (\<bottom> w)"
  using finite_bits unfolding botBit_def supp_def
  using Min_in top_set by auto

lemma above_top_unset:
  "i > \<top> w \<Longrightarrow> \<not>(bit w i)"
  by (metis empty_def eq_Max_iff finite_bits topBit_def supp_def linorder_not_less mem_Collect_eq)

lemma below_bot_unset:
  "i < \<bottom> w \<Longrightarrow> \<not>(bit w i)"
  by (metis Min_gr_iff bex_empty finite_bits less_irrefl botBit_def supp_def mem_Collect_eq)

lemma or_eq_add_disjoint:
  assumes "supp a \<inter> supp b = {}"
  shows "or a b = plus a b"
  by (simp add: assms local.disjunctive_add_eq_or supp_and supp_eq_iff supp_zero)

subsection \<open>Subtraction\<close>
(*lemma below_sub_allset:
  "i < \<bottom> w \<Longrightarrow> bit (minus w one) i"
  sorry

lemma below_sub_unset:
  "\<not>(bit (minus w one) (\<bottom> w))"
proof -
  have "minus w one = not (uminus w)"
    by (simp add: local.minus_eq_not_minus_1)
  also have "bit (uminus w) (\<bottom> w)"
    using bit_minus_iff sorry
  ultimately show ?thesis
    using local.bit_minus_iff by blast
qed*)

end

locale bit_inspection = bit_count + bit_top_bot + comm_monoid_add
begin
lemma one_bit:
  assumes "bitCount w = 1"
  shows "\<bottom> w = \<top> w"
  by (metis assms bot_set count_zero local.bit_exp_iff local.push_bit_of_1 power_of_two_ex top_set
      zero_neq_one_class.zero_neq_one)

(*lemma two_bit:
  assumes "bitCount w = 2"
  shows "w = plus (push_bit (\<top> w) one) (push_bit (\<bottom> w) one)"
proof -
  (*have "w = (\<Sum>i=0..bound w. push_bit i one)"*)
  obtain k j where set: "{i. bit w i} = {k, j}"
    using assms unfolding bc
    by (metis assms card_2_iff card_count)
  then have wsum: "w = plus (push_bit k one) (push_bit j one)"
    sorry
  from set have "{k, j} = {\<top> w, \<bottom> w}"
    using hsb lsb by force
  then show ?thesis using assms unfolding bc wsum unfolding hsb lsb
    by (metis add_commute doubleton_eq_iff)
qed*)

lemma power_of_two:
  assumes "bitCount w = 1"
  shows "w = push_bit (\<top> w) one"
  using assms bc
  by (metis bot_set count_zero local.bit_exp_iff local.push_bit_of_1 one_bit power_of_two_ex
      zero_neq_one_class.zero_neq_one)

end

definition bitCountSum :: "'a::len word \<Rightarrow> nat" where
  "bitCountSum w = (\<Sum>i=0..LENGTH('a). of_bool (bit w i))"
definition topBit :: "'a::len word \<Rightarrow> nat" where
  "topBit w = Max {i . bit w i}"
definition botBit :: "'a::len word \<Rightarrow> nat" where
  "botBit w = Min {i . bit w i}"

interpretation word_inspection: bit_inspection "(+)" "(-)" "0" "(*)" "1" "(div)" "(mod)" 
  "bit" "and" "or" "xor" "mask" "set_bit" "unset_bit" "flip_bit"
  "push_bit" "drop_bit" "take_bit" "uminus" "not" "(\<lambda>w::'a::len word. (LENGTH('a)))"
  apply standard
  apply (simp add: bit_word.rep_eq)
  done

section \<open>@{locale bit_inspection} lemmas\<close>

text \<open>POC: @{locale bit_inspection} lemmas can be used for optimizations\<close>

lemma single_bit_shift_one:
  fixes v :: "'a::len word"
  assumes "{n . bit v n} = {b}"
  shows "v = 1 << b"
  by (metis assms bit_imp_le_length bits_same_set_implies_val_same bitset_shift_is_shift
      single_bit_set)

subsection \<open>supp lemmas\<close>

lemma supp_range:
  fixes v :: "'a::len word"
  shows "\<forall> i . i \<in> word_inspection.supp v \<longrightarrow> 0 \<le> i \<and> i < LENGTH('a)"
  unfolding word_inspection.supp_def by (simp add: bits_set_in_range)

lemma supp_push_bit_sum:
  fixes v :: "'a::len word"
  shows "v = (\<Sum>i \<in> (word_inspection.supp v) . (push_bit i 1))"
proof -
  have subs: "word_inspection.supp v \<subseteq> {0..LENGTH('a)}"
    by (simp add: word_inspection.supp_subset)
  have v: "v = (\<Sum>i=0..LENGTH('a) . of_bool (bit v i) * (push_bit i 1))"
    by (metis (mono_tags, lifting) sum_word_rewrite horner_sum_word_push_bit)
  have split: "... =
      (\<Sum>i \<in> word_inspection.supp v . (of_bool (bit v i) * push_bit i 1)) +
      (\<Sum>i \<in> ({0..LENGTH('a)} - word_inspection.supp v) . (of_bool (bit v i) * push_bit i 1))"
    using subset_sum word_inspection.supp_finite subs by blast
  have "(\<Sum>i \<in> ({0..LENGTH('a)} - word_inspection.supp v) . (of_bool (bit v i) * push_bit i 1)) = 0"
    unfolding word_inspection.supp_def by simp
  then show ?thesis
    by (smt (verit) v add_cancel_right_right mem_Collect_eq mult_1 of_bool_eq(2) sum.cong split
        word_inspection.supp_def)
qed

lemma supp_nonzero_nonempty_iff: "v \<noteq> 0 \<longleftrightarrow> word_inspection.supp v \<noteq> {}"
  unfolding word_inspection.supp_def using word_inspection.bot_set by force

lemma supp_zero_empty_iff: "v = 0 \<longleftrightarrow> word_inspection.supp v = {}"
  unfolding word_inspection.supp_def using no_bits_implies_zero by auto

lemma supp_all_ones_iff:
  fixes v :: "'a::len word"
  shows "word_inspection.supp v = {0..LENGTH('a)-1} \<longleftrightarrow> (-1::'a::len word) = v"
proof -
  have "{n . 0 \<le> n \<and> n < LENGTH('a)} = {0..LENGTH('a)-1}"
    by auto
  then show ?thesis
    unfolding word_inspection.supp_def by (metis bits_same_set_implies_val_same negone_all_bits)
qed

lemma supp_mask:
  fixes v :: "'a::len word"
  assumes "v = ((mask n)::'a::len word)"
  assumes "n > 0"
  assumes "n \<le> LENGTH('a)"
  shows "word_inspection.supp v = {0..n-1}"
proof -
  have "word_inspection.supp ((mask n)::'a::len word) = {0..n-1}"
    unfolding word_inspection.supp_def apply auto
    apply (metis Suc_pred assms(2) mask_geq_n_unset not_less_eq_eq)
    using assms(2,3) mask_lt_n_set by fastforce
  then show ?thesis
    using assms(1) by blast
qed

lemma supp_max_topBit: "topBit v = Max (word_inspection.supp v)"
  by (simp add: topBit_def word_inspection.supp_def)

lemma supp_min_botBit: "botBit v = Min (word_inspection.supp v)"
  by (simp add: botBit_def word_inspection.supp_def)

lemma supp_contains_topBit_nonzero_iff: "v \<noteq> 0 \<longleftrightarrow> topBit v \<in> word_inspection.supp v"
  by (metis Max_in emptyE supp_max_topBit supp_nonzero_nonempty_iff word_inspection.supp_finite)

lemma supp_contains_botBit_nonzero_iff: "v \<noteq> 0 \<longleftrightarrow> botBit v \<in> word_inspection.supp v"
  by (metis Min_in emptyE supp_min_botBit supp_nonzero_nonempty_iff word_inspection.supp_finite)

lemma supp_leq_topBit:
  assumes "v \<noteq> 0"
  shows "\<forall> b . b \<in> word_inspection.supp v \<longrightarrow> b \<le> topBit v"
proof (cases "word_inspection.supp v = {topBit v}")
  case True
  then show ?thesis
    unfolding topBit_def word_inspection.supp_def by simp
next
  case False
  have "\<forall> i . i \<in> word_inspection.supp v \<longrightarrow> i = Max (word_inspection.supp v) \<or>
                                             i < Max (word_inspection.supp v)"
    using Max_or_lt [of "word_inspection.supp v"] word_inspection.supp_finite by blast
  then show ?thesis
    unfolding topBit_def word_inspection.supp_def by simp
qed

lemma supp_geq_botBit:
  assumes "v \<noteq> 0"
  shows "\<forall> b . b \<in> word_inspection.supp v \<longrightarrow> b \<ge> botBit v"
proof (cases "word_inspection.supp v = {botBit v}")
  case True
  then show ?thesis
    unfolding botBit_def word_inspection.supp_def by fastforce
next
  case False
  have "\<forall> i . i \<in> word_inspection.supp v \<longrightarrow> i = Min (word_inspection.supp v) \<or>
                                             i > Min (word_inspection.supp v)"
    using Min_or_gt [of "word_inspection.supp v"] word_inspection.supp_finite by blast
  then show ?thesis
    unfolding botBit_def word_inspection.supp_def by simp
qed

lemma supp_singular_is_topBit: "word_inspection.supp v = {S} \<Longrightarrow> S = topBit v"
  unfolding word_inspection.supp_def topBit_def by simp

lemma supp_singular_is_botBit: "word_inspection.supp v = {S} \<Longrightarrow> S = botBit v"
  unfolding word_inspection.supp_def botBit_def by simp

lemma supp_singular_imp_botBit_eq_topBit: "word_inspection.supp v = {S} \<Longrightarrow> botBit v = topBit v"
  unfolding word_inspection.supp_def botBit_def topBit_def by auto

lemma supp_single_bit_less:
  fixes a b :: "'a::len word"
  assumes "S \<in> word_inspection.supp a"
  assumes "word_inspection.supp b = word_inspection.supp a - {S}"
  shows "b = a - (push_bit S 1)"
proof -
  have a_sum: "a = (\<Sum>i \<in> (word_inspection.supp a) . (push_bit i 1))"
    using supp_push_bit_sum by auto
  have b_sum: "b = (\<Sum>i \<in> (word_inspection.supp b) . (push_bit i 1))"
    using supp_push_bit_sum by auto
  then have "... = (\<Sum>i \<in> word_inspection.supp a - {S} . (push_bit i 1))"
    using assms(2) by presburger
  then have distribute_sub: "... = (\<Sum>i \<in> word_inspection.supp a . (push_bit i 1)) -
                                   (\<Sum>i \<in> {S} . (push_bit i 1))"
    using sum_push_bit_distrib_sub assms(1) word_inspection.supp_finite by blast
  then have "... = a - push_bit S 1"
    using a_sum by force
  then show ?thesis
    using assms distribute_sub b_sum by presburger
qed

lemma supp_sum_minus_subset:
  fixes v :: "'a::len word"
  assumes "S \<subset> word_inspection.supp v"
  assumes "v > 0"
  shows "v = (\<Sum>i \<in> (word_inspection.supp v - S) . (push_bit i 1)) + (\<Sum>i \<in> S . (push_bit i 1))"
  using supp_push_bit_sum [of v]
  by (metis add.commute assms(1) inf.absorb4 sum.Int_Diff word_inspection.supp_finite)

lemma supp_set_less:
  fixes a b :: "'a::len word"
  assumes "S \<subset> word_inspection.supp v"
  assumes "v > 0"
  assumes "word_inspection.supp b = word_inspection.supp v - S"
  shows "b = v - (\<Sum>i \<in> S . (push_bit i 1))"
  by (metis supp_sum_minus_subset add_diff_cancel_right' assms supp_push_bit_sum)

subsection \<open>bitCount lemmas\<close>

lemma bitCount_1_shift:
  assumes "bitCount w = 1"
  shows "w = 1 << topBit w"
  by (metis bitCount_card_set_equiv pow2_1_shift push_bit_of_1 topBit_def word_inspection.card_count
      word_inspection.power_of_two word_inspection.supp_def word_inspection.topBit_def assms)

lemma bitCount_2_lsb_msb:
  fixes v :: "'a::len word"
  assumes "bitCount v = 2"
  shows "{n . bit v n} = {topBit v, botBit v}"
proof -
  have twoBits: "\<exists> j k . {n . bit v n} = {j, k}"
    using assms unfolding bitCount_def by (meson card_2_iff)
  have topAlwaysIn: "topBit v \<in> {n . bit v n}"
    by (metis Max_in bits_finite insert_not_empty topBit_def twoBits)
  have botAlwaysIn: "botBit v \<in> {n . bit v n}"
    by (metis twoBits supp_contains_botBit_nonzero_iff word_inspection.supp_def zero_empty_bits
        insert_not_empty)
  then show ?thesis
    using twoBits topAlwaysIn apply auto
    by (metis (no_types, lifting) Max.coboundedI Min.coboundedI bits_finite botBit_def insert_iff
        mem_Collect_eq order_antisym_conv singleton_iff topBit_def)
qed

lemma bitCount_2_supp:
  fixes v :: "'a::len word"
  assumes "bitCount v = 2"
  shows "word_inspection.supp v = {topBit v, botBit v}"
  using bitCount_2_lsb_msb word_inspection.supp_def assms by auto

lemma bitCount_2_sum_push_bit:
  fixes v :: "'a::len word"
  assumes "bitCount v = 2"
  shows "v = push_bit (topBit v) 1 + push_bit (botBit v) 1"
proof -
  have supp: "word_inspection.supp v = {topBit v, botBit v}"
    using bitCount_2_supp assms by meson
  have topBotDiff: "topBit v \<noteq> botBit v"
    by (metis assms bitCount_1_equiv insert_absorb2 semiring_norm(83) supp word_inspection.supp_def
        numeral_eq_one_iff)
  have suppSum: "v = (\<Sum>i \<in> (word_inspection.supp v) . (push_bit i 1))"
    using supp_push_bit_sum by blast
  have suppTopBot: "... = (\<Sum>i \<in> {topBit v, botBit v} . (push_bit i 1))"
    by (simp add: supp)
  have distribute: "... = (\<Sum>i \<in> {botBit v} . (push_bit i 1)) + (\<Sum>i \<in> {topBit v} . (push_bit i 1))"
    using topBotDiff by auto
  have "... = push_bit (topBit v) 1 + push_bit (botBit v) 1"
    by simp
  then show ?thesis
    using suppTopBot distribute suppSum by argo
qed

lemma bitCount_2_sum_pow_2:
  fixes v :: "'a::len word"
  assumes "bitCount v = 2"
  shows "v = 2 ^ (topBit v) + 2 ^ (botBit v)"
  using assms bitCount_2_sum_push_bit by auto

lemma bitCount_2_sum_shift_1:
  fixes v :: "'a::len word"
  assumes "bitCount v = 2"
  shows "v = 1 << (topBit v) + 1 << (botBit v)"
  by (metis assms bitCount_2_sum_pow_2 pow2_1_shift)

lemma bitCount_2_mul_distribute:
  fixes v :: "'a::len word"
  assumes "bitCount v = 2"
  shows "x * v = x << (topBit v) + x << (botBit v)"
  using assms unfolding bitCount_def
  by (metis (no_types, lifting) bitCount_2_sum_shift_1 pow2_1_shift push_bit_eq_mult shiftl_def
      assms ring_class.ring_distribs(1))

subsection \<open>topBit lemmas\<close>

lemma topBit_higher_unset:
  assumes "v \<noteq> 0"
  shows "\<forall> i . i > topBit v \<longrightarrow> \<not>bit v i"
proof -
  have "\<forall> b . b \<in> word_inspection.supp v \<longrightarrow> b \<le> topBit v"
    using supp_leq_topBit assms by auto
  then show ?thesis
    by (simp add: supp_max_topBit word_inspection.above_top_unset word_inspection.topBit_def)
qed

lemma topBit_in_range:
  fixes v :: "'a::len word"
  assumes "v \<noteq> 0"
  shows "topBit v \<le> LENGTH('a) - 1"
proof -
  have "topBit v \<in> word_inspection.supp v"
    using assms supp_contains_topBit_nonzero_iff by auto
  then show ?thesis
    using supp_range by auto
qed

lemma topBit_0_imp_1:
  fixes v :: "'a::len word"
  assumes "v \<noteq> 0"
  assumes "topBit v = 0"
  shows "v = 1"
  by (metis assms le0 nle_le supp_leq_topBit upper_bits_unset_implies_0_1 word_inspection.supp_def
      mem_Collect_eq)

lemma unfold_topBit_64:
  fixes yv :: "64word"
  assumes "bitCount yv = 2"
  shows "unat (and (word_of_nat (topBit yv)) (63::64 word)) = topBit yv"
proof -
  have mask: "(63::64 word) = mask 6"
    by eval
  have "63 = LENGTH(64) - 1"
    by auto
  then have range: "topBit yv \<le> 63"
    by (metis topBit_in_range assms bitCount_0 zero_neq_numeral)
  obtain max where maxInSet: "max = topBit yv"
    by simp
  have word_range: "(word_of_nat (max)::64word) \<le> 63"
    by (simp add: local.range maxInSet word_of_nat_leq_len_1_64)
  have lt_pow2: "(topBit yv) < (2 ^ LENGTH(64))"
    using range by auto
  have foldAnd: "(and (word_of_nat (max)::64word) (63::64 word)) = (word_of_nat (max)::64word)"
    using and_mask_eq_iff_le_mask by (metis mask word_range)
  have "unat (word_of_nat (max)::64word) = max"
    using lt_pow2 unat_word_of_nat_unfold_64 maxInSet by blast
  then show ?thesis
    using foldAnd maxInSet by auto
qed

subsection \<open>botBit lemmas\<close>

lemma botBit_lower_unset:
  assumes "v \<noteq> 0"
  shows "\<forall> i . i < botBit v \<longrightarrow> \<not>bit v i"
proof -
  have "\<forall> b . b \<in> word_inspection.supp v \<longrightarrow> b \<ge> botBit v"
    by (simp add: assms supp_geq_botBit)
  then show ?thesis
    by (simp add: supp_min_botBit word_inspection.below_bot_unset word_inspection.botBit_def)
qed

lemma botBit_in_range:
  fixes v :: "'a::len word"
  assumes "v \<noteq> 0"
  shows "botBit v \<le> LENGTH('a) - 1"
proof -
  have "botBit v \<in> word_inspection.supp v"
    using assms supp_contains_botBit_nonzero_iff by auto
  then show ?thesis
    using supp_range by auto
qed

lemma unfold_botBit_64:
  fixes yv :: "64word"
  assumes "bitCount yv = 2"
  shows "unat (and (word_of_nat (botBit yv)) (63::64 word)) = (botBit yv)"
proof -
  have mask: "(63::64 word) = mask 6"
    by eval
  have "63 = LENGTH(64) - 1"
    by auto
  then have range: "botBit yv \<le> 63"
    by (metis botBit_in_range assms bitCount_0 less_numeral_extra(3) pos2)
  obtain min where minInSet: "min = botBit yv"
    by simp
  have word_range: "(word_of_nat (min)::64word) \<le> 63"
    by (simp add: local.range minInSet word_of_nat_leq_len_1_64)
  have lt_pow2: "(botBit yv) < (2 ^ LENGTH(64))"
    using range by auto
  have foldAnd: "(and (word_of_nat (min)::64word) (63::64 word)) = (word_of_nat (min)::64word)"
    by (metis and_mask_eq_iff_le_mask mask word_range)
  have "unat (word_of_nat (min)::64word) = min"
    using lt_pow2 unat_word_of_nat_unfold_64 minInSet by blast
  then show ?thesis
    using foldAnd minInSet by auto
qed

end