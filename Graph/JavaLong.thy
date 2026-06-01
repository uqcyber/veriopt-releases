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

lemma size_len_eq:
  fixes v :: "'a::len word"
  shows "LENGTH('a) = Nat.size v"
  by (simp add: size_word.rep_eq)

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
  shows "i > size v \<Longrightarrow> \<not> (bit v i)"
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

lemma empty_zero_bits: "{i . bit v i} = {} \<Longrightarrow> \<forall>i . \<not>bit v i"
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

lemma upper_bits_unset_implies_0_1:
  assumes "\<forall> i . i \<noteq> 0 \<longrightarrow> \<not>bit v i"
  shows "v = 0 \<or> v = 1"
  by (metis assms bit_1_iff bits_same_implies_val_same no_bits_implies_zero)

text \<open>Shifting lemmas\<close>

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

lemma bitset_shift_is_shift:
  assumes "j < LENGTH('a)"
  shows "{n . bit ((1 << j)::('a::len) word) n} = {j}"
  using non_shiftbit_unset apply auto by (metis assms bit_1_0 bit_shift_upper plus_nat.add_0)

lemma card_shift_one:
  assumes "j < LENGTH('a)"
  shows "card {n . bit ((1 << j)::('a::len) word) n} = 1"
  using bitset_shift_is_shift [of j] apply auto using assms by fastforce

lemma shift_never_all_ones:
  fixes v :: "'a::len word"
  shows "\<forall> j . j > 0 \<longrightarrow> v << j \<noteq> -1"
  unfolding shiftl_def by (metis shift_zeros_below bit_lsb_set_in_all_ones shiftl_def)

text \<open>Power of 2 lemmas\<close>

lemma bitset_pow2_is_pow:
  assumes "j < LENGTH('a)"
  shows "{n . bit ((2 ^ j)::('a::len) word) n} = {j}"
  unfolding pow2_1_shift by (simp add: assms bitset_shift_is_shift)

lemma card_pow2_one:
  assumes "j < LENGTH('a)"
  shows "card {n . bit ((2 ^ j)::('a::len) word) n} = 1"
  by (simp add: assms pow2_1_shift card_shift_one)

lemma bitset_pow2_shift_eq:
  assumes "j < LENGTH('a)"
  shows "{n . bit ((2 ^ j)::('a::len) word) n} = {n . bit ((1 << j)::('a::len) word) n}"
  by (simp add: pow2_1_shift)

lemma pow2_even:
  assumes "k > 0"
  shows "bin_is_even (2 ^ k)"
  using assms apply (induction k) apply auto
  by (metis bot_nat_0.not_eq_extremum not_bit_numeral_Bit0_0 shift_zeros_below zero_shift)

subsubsection \<open>Set cardinality lemmas\<close>

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

lemma highestOneBitAtLeast:
  assumes "bit v n"
  shows "highestOneBit v \<ge> n"
  using assms highestOneBitInvar verit_comp_simplify1(3) by blast

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
    using no_bits_implies_zero
    using p by auto
  have geq0: "0 \<le> highestOneBit v"
    using bit_set zerosAboveHighestOne by force
  have lt64: "highestOneBit v < 64"
    using highestOneBitMax
    by (metis of_nat_numeral size64)
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

lemma highestOneBitRecN:
  assumes "bit v n"
  shows "highestOneBitRec n v = n"
  by (simp add: assms)

lemma highestOneBitRecMax: "highestOneBitRec n v \<le> n"
  by (induction n; simp)

lemma highestOneBitRecElim:
  assumes "highestOneBitRec n v = j"
  shows "(j = -1 \<and> v = 0) \<or> (j \<ge> 0 \<and> bit v j)"
  using assms highestOneBitRecTrue by blast

lemma highestOneBitRecZero: "v = 0 \<Longrightarrow> highestOneBitRec (size v) v = -1"
  by (induction rule: "highestOneBitRec.induct"; simp)

lemma highestOneBitRecLess:
  assumes "\<not> bit v n"
  shows "highestOneBitRec n v = highestOneBitRec (n - 1) v"
  using assms by force

text \<open>Some lemmas that use masks to restrict highestOneBit
      and relate it to highestOneBitRec.\<close>

lemma highestOneBitMask:
  assumes "size v = n"
  shows "highestOneBit v = highestOneBit (and v (mask n))"
  by (metis assms dual_order.refl lt2p_lem mask_eq_iff size_word.rep_eq)

lemma maskSmaller:
  assumes "\<not> bit v n"
  shows "and v (mask (Suc n)) = and v (mask n)"
  unfolding bit_eq_iff by (metis assms bit_and_iff bit_mask_iff less_Suc_eq)

lemma highestOneBitSmaller:
  assumes "size v = Suc n"
  assumes "\<not> bit v n"
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

lemma bitCount_shift1:
  assumes "j < LENGTH('a)"
  shows " bitCount ((1 :: 'a :: len word) << j) = 1"
  unfolding bitCount_def by (simp add: assms card_shift_one)

lemma bitCount_pow2:
  assumes "j < LENGTH('a)"
  shows "bitCount ((2 :: 'a :: len word) ^ j) = 1"
  unfolding bitCount_def using card_pow2_one assms by blast

lemma bitCount_leq_len: "bitCount (v::'a::len word) \<le> LENGTH('a)"
  unfolding bitCount_def using card_bits_leq_len by blast

lemma bitCount_pos_implies_bit_set:
  assumes "bitCount v > 0"
  shows "\<exists> n . bit v n"
proof -
  have "bitCount v = card {n . bit v n}"
    unfolding bitCount_def by simp
  then show ?thesis
    using assms nat_less_le by auto
qed

lemma bitCount_pos_implies_highestOneBit_set:
  assumes "bitCount v > 0"
  shows "bit v (nat (highestOneBit v))"
proof -
  have "\<exists> n . bit v n"
    by (simp add: assms bitCount_pos_implies_bit_set)
  then show ?thesis
    using highestOneBitAtLeast highestOneBitElim by force
qed

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

end