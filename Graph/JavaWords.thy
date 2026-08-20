section \<open>Additional Theorems about Computer Words\<close>

theory JavaWords
  imports
    "HOL-Library.Word"
    "HOL-Library.Signed_Division"
    "HOL-Library.Float"
    "HOL-Library.LaTeXsugar"
    Word_Lib.More_Word_Operations
begin

no_notation shiftl (infixl \<open><<\<close> 55)
no_notation shiftr (infixl \<open>>>\<close> 55)
no_notation sshiftr (infixl \<open>>>>\<close> 55)

text \<open>Java supports 64, 32, 16, 8 signed ints, plus 1 bit (boolean)
ints, and char is 16-bit unsigned.
E.g. an 8-bit stamp has a default range of -128..+127.
And a 1-bit stamp has a default range of -1..0, surprisingly.

During calculations the smaller sizes are sign-extended to 32 bits.
\<close>

type_synonym int64 = "64 word" \<comment> \<open>long\<close>
type_synonym int32 = "32 word" \<comment> \<open>int\<close>
type_synonym int16 = "16 word" \<comment> \<open>short\<close>
type_synonym int8 = "8 word" \<comment> \<open>char\<close>
type_synonym int1 = "1 word" \<comment> \<open>boolean\<close>

abbreviation valid_int_widths :: "nat set" where
  "valid_int_widths \<equiv> {1, 8, 16, 32, 64}"

type_synonym iwidth = "nat"  (* TODO: 1..64 *)

fun bit_bounds :: "nat \<Rightarrow> (int \<times> int)" where
  "bit_bounds bits = (((2 ^ bits) div 2) * -1, ((2 ^ bits) div 2) - 1)"

definition logic_negate :: "('a::len) word \<Rightarrow> 'a word" where
  "logic_negate x = (if x = 0 then 1 else 0)"

fun int_signed_value :: "iwidth \<Rightarrow> int64 \<Rightarrow> int" where
  "int_signed_value b v = sint (signed_take_bit (b - 1) v)"

fun int_unsigned_value :: "iwidth \<Rightarrow> int64 \<Rightarrow> int" where
  "int_unsigned_value b v = uint v"

text \<open>A convenience function for directly constructing -1 values of a given bit size.\<close>
fun neg_one :: "iwidth \<Rightarrow> int64" where
  "neg_one b = mask b"

subsection \<open>Bit-Shifting Operators\<close>

definition shiftl (infix "<<" 75) where
  "shiftl w n = (push_bit n) w"

lemma shiftl_power[simp]: "(x::('a::len) word) * (2 ^ j) = x << j"
  unfolding shiftl_def by (induction j; auto simp add: push_bit_eq_mult)

lemma "(x::('a::len) word) * ((2 ^ j) + 1) = x << j + x"
  by (simp add: distrib_left)

lemma "(x::('a::len) word) * ((2 ^ j) - 1) = x << j - x"
  by (simp add: right_diff_distrib)

lemma "(x::('a::len) word) * ((2 ^ j) + (2 ^ k)) = x << j + x << k"
  by (simp add: distrib_left)

lemma "(x::('a::len) word) * ((2 ^ j) - (2 ^ k)) = x << j - x << k"
  by (simp add: right_diff_distrib)

text \<open>Unsigned shift right.\<close>
definition shiftr (infix ">>>" 75) where
  "shiftr w n = drop_bit n w"

corollary "(255 :: 8 word) >>> (2 :: nat) = 63" by code_simp

(* TODO: define this using Word.signed_drop_bit ? *)
text \<open>Signed shift right.\<close>
definition sshiftr :: "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix ">>" 75) where
  "sshiftr w n = word_of_int ((sint w) div (2 ^ n))"

corollary "(128 :: 8 word) >> 2 = 0xE0" by code_simp

subsection \<open>Fixed-width Word Theories\<close>

subsubsection \<open>Support Lemmas for Upper/Lower Bounds\<close>

(* these two were weirdly hard to prove given it should be by definition *)
lemma size32: "size v = 32" for v :: "32 word"
  by (smt (verit) len_of_numeral_defs(2,3) mult.right_neutral numeral_Bit0_eq_double
      size_word.rep_eq)

lemma size64: "size v = 64" for v :: "64 word"
  by (smt (z3) numeral_times_numeral semiring_norm(12,13) len_of_numeral_defs(3) size_word.rep_eq
      size32)

(* Nb. Word.sint_ge and sint_lt subsume these lemmas.
lemma signed_int_bottom32: "-(((2::int) ^ 31)) \<le> sint (v::int32)"
  using sint_range_size size32
  by (smt (verit, ccfv_SIG) One_nat_def Suc_pred add_Suc add_Suc_right eval_nat_numeral(3) nat.inject numeral_2_eq_2 numeral_Bit0 numeral_Bit1 zero_less_numeral)

lemma signed_int_top32: "(2 ^ 31) - 1 \<ge> sint (v::int32)"
  using sint_range_size size32
  by (smt (verit, ccfv_SIG) One_nat_def Suc_pred add_Suc add_Suc_right eval_nat_numeral(3) nat.inject numeral_2_eq_2 numeral_Bit0 numeral_Bit1 zero_less_numeral)
*)

lemma lower_bounds_equiv:
  assumes "0 < N"
  shows "-(((2::int) ^ (N - 1))) = (2::int) ^ N div 2 * - 1"
  by (simp add: assms int_power_div_base)

lemma upper_bounds_equiv:
  assumes "0 < N"
  shows "(2::int) ^ (N - 1) = (2::int) ^ N div 2"
  by (simp add: assms int_power_div_base)

text \<open>Some min/max bounds for 64-bit words\<close>

lemma bit_bounds_min64: "fst (bit_bounds 64) \<le> sint (v::int64)"
  unfolding bit_bounds.simps fst_def using sint_ge[of v] by simp

lemma bit_bounds_max64: "snd (bit_bounds 64) \<ge> sint (v::int64)"
  unfolding bit_bounds.simps fst_def using sint_lt[of v] by simp

text \<open>Extend these min/max bounds to extracting smaller signed words using $signed\_take\_bit$.\<close>

text \<open>Note: we could use signed to convert between bit-widths, instead of 
  $signed\_take\_bit$.  But that would have to be done separately for each bit-width type.\<close>

corollary "sint(signed_take_bit 7 (128 :: int8)) = -128" by code_simp

ML_val \<open>@{thm signed_take_bit_decr_length_iff}\<close>
declare [[show_types=true]]
ML_val \<open>@{thm signed_take_bit_int_less_exp}\<close>

lemma signed_take_bit_int_less_exp_word:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  shows "sint(signed_take_bit n ival) < (2::int) ^ n"
  apply transfer using assms apply auto
  by (metis min.commute signed_take_bit_signed_take_bit signed_take_bit_int_less_exp)

lemma signed_take_bit_int_greater_eq_minus_exp_word:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  shows "- (2 ^ n) \<le> sint(signed_take_bit n ival)"
  apply transfer using assms apply auto
  by (metis min.commute signed_take_bit_signed_take_bit signed_take_bit_int_greater_eq_minus_exp)

lemma signed_take_bit_range:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  assumes "val = sint(signed_take_bit n ival)"
  shows "- (2 ^ n) \<le> val \<and> val < 2 ^ n"
  using signed_take_bit_int_greater_eq_minus_exp_word signed_take_bit_int_less_exp_word assms
  by blast

lemma val_neg_def:
  fixes v :: int64
  assumes "bit v (n - 1)"
  shows "sint (signed_take_bit (n - 1) v) < 0"
proof -
  have "signed_take_bit (n - 1) v = or (take_bit (n - 1) v) (not (mask (n - 1)))"
    using assms signed_take_bit_eq_if_negative by auto
  then show ?thesis
    using assms apply transfer by (simp add: bit_take_bit_iff)
qed

lemma val_pos_def:
  fixes v :: int64
  assumes "n \<le> 64"
  assumes "\<not> bit v (n - 1)"
  shows "0 \<le> sint (signed_take_bit (n - 1) v)"
  using assms apply transfer by (simp add: bit_take_bit_iff)

lemma val_pos_bit:
  fixes v :: int64
  assumes "n \<le> 64"
  assumes "0 \<le> sint (signed_take_bit (n - 1) v)"
  shows "\<not> bit v (n - 1)"
  using assms apply transfer by (simp add: bit_take_bit_iff)

lemma val_bits_take_eq:
  fixes v :: int64
  assumes "n \<le> 64"
  shows "0 \<le> sint (signed_take_bit (n - 1) v) = (\<not> bit v (n - 1))"
  by (metis assms val_pos_bit val_pos_def)

text \<open>A $bit\_bounds$ version of the above lemma.\<close>

lemma signed_take_bit_bounds:
  fixes ival :: "'a :: len word"
  assumes "n \<le> LENGTH('a)"
  assumes "0 < n"
  assumes "val = sint(signed_take_bit (n - 1) ival)"
  shows "fst (bit_bounds n) \<le> val \<and> val \<le> snd (bit_bounds n)"
  using assms apply auto
  by (simp add: signed_take_bit_int_greater_eq_minus_exp_word signed_take_bit_int_less_exp_word
      int_power_div_base)+

(* It is helpful to have the 64-bit instance of the above, to avoid uninstantiated types
   when applying it backwards. *)
lemma signed_take_bit_bounds64:
  fixes ival :: "int64"
  assumes "n \<le> 64"
  assumes "0 < n"
  assumes "val = sint(signed_take_bit (n - 1) ival)"
  shows "fst (bit_bounds n) \<le> val \<and> val \<le> snd (bit_bounds n)"
  by (metis assms signed_take_bit_bounds size64 word_size)

lemma int_signed_value_bounds:
  assumes "b \<le> 64"
  assumes "0 < b"
  shows "fst (bit_bounds b) \<le> int_signed_value b v \<and> int_signed_value b v \<le> snd (bit_bounds b)"
  using assms int_signed_value.simps signed_take_bit_bounds64 by blast

lemma int_signed_value_range:
  fixes ival :: "int64"
  assumes "val = int_signed_value n ival"
  shows "- (2 ^ (n - 1)) \<le> val \<and> val < 2 ^ (n - 1)"
  using assms apply auto
  by (smt (verit, ccfv_threshold) sint_greater_eq diff_less len_gt_0 power_strict_increasing sint_0
      power_less_imp_less_exp signed_take_bit_range One_nat_def neg_equal_0_iff_equal signed_minus_1
      power_0 not_gr_zero word_exp_length_eq_0 diff_zero sint_less)+

text \<open>Some lemmas to relate (int) bit bounds to bit-shifting values.\<close>

lemma bit_bounds_lower:
  assumes "0 < bits"
  shows "word_of_int (fst (bit_bounds bits)) = ((-1) << (bits - 1))"
  unfolding bit_bounds.simps fst_conv
  by (metis (mono_tags, opaque_lifting) assms mult_1 mult_minus1_right mult_minus_left of_int_minus
      of_int_power shiftl_power upper_bounds_equiv word_numeral_alt)

lemma two_exp_div:
  assumes "0 < bits"
  shows "((2::int) ^ bits div (2::int)) = (2::int) ^ (bits - Suc 0)"
  using assms by (auto simp: int_power_div_base)

declare [[show_types]]

(*
lemma mask_drop_bit_test:
  "\<forall> n bits :: nat.
    0 < bits \<and> bits < 4 \<and> n < bits \<and> bits < LENGTH('a)
    \<longrightarrow> drop_bit n (mask bits :: 'a :: len word) = mask (bits - n)"
  nitpick
*)
(*
lemma mask_drop_bit:
  fixes n bits :: nat
  assumes "0 < bits"
  assumes "bits < LENGTH('a)"
  assumes "n < bits"
  shows "drop_bit n (mask bits :: 'a :: len word) = mask (bits - n)"
proof -
  have "drop_bit (n::nat) (mask (bits::nat)) = mask (bits - n)"
    using assms drop_bit_mask_eq

    thm bit_eqI
    thm bits_induct
    thm drop_bit_mask_eq

  apply transfer
  print_state

  apply simp
lemma bit_bounds_upper:
  assumes 1: "0 < bits"
  assumes "bits \<le> 64"
  shows "word_of_int (snd (bit_bounds bits)) = (mask bits >>> 1)"
proof -
  have "(2 :: 'a word) ^ bits - 1 = mask bits"
    by (simp add: mask_eq_decr_exp)
  then show ?thesis
    unfolding bit_bounds.simps snd_conv two_exp_div[OF 1]
    apply (simp add: mask_eq_decr_exp[symmetric] shiftr_def)
    apply (simp add: drop_bit_mask_eq)


   apply (simp add: int_power_div_base)

   apply (simp add: mask_eq_decr_exp)
*)

text \<open>Some lemmas about unsigned words smaller than 64-bit, for zero-extend operators.\<close>

lemma take_bit_smaller_range:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  assumes "val = sint(take_bit n ival)"
  shows "0 \<le> val \<and> val < (2::int) ^ n"
  by (simp add: assms signed_take_bit_eq)

lemma take_bit_same_size_nochange:
  fixes ival :: "'a :: len word"
  shows "ival = take_bit (LENGTH('a)) ival"
  by simp

text \<open>A simplification lemma for $new\_int$, showing that upper bits can be ignored.\<close>

lemma take_bit_signed_redundant[simp]:
  fixes ival :: "'a :: len word"
  assumes "0 < n"
  shows "signed_take_bit (n - 1) (take_bit n ival) = signed_take_bit (n - 1) ival"
  by (smt (verit) Suc_diff_1 Suc_n_not_le_n assms(1) signed_take_bit_take_bit)

lemma take_bit_same_size_range:
  fixes ival :: "'a :: len word"
  assumes "n = LENGTH('a)"
  assumes "ival2 = take_bit n ival"
  shows "- (2 ^ n div 2) \<le> sint ival2 \<and> sint ival2 < 2 ^ n div 2"
  using assms lower_bounds_equiv sint_ge sint_lt by auto

lemma take_bit_same_bounds:
  fixes ival :: "'a :: len word"
  assumes "n = LENGTH('a)"
  assumes "ival2 = take_bit n ival"
  shows "fst (bit_bounds n) \<le> sint ival2 \<and> sint ival2 \<le> snd (bit_bounds n)"
  unfolding bit_bounds.simps using assms take_bit_same_size_range by force

text \<open>Next we show that casting a word to a wider word preserves any upper/lower bounds.
  (These lemmas may not be needed any more, since we are not using scast now?)\<close>

lemma scast_max_bound:
  assumes "sint (v :: 'a :: len word) < M"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "sint ((scast v) :: 'b :: len word) < M"
  using assms unfolding Word.scast_eq Word.sint_sbintrunc' by (simp add: sint_uint)

lemma scast_min_bound:
  assumes "M \<le> sint (v :: 'a :: len word)"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "M \<le> sint ((scast v) :: 'b :: len word)"
  using assms unfolding Word.scast_eq Word.sint_sbintrunc' by (simp add: sint_uint)

lemma scast_bigger_max_bound:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "sint result < 2 ^ LENGTH('a) div 2"
  using assms apply auto
  by (smt (verit, ccfv_SIG) assms len_gt_0 signed_scast_eq signed_take_bit_int_greater_self_iff
      sint_ge sint_less upper_bounds_equiv sint_lt upper_bounds_equiv scast_max_bound)

lemma scast_bigger_min_bound:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "- (2 ^ LENGTH('a) div 2) \<le> sint result"
  by (metis upper_bounds_equiv assms len_gt_0 nat_less_le not_less scast_max_bound scast_min_bound
      sint_ge)

lemma scast_bigger_bit_bounds:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "fst (bit_bounds (LENGTH('a))) \<le> sint result \<and> sint result \<le> snd (bit_bounds (LENGTH('a)))"
  using assms scast_bigger_min_bound scast_bigger_max_bound by auto

subsubsection \<open>Support lemmas for take bit and signed take bit.\<close>

text \<open>Lemmas for removing redundant take\_bit wrappers.\<close>

lemma take_bit_dist_addL[simp]:
  fixes x :: "'a :: len word"
  shows "take_bit b (take_bit b x + y) = take_bit b (x + y)"
  apply (induction b) by (simp add: add.commute mask_eqs(2) take_bit_eq_mask)+

lemma take_bit_dist_addR[simp]:
  fixes x :: "'a :: len word"
  shows "take_bit b (x + take_bit b y) = take_bit b (x + y)"
  by (metis take_bit_dist_addL add.commute)

lemma take_bit_dist_subL[simp]:
  fixes x :: "'a :: len word"
  shows "take_bit b (take_bit b x - y) = take_bit b (x - y)"
  by (metis take_bit_dist_addR uminus_add_conv_diff)

lemma take_bit_dist_subR[simp]:
  fixes x :: "'a :: len word"
  shows "take_bit b (x - take_bit b y) = take_bit b (x - y)"
  by (metis (no_types, opaque_lifting) take_bit_dist_subL diff_add_cancel diff_right_commute
      diff_self)

lemma take_bit_dist_neg[simp]:
  fixes x :: "'a :: len word"
  shows "take_bit b (-take_bit b (x)) = take_bit b (-x)"
  by (metis diff_0 take_bit_dist_subR)

lemma mergeTakeBit:
  fixes b c :: "'a :: len word"
  shows "take_bit a (take_bit a b * take_bit a c) = take_bit a (b * c)"
  by (smt (verit, ccfv_SIG) take_bit_mult take_bit_of_int unsigned_take_bit_eq word_mult_def)

lemma take_bit_size_eq64: "take_bit 64 a = take_bit LENGTH(64) (a::64 word)"
  by auto

lemma take_bit64 [simp]:
  fixes w :: "int64"
  shows "take_bit 64 w = w"
  by (metis take_bit_size_eq64 take_bit_length_eq)

text \<open>Lemmas for take\_bit equivalence.\<close>

lemma takeBitNot:
  assumes "xb \<ge> 1"
  shows "take_bit xb (not xv) \<noteq> take_bit xb xv"
  by (metis bit.xor_compl_left diff_0_right mask_eq_0_iff not_one_le_zero take_bit_not_eq_mask_diff
      assms take_bit_xor xor_self_eq)

lemma take_bit_minus_push_bit:
  fixes v :: "64word"
  assumes "\<not>bit v (n - 1)"
  assumes "take_bit n v = v"
  shows "(take_bit n v - take_bit (n - 1) v) = push_bit (n - 1) (of_bool (bit v (n - 1)))"
  using assms apply auto
  by (smt (z3) linordered_semidom_class.add_diff_inverse signed_take_bit_eq_if_positive less_Suc_eq
      zero_less_diff signed_take_bit_code One_nat_def plus_1_eq_Suc less_nat_zero_code not_gr_zero)

text \<open>Helpful signed\_take\_bit and sint properties\<close>

lemma take_bit_eq_signed: "take_bit b v = v \<Longrightarrow> signed_take_bit b v = v"
  by (metis (full_types) eq_imp_le signed_take_bit_take_bit)

lemma unwrap_signed_take_bit:
  fixes v :: int64
  assumes "0 < b \<and> b \<le> 64"
  assumes "signed_take_bit (b - 1) v = v"
  shows "signed_take_bit 63 (Word.rep (signed_take_bit (b - Suc 0) v)) = sint v"
  using assms by (simp add: signed_def)

lemma sint_pos_signed_unset:
  fixes w :: "'a::len word"
  assumes "sint w \<ge> 0"
  shows "\<not>(bit w (LENGTH('a) - Suc 0))"
  using bit_last_iff assms linorder_not_less by auto

lemma sint_pos_eq_uint:
  assumes "sint x \<ge> 0"
  shows "sint x = uint x"
  by (metis (lifting) sint_pos_signed_unset bit_uint_iff take_bit_eq_self_iff_drop_bit_eq_0 assms
      drop_bit_eq_zero_iff_not_bit_last signed_take_bit_eq_if_positive unsigned_take_bit_eq
      sint_uint)

lemma sint_pos_lt_uint_lt:
  assumes "sint x \<ge> 0"
  assumes "sint y \<ge> 0"
  shows "(sint x < sint y) = (uint x < uint y)"
  by (simp add: assms sint_pos_eq_uint)

lemma sint_pos_lt_uint_below:
  assumes "sint x \<ge> 0"
  assumes "sint y \<ge> 0"
  shows "(x <s y) = (x < y)"
  by (metis word_less_iff_unsigned word_sless_alt sint_pos_lt_uint_lt assms)

text \<open>mod lemmas\<close>

lemma mod_larger_ignore:
  fixes a :: int
  fixes m n :: nat
  assumes "n < m"
  shows "(a mod 2 ^ m) mod 2 ^ n = a mod 2 ^ n"
  by (meson assms le_imp_power_dvd less_or_eq_imp_le mod_mod_cancel)

lemma mod_dist_over_add:
  fixes a b c :: int64  (* "'a :: len word" *)
  fixes n :: nat
  assumes 1: "0 < n"
  assumes 2: "n < 64"
  shows "(a mod 2^n + b) mod 2^n = (a + b) mod 2^n"
proof -
  have g0: "(0 :: int64) < 2 ^ n"
    using assms by (simp add: size64 word_2p_lem)
  then show ?thesis
    unfolding word_mod_2p_is_mask[OF g0] by (simp add: mask_eqs(1))
qed

subsection \<open>Java min and max operators on 64-bit values\<close>

text \<open>Java uses signed comparison, so we define a convenient abbreviation for this to avoid
  accidental mistakes, because by default the Isabelle min/max will assume unsigned words.\<close>

abbreviation javaMin64 :: "int64 \<Rightarrow> int64 \<Rightarrow> int64" where
  "javaMin64 a b \<equiv> (if a \<le>s b then a else b)"

abbreviation javaMax64 :: "int64 \<Rightarrow> int64 \<Rightarrow> int64" where
  "javaMax64 a b \<equiv> (if a \<le>s b then b else a)"

end
