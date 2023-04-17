section \<open>Additional Theorems about Computer Words\<close>

theory JavaWords
  imports
    "HOL-Library.Word"
    "HOL-Library.Signed_Division"
    "HOL-Library.Float"
    "HOL-Library.LaTeXsugar"
begin

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
  unfolding shiftl_def apply (induction j)
   apply simp unfolding funpow_Suc_right
  by (metis (no_types, opaque_lifting) push_bit_eq_mult)

lemma "(x::('a::len) word) * ((2 ^ j) + 1) = x << j + x"
  by (simp add: distrib_left)

lemma "(x::('a::len) word) * ((2 ^ j) - 1) = x << j - x"
  by (simp add: right_diff_distrib)

lemma "(x::('a::len) word) * ((2^j) + (2^k)) = x << j + x << k"
  by (simp add: distrib_left)

lemma "(x::('a::len) word) * ((2^j) - (2^k)) = x << j - x << k"
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

(* declare [[show_types=true]] *)

subsubsection \<open>Support Lemmas for Upper/Lower Bounds\<close>

(* these two were weirdly hard to prove given it should be by definition *)
lemma size32: "size v = 32" for v :: "32 word"
  using size_word.rep_eq
  using One_nat_def add.right_neutral add_Suc_right len_of_numeral_defs(2) len_of_numeral_defs(3) mult.right_neutral mult_Suc_right numeral_2_eq_2 numeral_Bit0
  by (smt (verit, del_insts) mult.commute)

lemma size64: "size v = 64" for v :: "64 word"
  using size_word.rep_eq
  using One_nat_def add.right_neutral add_Suc_right len_of_numeral_defs(2) len_of_numeral_defs(3) mult.right_neutral mult_Suc_right numeral_2_eq_2 numeral_Bit0
  by (smt (verit, del_insts) mult.commute)

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
  shows "-(((2::int) ^ (N-1))) = (2::int) ^ N div 2 * - 1"
  by (simp add: assms int_power_div_base)

lemma upper_bounds_equiv:
  assumes "0 < N"
  shows "(2::int) ^ (N-1) = (2::int) ^ N div 2"
  by (simp add: assms int_power_div_base)


text \<open>Some min/max bounds for 64-bit words\<close>

lemma bit_bounds_min64: "((fst (bit_bounds 64))) \<le> (sint (v::int64))"
  unfolding bit_bounds.simps fst_def
  using sint_ge[of v] by simp

lemma bit_bounds_max64: "((snd (bit_bounds 64))) \<ge> (sint (v::int64))"
  unfolding bit_bounds.simps fst_def
  using sint_lt[of v] by simp


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
  apply transfer
  by (smt (verit, best) not_take_bit_negative signed_take_bit_eq_take_bit_shift 
     signed_take_bit_int_less_exp take_bit_int_greater_self_iff) 

lemma signed_take_bit_int_greater_eq_minus_exp_word:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  shows "- (2 ^ n) \<le> sint(signed_take_bit n ival)"
  apply transfer
  by (smt (verit, best) signed_take_bit_int_greater_eq_minus_exp 
     signed_take_bit_int_greater_eq_self_iff signed_take_bit_int_less_exp)

lemma signed_take_bit_range:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  assumes "val = sint(signed_take_bit n ival)"
  shows "- (2 ^ n) \<le> val \<and> val < 2 ^ n"
  using signed_take_bit_int_greater_eq_minus_exp_word signed_take_bit_int_less_exp_word
  using assms by blast

text \<open>A $bit\_bounds$ version of the above lemma.\<close>

lemma signed_take_bit_bounds:
  fixes ival :: "'a :: len word"
  assumes "n \<le> LENGTH('a)"
  assumes "0 < n"
  assumes "val = sint(signed_take_bit (n - 1) ival)"
  shows "fst (bit_bounds n) \<le> val \<and> val \<le> snd (bit_bounds n)"
  using assms signed_take_bit_range lower_bounds_equiv upper_bounds_equiv
  by (metis bit_bounds.simps fst_conv less_imp_diff_less nat_less_le sint_ge sint_lt snd_conv zle_diff1_eq)

(* It is helpful to have the 64-bit instance of the above, to avoid uninstantiated types
   when applying it backwards. *)
lemma signed_take_bit_bounds64:
  fixes ival :: "int64"
  assumes "n \<le> 64"
  assumes "0 < n"
  assumes "val = sint(signed_take_bit (n - 1) ival)"
  shows "fst (bit_bounds n) \<le> val \<and> val \<le> snd (bit_bounds n)"
  using assms signed_take_bit_bounds
  by (metis size64 word_size)

lemma int_signed_value_bounds:
  assumes "b1 \<le> 64"
  assumes "0 < b1"
  shows "fst (bit_bounds b1) \<le> int_signed_value b1 v2 \<and>
         int_signed_value b1 v2 \<le> snd (bit_bounds b1)"
  using assms int_signed_value.simps signed_take_bit_bounds64 by blast

lemma int_signed_value_range:
  fixes ival :: "int64"
  assumes "val = int_signed_value n ival"
  shows "- (2 ^ (n - 1)) \<le> val \<and> val < 2 ^ (n - 1)"
  using signed_take_bit_range assms
  by (smt (verit, ccfv_SIG) One_nat_def diff_less int_signed_value.elims len_gt_0 len_num1 power_less_imp_less_exp power_strict_increasing sint_greater_eq sint_less)


text \<open>Some lemmas to relate (int) bit bounds to bit-shifting values.\<close>

lemma bit_bounds_lower:
  assumes "0 < bits"
  shows "word_of_int (fst (bit_bounds bits)) = ((-1) << (bits - 1))"
   unfolding bit_bounds.simps fst_conv
   by (metis (mono_tags, opaque_lifting) assms(1) mult_1 mult_minus1_right mult_minus_left of_int_minus of_int_power shiftl_power upper_bounds_equiv word_numeral_alt)

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
  assumes "n = LENGTH('a)"
  shows "ival = take_bit n ival"
  by (simp add: assms)

text \<open>A simplification lemma for $new\_int$, showing that upper bits can be ignored.\<close>

lemma take_bit_redundant[simp]:
  fixes ival :: "'a :: len word"
  assumes "0 < n"
  assumes "n < LENGTH('a)"
  shows "signed_take_bit (n - 1) (take_bit n ival) = signed_take_bit (n - 1) ival"
proof -
  have "\<not> (n \<le> n - 1)" using assms by arith
  then have "\<And>i . signed_take_bit (n - 1) (take_bit n i) = signed_take_bit (n-1) i"
    using signed_take_bit_take_bit by (metis (mono_tags)) 
  then show ?thesis
    by blast
qed

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
  unfolding bit_bounds.simps 
  using assms take_bit_same_size_range
  by force



text \<open>Next we show that casting a word to a wider word preserves any upper/lower bounds.
  (These lemmas may not be needed any more, since we are not using scast now?)\<close>

lemma scast_max_bound:
  assumes "sint (v :: 'a :: len word) < M"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "sint ((scast v) :: 'b :: len word) < M"
  unfolding Word.scast_eq Word.sint_sbintrunc'
  using Bit_Operations.signed_take_bit_int_eq_self_iff
  by (smt (verit, best) One_nat_def assms(1) assms(2) decr_length_less_iff linorder_not_le power_strict_increasing_iff signed_take_bit_int_less_self_iff sint_greater_eq) 

lemma scast_min_bound:
  assumes "M \<le> sint (v :: 'a :: len word)"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "M \<le> sint ((scast v) :: 'b :: len word)"
  unfolding Word.scast_eq Word.sint_sbintrunc'
  using Bit_Operations.signed_take_bit_int_eq_self_iff
  by (smt (verit) One_nat_def Suc_pred assms(1) assms(2) len_gt_0 less_Suc_eq order_less_le order_less_le_trans power_le_imp_le_exp signed_take_bit_int_greater_eq_self_iff sint_lt)

lemma scast_bigger_max_bound:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "sint result < 2 ^ LENGTH('a) div 2"
  using sint_lt upper_bounds_equiv scast_max_bound
  by (smt (verit, best) assms(1) len_gt_0 signed_scast_eq signed_take_bit_int_greater_self_iff sint_ge sint_less upper_bounds_equiv) 

lemma scast_bigger_min_bound:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "- (2 ^ LENGTH('a) div 2) \<le> sint result"
  using sint_ge lower_bounds_equiv scast_min_bound
  by (smt (verit) assms len_gt_0 nat_less_le not_less scast_max_bound)

lemma scast_bigger_bit_bounds:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "fst (bit_bounds (LENGTH('a))) \<le> sint result \<and> sint result \<le> snd (bit_bounds (LENGTH('a)))"
  using assms scast_bigger_min_bound scast_bigger_max_bound
  by auto



subsubsection \<open>Support lemmas for take bit and signed take bit.\<close>

text \<open>Lemmas for removing redundant take\_bit wrappers.\<close>

lemma take_bit_dist_addL[simp]: 
  fixes x :: "'a :: len word"
  shows "take_bit b (take_bit b x + y) = take_bit b (x + y)"
proof (induction b)
  case 0
  then show ?case
    by simp 
next
  case (Suc b)
  then show ?case
    by (simp add: add.commute mask_eqs(2) take_bit_eq_mask) 
qed

lemma take_bit_dist_addR[simp]: 
  fixes x :: "'a :: len word"
  shows "take_bit b (x + take_bit b y) = take_bit b (x + y)"
  using take_bit_dist_addL by (metis add.commute)


lemma take_bit_dist_subL[simp]: 
  fixes x :: "'a :: len word"
  shows "take_bit b (take_bit b x - y) = take_bit b (x - y)"
  by (metis take_bit_dist_addR uminus_add_conv_diff)

lemma take_bit_dist_subR[simp]: 
  fixes x :: "'a :: len word"
  shows "take_bit b (x - take_bit b y) = take_bit b (x - y)"
  using take_bit_dist_subL
  by (metis (no_types, opaque_lifting) diff_add_cancel diff_right_commute diff_self) 


lemma take_bit_dist_neg[simp]:
  fixes ix :: "'a :: len word"
  shows "take_bit b (- take_bit b (ix)) = take_bit b (- ix)"
  by (metis diff_0 take_bit_dist_subR)


lemma signed_take_take_bit[simp]: 
  fixes x :: "'a :: len word"
  assumes "0 < b"
  shows "signed_take_bit (b - 1) (take_bit b x) = signed_take_bit (b - 1) x"
  by (smt (verit, best) Suc_diff_1 assms lessI linorder_not_less signed_take_bit_take_bit)


lemma mod_larger_ignore:
  fixes a :: int
  fixes m n :: nat
  assumes "n < m"
  shows "(a mod 2 ^ m) mod 2 ^ n = a mod 2 ^ n"
  by (smt (verit, del_insts) assms exp_mod_exp linorder_not_le mod_0_imp_dvd mod_mod_cancel mod_self order_less_imp_le)
  

lemma mod_dist_over_add:
  fixes a b c :: int64  (* "'a :: len word" *)
  fixes n :: nat
  assumes 1: "0 < n"
  assumes 2: "n < 64"
  shows "(a mod 2^n + b) mod 2^n = (a + b) mod 2^n"
proof -
  have 3: "(0 :: int64) < 2 ^ n"
    using assms by (simp add: size64 word_2p_lem)
  then show ?thesis
    unfolding word_mod_2p_is_mask[OF 3]
    apply transfer
    by (metis (no_types, opaque_lifting) and.right_idem take_bit_add take_bit_eq_mask)
qed

end
