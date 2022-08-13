section \<open>Extra Theorems for Fixed-Width Integer Words\<close>

theory ValueThms
  imports Values
begin

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
  signed\_take\_bit.  But that would have to be done separately for each bit-width type.\<close>

value "sint(signed_take_bit 7 (128 :: int8))"


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

text \<open>A $bit_bounds$ version of the above lemma.\<close>

lemma signed_take_bit_bounds:
  fixes ival :: "'a :: len word"
  assumes "n \<le> LENGTH('a)"
  assumes "0 < n"
  assumes "val = sint(signed_take_bit (n - 1) ival)"
  shows "fst (bit_bounds n) \<le> val \<and> val \<le> snd (bit_bounds n)"
  using assms signed_take_bit_range lower_bounds_equiv upper_bounds_equiv
  by (metis bit_bounds.simps fst_conv less_imp_diff_less nat_less_le sint_ge sint_lt snd_conv zle_diff1_eq)

(* It is helpful to have the 64-bit instance of the above, to avoid uninstantiated types
   when apply it backwards. *)
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
(* helpful thms?
  Word.scast_eq: scast (?w::?'b word) = word_of_int (sint ?w)
  Word.sint_lt: sint (?x::?'a word) < (2::int) ^ (LENGTH(?'a) - (1::nat)
  Word.sint_uint: sint (w::'a word) = signed_take_bit (LENGTH('a) - Suc (0::nat)) (uint w)
  Word.sint_sbintrunc' :  sint (word_of_int (?bin::int)) = signed_take_bit (LENGTH(?'a) - (1::nat)) ?bin
  Word.int_word_sint   - moves up, takes mod, then moves down
  Bit_Operations.signed_take_bit_int_eq_self_iff:
    (signed_take_bit (?n::nat) (?k::int) = ?k) = (- ((2::int) ^ ?n) \<sqsubseteq> ?k \<and> ?k < (2::int) ^ ?n)
  Bit_Operations.signed_take_bit_int_eq_self:
    - ((2::int) ^ (?n::nat)) \<sqsubseteq> (?k::int) \<Longrightarrow> ?k < (2::int) ^ ?n \<Longrightarrow> signed_take_bit ?n ?k = ?k
*)

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


text \<open>Results about $new_int$.\<close>

(* may be too trivial? *)
lemma new_int_take_bits:
  assumes "IntVal b val = new_int b ival"
  shows "take_bit b val = val"
  using assms by force

end
