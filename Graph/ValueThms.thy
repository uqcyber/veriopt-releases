subsection \<open>Fixed-width Word Theories\<close>

theory ValueThms
  imports
    Values
begin

(* declare [[show_types=true]] *)

subsubsection \<open>Support Lemmas for Upper/Lower Bounds\<close>

(* these two were weirdly hard to prove given it should be by definition *)
lemma size32: "size v = 32" for v :: "32 word"
  by (simp add: size32)

lemma size64: "size v = 64" for v :: "64 word"
  by (simp add: size64)

(* Nb. Word.sint_ge and sint_lt subsume these lemmas.
lemma signed_int_bottom32: "-(((2::int) ^ 31)) \<le> sint (v::int32)"
  using sint_range_size size32
  by (smt (verit, ccfv_SIG) One_nat_def Suc_pred add_Suc add_Suc_right eval_nat_numeral(3) nat.inject numeral_2_eq_2 numeral_Bit0 numeral_Bit1 zero_less_numeral)

lemma signed_int_top32: "(2 ^ 31) - 1 \<ge> sint (v::int32)"
  using sint_range_size size32
  by (smt (verit, ccfv_SIG) One_nat_def Suc_pred add_Suc add_Suc_right eval_nat_numeral(3) nat.inject numeral_2_eq_2 numeral_Bit0 numeral_Bit1 zero_less_numeral)
*)

lemma lower_bounds_equiv: "0 < N \<Longrightarrow> -(((2::int) ^ (N-1))) = (2::int) ^ N div 2 * - 1"
  by (simp add: int_power_div_base)

lemma upper_bounds_equiv: "0 < N \<Longrightarrow> (2::int) ^ (N-1) = (2::int) ^ N div 2"
  by (simp add: int_power_div_base)

lemma intval_bits_in_bounds_expand_lower:
  assumes "intval_bits_in_bounds x l h"
  assumes "l' < l"
  shows "intval_bits_in_bounds x l' h"
  using assms intval_bits_in_bounds.elims(2) by fastforce

lemma intval_bits_in_bounds_expand_upper:
  assumes "intval_bits_in_bounds x l h"
  assumes "h' > h"
  shows "intval_bits_in_bounds x l h'"
  using assms intval_bits_in_bounds.elims(2) by fastforce

lemma width_eq_implies_bitbounds_eq:
  assumes "x = IntVal n xv"
  assumes "y = IntVal n yv"
  assumes "intval_bits_in_bounds x lo hi"
  shows "intval_bits_in_bounds y lo hi"
  using assms by auto

text \<open>Some min/max bounds for 64-bit words\<close>

lemma bit_bounds_min64: "((fst (bit_bounds 64))) \<le> (sint (v::int64))"
  using sint_ge[of v] by simp

lemma bit_bounds_max64: "((snd (bit_bounds 64))) \<ge> (sint (v::int64))"
  using sint_lt[of v] by simp

text \<open>Extend these min/max bounds to extracting smaller signed words using $signed\_take\_bit$.\<close>

text \<open>Note: we could use signed to convert between bit-widths, instead of
      signed\_take\_bit.  But that would have to be done separately for each bit-width type.\<close>

value "sint(signed_take_bit 7 (128 :: int8))"

ML_val \<open>@{thm signed_take_bit_decr_length_iff}\<close>
declare [[show_types=true]]
ML_val \<open>@{thm signed_take_bit_int_less_exp}\<close>

lemma signed_take_bit_int_less_exp_word:
  fixes v :: "'a :: len word"
  assumes "n < LENGTH('a)"
  shows "sint(signed_take_bit n v) < (2::int) ^ n"
  using assms signed_take_bit_range by auto

lemma signed_take_bit_int_greater_eq_minus_exp_word:
  fixes v :: "'a :: len word"
  assumes "n < LENGTH('a)"
  shows "- (2 ^ n) \<le> sint(signed_take_bit n v)"
  using signed_take_bit_int_greater_eq_minus_exp_word assms by blast

lemma signed_take_bit_range:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  assumes "v = sint(signed_take_bit n ival)"
  shows "- (2 ^ n) \<le> v \<and> v < 2 ^ n"
  by (auto simp add: signed_take_bit_int_greater_eq_minus_exp_word signed_take_bit_int_less_exp_word
      assms)

text \<open>A $bit\_bounds$ version of the above lemma.\<close>

lemma signed_take_bit_bounds:
  fixes ival :: "'a :: len word"
  assumes "n \<le> LENGTH('a)"
  assumes "0 < n"
  assumes "v = sint(signed_take_bit (n - 1) ival)"
  shows "fst (bit_bounds n) \<le> v \<and> v \<le> snd (bit_bounds n)"
  using assms signed_take_bit_bounds by blast

(* It is helpful to have the 64-bit instance of the above, to avoid uninstantiated types
   when apply it backwards. *)
lemma signed_take_bit_bounds64:
  fixes ival :: "int64"
  assumes "n \<le> 64"
  assumes "0 < n"
  assumes "v = sint(signed_take_bit (n - 1) ival)"
  shows "fst (bit_bounds n) \<le> v \<and> v \<le> snd (bit_bounds n)"
  by (metis size64 word_size signed_take_bit_bounds assms)

lemma int_signed_value_bounds:
  assumes "b1 \<le> 64"
  assumes "0 < b1"
  shows "fst (bit_bounds b1) \<le> int_signed_value b1 v2 \<and>
         int_signed_value b1 v2 \<le> snd (bit_bounds b1)"
  using signed_take_bit_bounds64 by (simp add: assms)

lemma int_signed_value_range:
  fixes ival :: "int64"
  assumes "v = int_signed_value n ival"
  shows "- (2 ^ (n - 1)) \<le> v \<and> v < 2 ^ (n - 1)"
  using assms int_signed_value_range by blast

text \<open>Some lemmas about unsigned words smaller than 64-bit, for zero-extend operators.\<close>

lemma take_bit_smaller_range:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  assumes "v = sint(take_bit n ival)"
  shows "0 \<le> v \<and> v < (2::int) ^ n"
  by (simp add: assms signed_take_bit_eq)

lemma take_bit_same_size_nochange: "n = LENGTH('a) \<Longrightarrow> (v::'a :: len word) = take_bit n v"
  by simp

text \<open>A simplification lemma for $new\_int$, showing that upper bits can be ignored.\<close>

lemma take_bit_redundant[simp]:
  fixes v :: "'a :: len word"
  assumes "0 < n"
  shows "signed_take_bit (n - 1) (take_bit n v) = signed_take_bit (n - 1) v"
  using assms take_bit_signed_redundant by auto

lemma take_bit_same_size_range:
  fixes v :: "'a :: len word"
  assumes "n = LENGTH('a)"
  assumes "v2 = take_bit n v"
  shows "- (2 ^ n div 2) \<le> sint v2 \<and> sint v2 < 2 ^ n div 2"
  using lower_bounds_equiv sint_ge sint_lt by (auto simp add: assms)

lemma take_bit_same_bounds:
  fixes v :: "'a :: len word"
  assumes "n = LENGTH('a)"
  assumes "v2 = take_bit n v"
  shows "fst (bit_bounds n) \<le> sint v2 \<and> sint v2 \<le> snd (bit_bounds n)"
  using assms take_bit_same_size_range by force

text \<open>Next we show that casting a word to a wider word preserves any upper/lower bounds.
  (These lemmas may not be needed any more, since we are not using scast now?)\<close>

lemma scast_max_bound:
  assumes "sint (v :: 'a :: len word) < M"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "sint ((scast v) :: 'b :: len word) < M"
  using scast_max_bound assms by fast
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
  by (simp add: scast_min_bound assms)

lemma scast_bigger_max_bound:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "sint result < 2 ^ LENGTH('a) div 2"
  using assms scast_bigger_max_bound by blast

lemma scast_bigger_min_bound:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "- (2 ^ LENGTH('a) div 2) \<le> sint result"
  using scast_bigger_min_bound assms by blast

lemma scast_bigger_bit_bounds:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "fst (bit_bounds (LENGTH('a))) \<le> sint result \<and> sint result \<le> snd (bit_bounds (LENGTH('a)))"
  by (auto simp add: scast_bigger_max_bound scast_bigger_min_bound assms)

text \<open>Results about $new\_int$.\<close>

(* may be too trivial? *)
lemma new_int_take_bits: "IntVal b val = new_int b v \<Longrightarrow> take_bit b val = val"
  by simp

lemma new_int_take_bit_eq:
  assumes "x = IntVal n v"
  assumes "take_bit_val_eq x"
  shows "x = new_int n v"
  using assms by auto

lemma is_truncated_IntVal_new_int_iff: "is_truncated v b \<longleftrightarrow> new_int b v = IntVal b v"
  using is_truncated_def by force

subsubsection \<open>Support lemmas for take bit and signed take bit.\<close>

text \<open>Lemmas for removing redundant take\_bit wrappers.\<close>

lemma take_bit_dist_addL[simp]:
  fixes x :: "'a :: len word"
  shows "take_bit b (take_bit b x + y) = take_bit b (x + y)"
  by simp

lemma take_bit_dist_addR[simp]:
  fixes x :: "'a :: len word"
  shows "take_bit b (x + take_bit b y) = take_bit b (x + y)"
  by simp

lemma take_bit_dist_subL[simp]:
  fixes x :: "'a :: len word"
  shows "take_bit b (take_bit b x - y) = take_bit b (x - y)"
  by simp

lemma take_bit_dist_subR[simp]:
  fixes x :: "'a :: len word"
  shows "take_bit b (x - take_bit b y) = take_bit b (x - y)"
  by simp

lemma take_bit_dist_neg[simp]:
  fixes ix :: "'a :: len word"
  shows "take_bit b (- take_bit b (ix)) = take_bit b (- ix)"
  by simp

lemma mod_larger_ignore:
  fixes a :: int
  fixes m n :: nat
  assumes "n < m"
  shows "(a mod 2 ^ m) mod 2 ^ n = a mod 2 ^ n"
  using mod_larger_ignore assms by blast
  
lemma mod_dist_over_add:
  fixes a b c :: int64  (* "'a :: len word" *)
  fixes n :: nat
  assumes "0 < n"
  assumes "n < 64"
  shows "(a mod 2^n + b) mod 2^n = (a + b) mod 2^n"
  by (simp add: assms mod_dist_over_add)

subsubsection \<open>$val_boolean$ and $bool_to_val$ lemmas\<close>

lemma intval_logic_negation_bool_self:
  "val_is_boolean v \<Longrightarrow> intval_logic_negation (intval_logic_negation v) = v"
  unfolding val_is_boolean_def bool_values_def apply (cases v; auto)
  by (simp add: logic_negate_def word_coorder.extremum_uniqueI)+

lemma bool_to_val_boolean: "val_is_boolean (bool_to_val v)"
  unfolding val_is_boolean_def bool_values_def using bool_to_val.elims by blast

lemma unwrap_bool_to_val: "(bool_to_val a = bool_to_val b) = (a = b)"
  apply auto using bool_to_val.elims by fastforce+

subsubsection \<open>bitCount and $val_bit_count$ lemmas\<close>

text \<open>bitCount lemmas\<close>

lemma bitCount_64_IntVal: "val_bit_count (IntVal 64 v) = bitCount v"
  using val_bit_count.simps by simp

lemma bitCount_64_new_int: "val_bit_count (new_int 64 v) = bitCount v"
  using val_bit_count.simps by simp

text \<open>$val_bit_count$ lemmas\<close>

lemma val_bit_count_2_val_supp:
  assumes "y = new_int b yv"
  assumes "is_truncated yv b"
  assumes "val_bit_count y = 2"
  shows "val_supp y = {topBit yv, botBit yv}"
  using bitCount_2_lsb_msb word_inspection.supp_def assms unfolding is_truncated_def by auto

lemma val_bit_count_2_sum_push_bit:
  assumes "y = new_int b yv"
  assumes "is_truncated yv b"
  assumes "val_bit_count y = 2"
  shows "yv = push_bit (topBit yv) 1 + push_bit (botBit yv) 1"
  using assms bitCount_2_sum_push_bit unfolding is_truncated_def by force

lemma val_bit_count_2_sum_pow_2:
  assumes "y = new_int b yv"
  assumes "val_bit_count y = 2"
  assumes "is_truncated yv b"
  shows "yv = 2 ^ (topBit yv) + 2 ^ (botBit yv)"
  using val_bit_count_2_sum_push_bit assms by fastforce

lemma val_bit_count_nonzero:
  assumes "x = new_int b xv"
  assumes "val_bit_count x \<noteq> 0"
  shows "xv \<noteq> 0"
  by (metis val_bit_count.simps Value.inject(1) bitCount_0 new_int.elims new_int_zero assms)

text \<open>topBit lemmas\<close>

lemma val_bit_count_top_is_truncated_take_bit_32:
  assumes "y = new_int b yv"
  assumes "val_bit_count y = 2"
  assumes "yv \<noteq> 0"
  assumes "is_truncated yv 32"
  shows "(and (take_bit 32 (word_of_nat (topBit yv))) 31) =
         (and (word_of_nat (topBit yv))) 31"
proof -
  have "topBit yv \<in> word_inspection.supp yv"
    using assms(3) supp_contains_topBit_nonzero_iff by blast
  then have range: "topBit yv \<in> {0..31}"
    using assms supp_is_truncated_range [of yv 32] unfolding is_truncated_def by auto
  have "(and (take_bit 32 (topBit yv)) 31) = (and (topBit yv) 31)"
    using range take_bit_eq by (simp add: le_def)
  then show ?thesis
    by (metis of_nat_and_eq of_nat_numeral take_bit_of_nat)
qed

lemma val_bit_count_unfold_topBit_32:
  assumes "y = new_int b yv"
  assumes "val_bit_count y = 2"
  assumes "yv \<noteq> 0"
  assumes "is_truncated yv 32"
  shows "unat (and (word_of_nat (topBit yv)) (31::64word)) = topBit yv"
proof -
  have mask: "(31::64word) = mask 5"
    by eval
  have "topBit yv \<in> word_inspection.supp yv"
    using assms(3) supp_contains_topBit_nonzero_iff by blast
  then have range: "topBit yv \<le> 31"
    using assms supp_is_truncated_range [of yv 32] unfolding is_truncated_def by fastforce
  obtain max where maxInSet: "max = topBit yv"
    by simp
  have word_range: "(word_of_nat (max)::64word) \<le> 31"
    by (simp add: local.range maxInSet word_of_nat_leq_len_1_32)
  have lt_pow2: "(topBit yv) < (2 ^ LENGTH(64))"
    using range by auto
  have foldAnd: "(and (word_of_nat (max)::64word) (31::64 word)) = (word_of_nat (max)::64word)"
    by (metis le_mask_imp_and_mask mask word_range)
  have "unat (word_of_nat (max)::64word) = max"
    unfolding maxInSet using unat_word_of_nat_unfold_64 lt_pow2 by presburger
  then show ?thesis
    unfolding maxInSet using foldAnd maxInSet by argo
qed

text \<open>botBit lemmas\<close>

lemma val_bit_count_bot_is_truncated_take_bit_32:
  assumes "y = new_int b yv"
  assumes "val_bit_count y = 2"
  assumes "yv \<noteq> 0"
  assumes "is_truncated yv 32"
  shows "(and (take_bit 32 (word_of_nat (botBit yv))) 31) =
         (and (word_of_nat (botBit yv))) 31"
proof -
  have "botBit yv \<in> word_inspection.supp yv"
    using assms(3) supp_contains_botBit_nonzero_iff by blast
  then have range: "botBit yv \<in> {0..31}"
    using assms supp_is_truncated_range [of yv 32] unfolding is_truncated_def by auto
  have "(and (take_bit 32 (botBit yv)) 31) = (and (botBit yv) 31)"
    using range take_bit_eq by simp
  then show ?thesis
    by (metis of_nat_and_eq of_nat_numeral take_bit_of_nat)
qed

lemma val_bit_count_unfold_botBit_32:
  assumes "y = new_int b yv"
  assumes "val_bit_count y = 2"
  assumes "yv \<noteq> 0"
  assumes "is_truncated yv 32"
  shows "unat (and (word_of_nat (botBit yv)) (31::64word)) = botBit yv"
proof -
  have mask: "(31::64word) = mask 5"
    by eval
  have "botBit yv \<in> word_inspection.supp yv"
    using assms(3) supp_contains_botBit_nonzero_iff by blast
  then have range: "botBit yv \<le> 31"
    using assms supp_is_truncated_range [of yv 32] unfolding is_truncated_def by fastforce
  obtain min where minInSet: "min = botBit yv"
    by simp
  have word_range: "(word_of_nat (min)::64word) \<le> 31"
    by (simp add: local.range minInSet word_of_nat_leq_len_1_32)
  have lt_pow2: "(botBit yv) < (2 ^ LENGTH(64))"
    using range by auto
  have foldAnd: "(and (word_of_nat (min)::64word) (31::64 word)) = (word_of_nat (min)::64word)"
    by (metis le_mask_imp_and_mask mask word_range)
  have "unat (word_of_nat (min)::64word) = min"
    unfolding minInSet using unat_word_of_nat_unfold_64 lt_pow2 by blast
  then show ?thesis
    unfolding minInSet using foldAnd minInSet by argo
qed

end