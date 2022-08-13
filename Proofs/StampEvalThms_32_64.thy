subsection \<open>Evaluation Stamp Theorems\<close>

theory StampEvalThms
  imports Semantics.IRTreeEvalThms
begin

subsubsection \<open>Support Lemmas for Stamps and Upper/Lower Bounds\<close>

(* these two were weirdly hard to prove given it should be by definition *)
lemma size32: "size v = 32" for v :: "32 word"
  using size_word.rep_eq
  using One_nat_def add.right_neutral add_Suc_right len_of_numeral_defs(2) len_of_numeral_defs(3) mult.right_neutral mult_Suc_right numeral_2_eq_2 numeral_Bit0
  by (smt (verit, del_insts) mult.commute)

lemma size64: "size v = 64" for v :: "64 word"
  using size_word.rep_eq
  using One_nat_def add.right_neutral add_Suc_right len_of_numeral_defs(2) len_of_numeral_defs(3) mult.right_neutral mult_Suc_right numeral_2_eq_2 numeral_Bit0
  by (smt (verit, del_insts) mult.commute)

declare [[show_types=true]]

(* Nb. sint_ge and sint_lt subsume these lemmas? *)
lemma signed_int_bottom32: "-(((2::int) ^ 31)) \<le> sint (v::int32)"
  using sint_range_size size32
  by (smt (verit, ccfv_SIG) One_nat_def Suc_pred add_Suc add_Suc_right eval_nat_numeral(3) nat.inject numeral_2_eq_2 numeral_Bit0 numeral_Bit1 zero_less_numeral)

lemma signed_int_top32: "(2 ^ 31) - 1 \<ge> sint (v::int32)"
  using sint_range_size size32
  by (smt (verit, ccfv_SIG) One_nat_def Suc_pred add_Suc add_Suc_right eval_nat_numeral(3) nat.inject numeral_2_eq_2 numeral_Bit0 numeral_Bit1 zero_less_numeral)

lemma lower_bounds_equiv32: "-(((2::int) ^ 31)) = (2::int) ^ 32 div 2 * - 1"
  by fastforce

lemma upper_bounds_equiv32: "(2::int) ^ 31 = (2::int) ^ 32 div 2"
  by simp

lemma bit_bounds_min32: "((fst (bit_bounds 32))) \<le> (sint (v::int32))"
  unfolding bit_bounds.simps fst_def using signed_int_bottom32 lower_bounds_equiv32
  by auto

lemma bit_bounds_max32: "((snd (bit_bounds 32))) \<ge> (sint (v::int32))"
  unfolding bit_bounds.simps fst_def using signed_int_top32 upper_bounds_equiv32
  by auto

lemma signed_int_bottom64: "-(((2::int) ^ 63)) \<le> sint (v::int64)"
  using sint_range_size size64
  by (smt (verit, ccfv_SIG) One_nat_def Suc_pred add_Suc add_Suc_right eval_nat_numeral(3) nat.inject numeral_2_eq_2 numeral_Bit0 numeral_Bit1 zero_less_numeral)

lemma signed_int_top64: "(2 ^ 63) - 1 \<ge> sint (v::int64)"
  using sint_range_size size64
  by (smt (verit, ccfv_SIG) One_nat_def Suc_pred add_Suc add_Suc_right eval_nat_numeral(3) nat.inject numeral_2_eq_2 numeral_Bit0 numeral_Bit1 zero_less_numeral)

lemma lower_bounds_equiv64: "-(((2::int) ^ 63)) = (2::int) ^ 64 div 2 * - 1"
  by fastforce

lemma upper_bounds_equiv64: "(2::int) ^ 63 = (2::int) ^ 64 div 2"
  by simp

lemma bit_bounds_min64: "((fst (bit_bounds 64))) \<le> (sint (v::int64))"
  unfolding bit_bounds.simps fst_def using signed_int_bottom64 lower_bounds_equiv64
  by auto

lemma bit_bounds_max64: "((snd (bit_bounds 64))) \<ge> (sint (v::int64))"
  unfolding bit_bounds.simps fst_def using signed_int_top64 upper_bounds_equiv64
  by auto

lemma unrestricted_32bit_always_valid [simp]:
  "valid_value (IntVal32 v) (unrestricted_stamp (IntegerStamp 32 lo hi))"
  using valid_value.simps(1) bit_bounds_min32 bit_bounds_max32
  using unrestricted_stamp.simps(2) by presburger

lemma unrestricted_64bit_always_valid [simp]:
  "valid_value (IntVal64 v) (unrestricted_stamp (IntegerStamp 64 lo hi))"
  using valid_value.simps(2) bit_bounds_min64 bit_bounds_max64
  using unrestricted_stamp.simps(2) by presburger

lemma unary_undef: "val = UndefVal \<Longrightarrow> unary_eval op val = UndefVal"
  by (cases op; auto)

lemma unary_obj: "val = ObjRef x \<Longrightarrow> unary_eval op val = UndefVal"
  by (cases op; auto)


(* MU: try to generalise the above for various bit lengths. *)
lemma lower_bounds_equiv: 
  assumes "N > 0"
  shows "-(((2::int) ^ (N-1))) = (2::int) ^ N div 2 * - 1"
  by (simp add: assms int_power_div_base)

lemma upper_bounds_equiv:
  assumes "N > 0"
  shows "(2::int) ^ (N-1) = (2::int) ^ N div 2"
  by (simp add: assms int_power_div_base)


text \<open>Next we show that casting a word to a wider word preserves any upper/lower bounds.\<close>

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
  

text \<open>Possibly helpful lemmas about $signed_take_bit$, to help with UnaryNarrow.
  Note: we could use signed to convert between bit-widths, instead of 
  signed\_take\_bit.  But this has to be done separately for each bit-width type.\<close>

value "sint(signed_take_bit 7 (128 :: int8))"


ML_val \<open>@{thm signed_take_bit_decr_length_iff}\<close>
declare [[show_types=true]]
ML_val \<open>@{thm signed_take_bit_int_less_exp}\<close>

lemma signed_take_bit_int_less_exp_word:
  assumes "n < LENGTH('a)"
  shows "sint(signed_take_bit n (k :: 'a :: len word)) < (2::int) ^ n"
  apply transfer
  by (smt (verit, best) not_take_bit_negative signed_take_bit_eq_take_bit_shift 
     signed_take_bit_int_less_exp take_bit_int_greater_self_iff) 

lemma signed_take_bit_int_greater_eq_minus_exp_word:
  assumes "n < LENGTH('a)"
  shows "- (2 ^ n) \<le> sint(signed_take_bit n (k :: 'a :: len word))"
  apply transfer
  by (smt (verit, best) signed_take_bit_int_greater_eq_minus_exp 
     signed_take_bit_int_greater_eq_self_iff signed_take_bit_int_less_exp)


text \<open>Some important lemmas showing that sign\_extend\_helper produces integer results
   whose range is determined by the inBits parameter.\<close>

lemma sign_extend_helper_output_range64:
  assumes "result = sign_extend_helper inBits outBits val"
  assumes "result = IntVal64 ival"
  shows "outBits = 64 \<and> -(2 ^ (inBits - 1)) \<le> sint ival \<and> sint ival \<le> 2 ^ (inBits - 1)"
(* or?  "(fst (bit_bounds inBits)) \<le> sint ival \<and> sint ival \<le> (snd (bit_bounds inBits))" *)
proof -
  have ival: "ival = (scast (signed_take_bit (inBits - 1) val))"
    using assms sign_extend_helper.simps
    by (smt (verit, ccfv_SIG) Value.distinct(3) Value.inject(2) Value.simps(14))
  then have lo: "-(2 ^ (inBits - 1)) \<le> sint (signed_take_bit (inBits - 1) val)"
    using signed_take_bit_int_greater_eq_minus_exp_word
    by (smt (verit, best) diff_le_self not_less power_increasing_iff sint_below_size wsst_TYs(3))
  then have lo2: "-(2 ^ (inBits - 1)) \<le> sint (scast (signed_take_bit (inBits - 1) val))"
    by (smt (verit, best) diff_less len_gt_0 less_Suc_eq power_strict_increasing_iff signed_scast_eq signed_take_bit_int_greater_eq_self_iff signed_take_bit_int_less_exp_word sint_range_size wsst_TYs(3))
  have hi: "sint (signed_take_bit (inBits - 1) val) < 2 ^ (inBits - 1)"
    using signed_take_bit_int_less_exp_word
    by (metis diff_le_mono less_imp_diff_less linorder_not_le one_le_numeral power_increasing sint_above_size wsst_TYs(3))
  then have hi2: "sint (scast (signed_take_bit (inBits - 1) val)) < 2 ^ (inBits - 1)"
    by (smt (verit) One_nat_def lo signed_scast_eq signed_take_bit_int_less_eq_self_iff sint_lt)
  show ?thesis 
    unfolding bit_bounds.simps fst_def ival
    using assms lo2 hi2 order_le_less
    by (smt (verit, best) Value.simps(14) Value.simps(8) sign_extend_helper.simps)
qed

lemma sign_extend_helper_output_range32:
  assumes "result = sign_extend_helper inBits outBits val"
  assumes "result = IntVal32 ival"
  shows "outBits \<le> 32 \<and> -(2 ^ (inBits - 1)) \<le> sint ival \<and> sint ival \<le> 2 ^ (inBits - 1)"
(* or? "(fst (bit_bounds inBits)) \<le> sint ival \<and> sint ival \<le> (snd (bit_bounds inBits))" *)
proof -
  have ival: "ival = (signed_take_bit (inBits - 1) val)"
    using assms sign_extend_helper.simps
    by (smt (verit, ccfv_SIG) Value.distinct(1) Value.inject(1) Value.simps(14) scast_id)
  have def: "result \<noteq> UndefVal"
    using assms
    by blast 
  then have ok: "0 < inBits \<and> inBits \<le> 32 \<and>
        inBits \<le> outBits \<and> 
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths"
    using assms sign_extend_helper_ok by blast
  then have lo: "-(2 ^ (inBits - 1)) \<le> sint (signed_take_bit (inBits - 1) val)"
    using signed_take_bit_int_greater_eq_minus_exp_word
    by (smt (verit, best) diff_le_self not_less power_increasing_iff sint_below_size wsst_TYs(3))
  have hi: "sint (signed_take_bit (inBits - 1) val) < 2 ^ (inBits - 1)"
    using signed_take_bit_int_less_exp_word
    by (metis diff_le_mono less_imp_diff_less linorder_not_le one_le_numeral power_increasing sint_above_size wsst_TYs(3))
  show ?thesis 
    unfolding bit_bounds.simps fst_def ival
    using assms ival ok lo hi order_le_less
    by force
qed




lemma take_bit_smaller_range:
  assumes "n < LENGTH('a)"
  assumes "val = sint(take_bit n (k :: 'a :: len word))"
  shows "0 \<le> val \<and> val < (2::int) ^ n"
  by (simp add: assms signed_take_bit_eq)

lemma take_bit_same_size_nochange:
  assumes "n = LENGTH('a)"
  shows "k = take_bit n (k :: 'a :: len word)"
  by (simp add: assms)

lemma take_bit_same_size_range:
  assumes "n = LENGTH('a)"
  assumes "val = take_bit n (k :: 'a :: len word)"
  shows "- (2 ^ n div 2) \<le> sint val \<and>
          sint val < 2 ^ n div 2"
  using assms lower_bounds_equiv sint_ge sint_lt by auto



lemma signed_take_bit_int_greater_eq_minus_exp_word:
  assumes "n < LENGTH('a)"
  shows "- (2 ^ n) \<le> sint(signed_take_bit n (k :: 'a :: len word))"
  apply transfer
  by (smt (verit, best) signed_take_bit_int_greater_eq_minus_exp 
     signed_take_bit_int_greater_eq_self_iff signed_take_bit_int_less_exp)

lemma zero_extend_helper_output_range32:
  assumes "result = zero_extend_helper inBits outBits val"
  assumes "result = IntVal32 ival"
  shows "outBits \<le> 32 \<and> -(2 ^ (inBits - 1)) \<le> sint ival \<and> sint ival \<le> 2 ^ (inBits - 1)"
(* or? "(fst (bit_bounds inBits)) \<le> sint ival \<and> sint ival \<le> (snd (bit_bounds inBits))" *)
proof -
  have ival: "ival = (signed_take_bit (inBits - 1) val)"
    using assms sign_extend_helper.simps
    by (smt (verit, ccfv_SIG) Value.distinct(1) Value.inject(1) Value.simps(14) scast_id)
  have def: "result \<noteq> UndefVal"
    using assms
    by blast 
  then have ok: "0 < inBits \<and> inBits \<le> 32 \<and>
        inBits \<le> outBits \<and> 
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths"
    using assms sign_extend_helper_ok by blast
  then have lo: "-(2 ^ (inBits - 1)) \<le> sint (signed_take_bit (inBits - 1) val)"
    using signed_take_bit_int_greater_eq_minus_exp_word
    by (smt (verit, best) diff_le_self not_less power_increasing_iff sint_below_size wsst_TYs(3))
  have hi: "sint (signed_take_bit (inBits - 1) val) < 2 ^ (inBits - 1)"
    using signed_take_bit_int_less_exp_word
    by (metis diff_le_mono less_imp_diff_less linorder_not_le one_le_numeral power_increasing sint_above_size wsst_TYs(3))
  show ?thesis 
    unfolding bit_bounds.simps fst_def ival
    using assms ival ok lo hi order_le_less
    by force
qed


subsubsection \<open>Support Lemmas for integer input/output size of unary and binary operators\<close>

text \<open>These help us to deduce integer sizes through expressions.  Not used yet.\<close>

lemma unary_abs_io32:
  assumes "result = unary_eval UnaryAbs val"
  assumes "result = IntVal32 r32"
  shows "\<exists>v32. val = IntVal32 v32"
  by (smt (verit, best) Value.distinct(9) Value.simps(6) assms(1) assms(2) intval_abs.elims unary_eval.simps(1))

lemma unary_abs_io64:
  assumes "result = unary_eval UnaryAbs val"
  assumes "result = IntVal64 r64"
  shows "\<exists>v64. val = IntVal64 v64"
  by (metis Value.collapse(2) Value.collapse(3) Value.collapse(4) Value.disc(3) Value.exhaust_disc Value.simps(8) assms(1) assms(2) intval_abs.simps(1) intval_abs.simps(5) is_IntVal32_def unary_eval.simps(1) unary_obj unary_undef)

lemma unary_neg_io32:
  assumes "result = unary_eval UnaryNeg val"
  assumes "result = IntVal32 r32"
  shows "\<exists>v32. val = IntVal32 v32"
  by (metis Value.disc(7) Value.distinct(1) assms(1) assms(2) intval_negate.elims is_IntVal64_def unary_eval.simps(2))

lemma unary_neg_io64:
  assumes "result = unary_eval UnaryNeg val"
  assumes "result = IntVal64 r64"
  shows "\<exists>v64. val = IntVal64 v64"
  by (metis Value.disc(3) Value.simps(8) assms(1) assms(2) intval_negate.elims is_IntVal32_def unary_eval.simps(2))



subsubsection \<open>Validity of UnaryAbs\<close>


text \<open>A set of lemmas for each evaltree step.
   Questions: 
   1. do we need separate 32/64 lemmas?  
      Yes, I think so, because almost every operator behaves differently on each width.
      And it makes the matching more direct, does not need is\_IntVal\_def etc.
   2. is this top-down approach (assume the result node evaluation) best?
      Maybe.  It seems to be the shortest/simplest trigger?
\<close>

lemma unary_abs_result64:
  assumes "[m,p] \<turnstile> (UnaryExpr UnaryAbs e) \<mapsto> IntVal64 v"
  obtains ve where "([m, p] \<turnstile> e \<mapsto> IntVal64 ve) \<and>
           v = (if ve <s 0 then -ve else ve)"
proof -
  obtain ve where "[m,p] \<turnstile> e \<mapsto> IntVal64 ve"
    by (smt (verit, best) assms UnaryExprE Value.distinct evalDet intval_abs.elims unary_eval.simps(1))
  then show ?thesis
    by (metis UnaryExprE Value.sel(2) assms evalDet intval_abs.simps(2) that unary_eval.simps(1))
qed
(* or backwards proof (for exists version of the rule):
  apply (rule UnaryExprE[OF 1])
  subgoal premises 2 for va
    using 2 apply (cases va; simp)
     apply (metis Value.distinct(9))
    apply (meson Value.inject(2))
    done
  done
*)

lemma unary_abs_result32:
  assumes 1:"[m,p] \<turnstile> (UnaryExpr UnaryAbs e) \<mapsto> IntVal32 v"
  shows "\<exists> ve. ([m, p] \<turnstile> e \<mapsto> IntVal32 ve) \<and>
           v = (if ve <s 0 then -ve else ve)"
proof -
  obtain ve where "[m,p] \<turnstile> e \<mapsto> IntVal32 ve"
    by (smt (verit, best) 1 UnaryExprE Value.distinct evalDet intval_abs.elims unary_eval.simps(1))
  then show ?thesis
    by (metis UnaryExprE Value.inject(1) assms evalDet intval_abs.simps(1) unary_eval.simps(1))
qed


lemma unary_abs_implies_valid_value:
  assumes 1:"[m,p] \<turnstile> expr \<mapsto> val"
  assumes 2:"result = unary_eval UnaryAbs val"
  assumes 3:"result \<noteq> UndefVal"
  assumes 4:"valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr UnaryAbs expr))"
proof -
  have 5:"[m,p] \<turnstile> (UnaryExpr UnaryAbs expr) \<mapsto> result"
    using assms by blast
  then have 6: "is_IntegerStamp (stamp_expr expr)"
    using assms valid_value.elims(2) by fastforce
  then consider v32 where "result = IntVal32 v32" | v64 where "result = IntVal64 v64"
    by (metis "2" "4" Stamp.collapse(1) intval_abs.simps(1) intval_abs.simps(2) unary_eval.simps(1) valid32or64)
  then show ?thesis
  proof cases
    case 1 (* 32 bit *)
    then obtain ve where ve: "([m, p] \<turnstile> expr \<mapsto> IntVal32 ve) \<and>
           result = (if ve <s 0 then IntVal32 (-ve) else IntVal32 ve)"
      using 5 unary_abs_result32 by metis
    then have 32: "val = IntVal32 ve"
      using assms(1) evalDet by presburger
    (* now deduce some stamp information *)
    then obtain b lo hi where se: "stamp_expr expr = IntegerStamp b lo hi"
      using 6 is_IntegerStamp_def by auto
    then have "((b=32 \<or> b=16 \<or> b=8 \<or> b=1) \<and> (lo \<le> sint ve) \<and> (sint ve \<le> hi))"
      using 4 32 se by simp 
    then have "stamp_expr (UnaryExpr UnaryAbs expr) = unrestricted_stamp (IntegerStamp 32 lo hi)"
      using se by fastforce
    then show ?thesis
      using "1" unrestricted_32bit_always_valid by presburger
  next
    case 2 (* 64 bit *)
    then obtain ve where ve: "([m, p] \<turnstile> expr \<mapsto> IntVal64 ve) \<and>
           result = (if ve <s 0 then IntVal64 (-ve) else IntVal64 ve)"
      using 5 unary_abs_result64 by metis 
    then have 64: "val = IntVal64 ve"
      using assms(1) evalDet by presburger
    (* now deduce some stamp information *)
    then obtain b lo hi where se: "stamp_expr expr = IntegerStamp b lo hi"
      using 6 is_IntegerStamp_def by auto
    then have range64: "b=64 \<and> (lo \<le> sint ve) \<and> (sint ve \<le> hi)"
      using 4 64 se by simp
    then have "stamp_expr (UnaryExpr UnaryAbs expr) = unrestricted_stamp (IntegerStamp b lo hi)"
      using se by simp
    then show ?thesis
      by (metis "2" range64 unrestricted_64bit_always_valid)
  qed
qed



subsubsection \<open>Validity of UnaryNeg\<close>

(* These lemmas are not needed:

lemma unary_neg_resultE:
  assumes "[m,p] \<turnstile> (UnaryExpr UnaryNeg e) \<mapsto> v"
  shows "\<exists> ve. (([m, p] \<turnstile> e \<mapsto> ve) \<and> (v = intval_negate ve))"
  using assms unary_eval.simps(2) by blast

lemma unary_neg_result64_exists:
  assumes 1: "[m,p] \<turnstile> (UnaryExpr UnaryNeg e) \<mapsto> IntVal64 v"
  shows "\<exists> ie. (([m, p] \<turnstile> e \<mapsto> IntVal64 ie) \<and> (v = -ie))" 
  apply (rule UnaryExprE[OF 1])
  subgoal premises 2 for va
    using 2 by (cases va; simp)
  done

lemma unary_neg_result64_obtains:
  assumes "[m,p] \<turnstile> (UnaryExpr UnaryNeg e) \<mapsto> IntVal64 v"
  obtains ie where "([m, p] \<turnstile> e \<mapsto> IntVal64 ie) \<and> (v = -ie)" 
  using assms unary_neg_resultE
  by (metis (no_types, lifting) Value.disc(3) Value.disc(6) Value.discI(2) Value.inject(2) intval_negate.elims is_IntVal32_def) 
or
proof -
  obtain ie where "[m,p] \<turnstile> e \<mapsto> IntVal64 ie"
    by (metis assms UnaryExprE Value.distinct(9) intval_negate.elims unary_eval.simps(2)) 
  then show ?thesis
    by (metis UnaryExprE Value.inject(2) assms evalDet intval_negate.simps(2) that unary_eval.simps(2))
qed


lemma unary_neg_result32:
  assumes 1:"[m,p] \<turnstile> (UnaryExpr UnaryNeg e) \<mapsto> IntVal32 v"
  shows "\<exists> ve. ([m, p] \<turnstile> e \<mapsto> IntVal32 ve) \<and>
           v = (if ve <s 0 then -ve else ve)"
proof -
  obtain ve where "[m,p] \<turnstile> e \<mapsto> IntVal32 ve"
    by (smt (verit, best) 1 UnaryExprE Value.distinct evalDet intval_abs.elims unary_eval.simps(1))
  then show ?thesis
    by (metis UnaryExprE Value.inject(1) assms evalDet intval_abs.simps(1) unary_eval.simps(1))
qed
*)

lemma unary_neg_implies_valid_value:
  assumes 1:"[m,p] \<turnstile> expr \<mapsto> val"
  assumes 2:"result = unary_eval UnaryNeg val"
  assumes 3:"result \<noteq> UndefVal"
  assumes 4:"valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr UnaryNeg expr))"
proof -
  have 6: "result = intval_negate val"
    using assms by auto
  then have 7: "is_IntegerStamp (stamp_expr expr)"
    using assms valid_value.elims(2) by fastforce
  then obtain b lo hi where se: "stamp_expr expr = IntegerStamp b lo hi"
    using 7 assms valid_value.elims(2) is_IntegerStamp_def by auto
  then have "stamp_expr (UnaryExpr UnaryNeg expr) = unrestricted_stamp (IntegerStamp (if b=64 then 64 else 32) lo hi)"
    using assms by auto
  then show ?thesis
    using assms 6 se 
    by (smt (verit, best) intval_negate.simps(1) intval_negate.simps(2) unrestricted_32bit_always_valid unrestricted_64bit_always_valid valid32or64 valid_int64 valid_value.simps(2)) 
qed


subsubsection \<open>Validity of UnaryNot\<close>

lemma unary_not_implies_valid_value:
  assumes 1:"[m,p] \<turnstile> expr \<mapsto> val"
  assumes 2:"result = unary_eval UnaryNot val"
  assumes 3:"result \<noteq> UndefVal"
  assumes 4:"valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr UnaryNot expr))"
proof -
  have 6: "result = intval_not val"
    using assms by auto
  then have 7: "is_IntegerStamp (stamp_expr expr)"
    using assms valid_value.elims(2) by fastforce
  then obtain b lo hi where se: "stamp_expr expr = IntegerStamp b lo hi"
    using 7 assms valid_value.elims(2) is_IntegerStamp_def by auto
  then have "stamp_expr (UnaryExpr UnaryNot expr) = unrestricted_stamp (IntegerStamp (if b=64 then 64 else 32) lo hi)"
    using assms by auto
  then show ?thesis
    using assms 6 se 
    by (smt (verit, best) intval_not.simps(1) intval_not.simps(2) unrestricted_32bit_always_valid unrestricted_64bit_always_valid valid32or64 valid_int64 valid_value.simps(2)) 
qed

subsubsection \<open>Validity of UnaryLogicNegation\<close>

lemma unary_logic_negation_implies_valid_value:
  assumes 1:"[m,p] \<turnstile> expr \<mapsto> val"
  assumes 2:"result = unary_eval UnaryLogicNegation val"
  assumes 3:"result \<noteq> UndefVal"
  assumes 4:"valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr UnaryLogicNegation expr))"
proof -
  have 6: "result = intval_logic_negation val"
    using assms by auto
  then have 7: "is_IntegerStamp (stamp_expr expr)"
    using assms valid_value.elims(2) by fastforce
  then obtain b lo hi where se: "stamp_expr expr = IntegerStamp b lo hi"
    using 7 assms valid_value.elims(2) is_IntegerStamp_def by auto
  then have "stamp_expr (UnaryExpr UnaryLogicNegation expr) = unrestricted_stamp (IntegerStamp (if b=64 then 64 else 32) lo hi)"
    using assms by auto
  then show ?thesis
    using assms 6 se 
    by (smt (verit, best) intval_logic_negation.simps(1) intval_logic_negation.simps(2) unrestricted_32bit_always_valid unrestricted_64bit_always_valid valid32or64 valid_int64 valid_value.simps(2)) 
qed


subsubsection \<open>Validity of UnaryNarrow\<close>

(* possibly helpful?
lemma sint_less:
  \<open>sint w < 2 ^ (LENGTH('a) - Suc 0)\<close> for w :: \<open>'a::len word\<close>

lift_definition word_sless :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> bool\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k < signed_take_bit (LENGTH('a) - Suc 0) l\<close>

lemma word_sle_eq [code]:
  \<open>a <=s b \<longleftrightarrow> sint a \<le> sint b\<close>

lemma word_sless_alt: "a <s b \<longleftrightarrow> sint a < sint b"

lemma uint_lt2p [iff]: "uint x < 2 ^ LENGTH('a)"
  for x :: "'a::len word"

lemma unsigned_less [simp]:
  \<open>unsigned w < 2 ^ LENGTH('b)\<close> for w :: \<open>'b::len word\<close>

? lemma word_of_int_2p: "(word_of_int (2 ^ n) :: 'a::len word) = 2 ^ n"

word_of_int_inverse:
    word_of_int ?r = ?a \<Longrightarrow>
    0 \<le> ?r \<Longrightarrow> 
    ?r < 2 ^ LENGTH(?'a) \<Longrightarrow> 
    uint ?a = ?r

Word.sint_uint: sint ?w = signed_take_bit (LENGTH(?'a) - Suc 0) (uint ?w)

lemma uint_range_size: "0 \<le> uint w \<and> uint w < 2 ^ size w"
lemma sint_range_size: "- (2 ^ (size w - Suc 0)) \<le> sint w \<and> sint w < 2 ^ (size w - Suc 0)"

lemma int_word_sint:
  \<open>sint (word_of_int x :: 'a::len word) 
   = (x + 2 ^ (LENGTH('a) - 1)) mod 2 ^ LENGTH('a) - 2 ^ (LENGTH('a) - 1)\<close>

From Bit_Operations:
lemma signed_take_bit_eq_if_positive:
  \<open>signed_take_bit n a = take_bit n a\<close> if \<open>\<not> bit a n\<close>

(lots of useful mask lemmas around this one)
lemma and_mask_wi: "word_of_int i AND mask n = word_of_int (take_bit n i)"

take_bit_eq_mod: \<open>take_bit n a = a mod 2 ^ n

mask_eq_exp_minus_1: \<open>mask n = 2 ^ n - 1\<close>


signed_take_bit lemmas
----------------------

lemma signed_take_bit_nonnegative_iff [simp]:
  \<open>0 \<le> signed_take_bit n k \<longleftrightarrow> \<not> bit k n\<close>

lemma signed_take_bit_negative_iff [simp]:
  \<open>signed_take_bit n k < 0 \<longleftrightarrow> bit k n\<close>

lemma signed_take_bit_int_greater_eq_minus_exp [simp]:
  \<open>- (2 ^ n) \<le> signed_take_bit n k\<close>

lemma signed_take_bit_int_less_exp [simp]:
  \<open>signed_take_bit n k < 2 ^ n\<close>

lemma signed_take_bit_eq_take_bit_shift:
  \<open>signed_take_bit n k = take_bit (Suc n) (k + 2 ^ n) - 2 ^ n\<close>
  for k :: int

MOD lemmas
----------
lemma word_mod_def [code]:
  "a mod b = word_of_int (uint a mod uint b)"

lemma mod_word_less:
  \<open>w mod v = w\<close> if \<open>w < v\<close> for w v :: \<open>'a::len word\<close>

lemma wi_less:
  "(word_of_int n < (word_of_int m :: 'a::len word)) =
    (n mod 2 ^ LENGTH('a) < m mod 2 ^ LENGTH('a))"


*) 


text \<open>Possibly helpful lemmas about mod - mostly not used now.\<close>

lemma uint_distr_mod:
  fixes n :: nat
  assumes "n < LENGTH('a)"
  shows "uint ((uval :: 'a :: len word) mod 2^n) = uint uval mod 2^n"
  by (metis take_bit_eq_mod unsigned_take_bit_eq)

lemma sint_mod_not_sign_bit:
  fixes n :: nat
  assumes "n < LENGTH('a)"
  shows "\<not> bit ((uval :: 'a :: len word) mod 2^n) LENGTH('a)"
  by simp

lemma sint_mod_upper_bound:
  fixes n :: nat
  assumes "n < LENGTH('a)"
  shows "sint ((uval :: 'a :: len word) mod 2^n) < 2^n"
  by (metis assms(1) signed_take_bit_eq take_bit_eq_mod take_bit_int_less_exp)

lemma sint_mod_lower_bound:
  fixes n :: nat
  assumes "n < LENGTH('a)"
  shows "0 \<le> sint ((uval :: 'a :: len word) mod 2^n)"
  unfolding sint_uint
  by (metis assms signed_take_bit_eq sint_uint take_bit_eq_mod take_bit_nonnegative)

lemma sint_mod_range: 
  fixes n :: nat
  assumes "n < LENGTH('a)"
  assumes "smaller = ((val :: 'a :: len word) mod 2^n)"
  shows "0 \<le> sint smaller \<and> sint smaller < 2^n"
  using assms sint_mod_upper_bound sint_mod_lower_bound
  using le_less by blast

lemma sint_mod_eq_uint:
  fixes n :: nat
  assumes "n < LENGTH('a)"
  shows "sint ((uval :: 'a :: len word) mod 2^n) = uint (uval mod 2^n)"
  unfolding sint_uint
  by (metis Suc_pred assms le_less len_gt_0 signed_take_bit_eq sint_uint take_bit_eq_mod
            take_bit_signed_take_bit unsigned_take_bit_eq)



lemma unary_narrow_helper32:
  assumes "[m,p] \<turnstile> expr \<mapsto> IntVal32 i32"
  assumes "stamp_expr expr = IntegerStamp b lo hi"
  assumes "r32 = signed_take_bit (outBits - 1) i32"
  assumes "result = IntVal32 r32"
  assumes "outBits=32 \<or> outBits=16 \<or> outBits=8 \<or> outBits=1"
  assumes "stamp_expr (UnaryExpr (UnaryNarrow inBits outBits) expr) 
             = unrestricted_stamp (IntegerStamp outBits lo hi)"
  shows "valid_value result (stamp_expr (UnaryExpr (UnaryNarrow inBits outBits) expr))"
proof -
  have hi: "sint r32 < 2^(outBits-1)"
    using assms signed_take_bit_int_less_exp_word
    by (metis diff_le_mono less_imp_diff_less linorder_not_le one_le_numeral 
          power_increasing sint_above_size word_size)
  then have lo: "- (2^(outBits-1)) \<le> sint r32"
    using assms signed_take_bit_int_greater_eq_minus_exp_word
    by (smt (verit, best) diff_le_self less_le_trans power_less_imp_less_exp sint_ge)
  then show ?thesis
    using assms lo hi apply simp
    by (metis int_power_div_base lessI zero_less_numeral) 
qed

lemma unary_narrow_helper64:
  assumes "[m,p] \<turnstile> expr \<mapsto> IntVal64 i64"
  assumes "stamp_expr expr = IntegerStamp b lo hi"
  assumes "r32 = signed_take_bit (outBits - 1) (scast i64)"
  assumes "result = IntVal32 r32"
  assumes "outBits=32 \<or> outBits=16 \<or> outBits=8 \<or> outBits=1"
  assumes "stamp_expr (UnaryExpr (UnaryNarrow inBits outBits) expr) 
             = unrestricted_stamp (IntegerStamp outBits lo hi)"
  shows "valid_value result (stamp_expr (UnaryExpr (UnaryNarrow inBits outBits) expr))"
proof -
  have hi: "sint r32 < 2^(outBits-1)"
    using assms signed_take_bit_int_less_exp_word
    by (metis diff_le_mono less_imp_diff_less linorder_not_le one_le_numeral 
          power_increasing sint_above_size word_size)
  then have lo: "- (2^(outBits-1)) \<le> sint r32"
    using assms signed_take_bit_int_greater_eq_minus_exp_word
    by (smt (verit, best) diff_le_self less_le_trans power_less_imp_less_exp sint_ge)
  then show ?thesis
    using assms lo hi apply simp
    by (metis int_power_div_base lessI zero_less_numeral)
qed


lemma unary_narrow_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval (UnaryNarrow inBits outBits) val"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr (UnaryNarrow inBits outBits) expr))"
proof -
  (* make some deductions about the input stamp of expr *)
  have i: "is_IntegerStamp (stamp_expr expr)"
    using assms valid_value.elims(2) by fastforce 
  then obtain b lo hi where se:"stamp_expr expr = IntegerStamp b lo hi"
    by (auto simp add: assms valid_value.elims(2) is_IntegerStamp_def)
  then have u: "stamp_expr (UnaryExpr (UnaryNarrow inBits outBits) expr) 
             = unrestricted_stamp (IntegerStamp outBits lo hi)"
    by simp
  (* make some general deductions about result, then split into 32/64 bit cases *)
  have r: "result = intval_narrow inBits outBits val"
    by (simp add: assms(2)) 
  then have ok: "0 < outBits \<and> outBits \<le> inBits \<and> 
        outBits \<in> valid_int_widths \<and> inBits \<in> valid_int_widths"
      using assms intval_narrow_ok by simp 
  then consider i32 where "val = IntVal32 i32" | i64 where "val = IntVal64 i64"
    using assms by (metis se valid32or64) 
  then show ?thesis
  proof cases
    case 1 (* input is IntVal32 and inBits < 64 *)
    then have r1: "result = narrow_helper inBits outBits i32"
      using assms r by (metis intval_narrow.simps(1)) 
    then have r2: "result = (IntVal32 (signed_take_bit (outBits - 1) i32))"
      using assms by (metis narrow_helper.simps)
    then obtain r32 where 
      r32: "result = IntVal32 r32 \<and> r32 = signed_take_bit (outBits - 1) i32"
      by simp
    then have "outBits=32 \<or> outBits=16 \<or> outBits=8 \<or> outBits=1"
      using ok 1 assms by force 
    then show ?thesis
      using ok 1 assms u r32 se unary_narrow_helper32 by force
  next 
    case 2  (* input is IntVal64 and inBits=64 *)
    then have in64: "inBits = 64"
      using assms ok intval_narrow.simps(2) r by presburger 
    then show ?thesis
      proof (cases "outBits = 64")
        case True
        then show ?thesis
          using 2 in64 r u intval_narrow.simps(2) unrestricted_64bit_always_valid by presburger
      next
        case False
        (* Nb. proof differs from case 1 above by scast, so not easy to combine them. *)
        then have out32: "outBits=32 \<or> outBits=16 \<or> outBits=8 \<or> outBits=1"
          using ok assms by force 
        then have r1: "result = narrow_helper inBits outBits (scast i64)"
          using assms "2" False in64 r ok narrow_takes_64 by simp
        then have r2: "result = (IntVal32 (signed_take_bit (outBits - 1) (scast i64)))"
          using assms by (metis narrow_helper.simps)
        then obtain r32 where 
          r32: "result = IntVal32 r32 \<and> r32 = signed_take_bit (outBits - 1) (scast i64)"
          by simp
        then show ?thesis
          using assms 2 r32 out32 u se unary_narrow_helper64 by blast 
      qed
  qed
qed



subsubsection \<open>Validity of UnarySignExtend\<close>

(*
lemma unary_sign_extend_helper32:
  assumes "[m,p] \<turnstile> expr \<mapsto> IntVal32 i32"
  assumes "stamp_expr expr = IntegerStamp b lo hi"
  assumes "r32 = signed_take_bit (outBits - 1) i32"
  assumes "result = IntVal32 r32"
  assumes "outBits=32 \<or> outBits=16 \<or> outBits=8 \<or> outBits=1"
  assumes "stamp_expr (UnaryExpr (UnaryNarrow inBits outBits) expr) 
             = unrestricted_stamp (IntegerStamp outBits lo hi)"
  shows "valid_value result (stamp_expr (UnaryExpr (UnaryNarrow inBits outBits) expr))"
proof -
  have hi: "sint r32 < 2^(outBits-1)"
    using assms signed_take_bit_int_less_exp_word
    by (metis diff_le_mono less_imp_diff_less linorder_not_le one_le_numeral 
          power_increasing sint_above_size word_size)
  then have lo: "- (2^(outBits-1)) \<le> sint r32"
    using assms signed_take_bit_int_greater_eq_minus_exp_word
    by (smt (verit, best) diff_le_self less_le_trans power_less_imp_less_exp sint_ge)
  then show ?thesis
    using assms lo hi apply simp
    by (metis int_power_div_base lessI zero_less_numeral) 
qed


lemma sign_extend_range:
  assumes "(result :: int64) = scast (v :: 'a :: len word)"
  shows "fst (bit_bounds LENGTH('a)) \<le> sint result \<and> sint result \<le> snd (bit_bounds LENGTH('a))"
  using scast_bit_bounds
  using assms len_gt_0 by blast 
*)


lemma valid_sign_extend32_or_less:
  assumes "(result :: int32) = scast (v :: 'a :: len word)"
  assumes "LENGTH('a) = 32 \<or> LENGTH('a) = 16 \<or> LENGTH('a) = 8 \<or> LENGTH('a) = 1"
  shows "valid_value (IntVal32 result) (IntegerStamp LENGTH('a) 
                              (fst (bit_bounds (LENGTH('a)))) 
                              (snd (bit_bounds (LENGTH('a)))))"
  unfolding valid_value.simps 
  using scast_bigger_bit_bounds assms by blast


lemma valid_sign_extend64:
  assumes "(result :: int64) = scast (v :: 'a :: len word)"
  shows "valid_value (IntVal64 result) (IntegerStamp 64 
                              (fst (bit_bounds (LENGTH('a)))) 
                              (snd (bit_bounds (LENGTH('a)))))"
  unfolding valid_value.simps 
  using scast_bigger_bit_bounds
  using assms(1) len_gt_0 by blast


lemma unary_sign_extend_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval (UnarySignExtend inBits outBits) val"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr (UnarySignExtend inBits outBits) expr))"
proof -
  (* make some deductions about the input stamp of expr *)
  have i: "is_IntegerStamp (stamp_expr expr)"
    using assms valid_value.elims(2) by fastforce 
  then obtain b lo hi where se:"stamp_expr expr = IntegerStamp b lo hi"
    by (auto simp add: assms valid_value.elims(2) is_IntegerStamp_def)
  then have u: "stamp_expr (UnaryExpr (UnarySignExtend inBits outBits) expr) 
             = unrestricted_stamp (IntegerStamp outBits lo hi)"
    by simp
  then show ?thesis
  proof (cases "is_IntVal64 val")
    case True
    then show ?thesis
      using assms u unrestricted_64bit_always_valid
      using is_IntVal64_def by fastforce
  next
    case False
    then obtain i32 where i32: "result = sign_extend_helper inBits outBits i32"
      using assms intval_sign_extend.simps
      by (metis is_IntVal64_def se unary_eval.simps(6) valid32or64)
    then have ok: "0 < inBits \<and> inBits \<le> 32 \<and> inBits \<le> outBits \<and> 
        outBits \<in> valid_int_widths \<and> inBits \<in> valid_int_widths"
      using assms sign_extend_helper_ok by blast
    then show ?thesis
    proof (cases "outBits = 64")
      case True
      then obtain r64 where "result = IntVal64 r64"
        by (metis assms(3) i32 sign_extend_helper.simps) 
      then show ?thesis
        using True u unrestricted_64bit_always_valid by presburger
    next
      case False
      then obtain r32 where r32: "result = IntVal32 r32"
        using ok i32 by force
      then have lohi: "-(2 ^ (inBits - 1)) \<le> sint r32 \<and> sint r32 < 2 ^ (inBits - 1)"
        using sign_extend_helper_output_range32
        by (smt (verit, ccfv_threshold) False Value.inject(1) assms(3) diff_le_self i32 linorder_not_le power_less_imp_less_exp sign_extend_helper.simps signed_take_bit_int_less_exp_word sint_lt) 
      then have bnds: "fst (bit_bounds inBits) \<le> sint r32 \<and> sint r32 \<le> snd (bit_bounds inBits)"
        unfolding bit_bounds.simps fst_def
        using ok lower_bounds_equiv upper_bounds_equiv by simp
      then have v: "valid_value result (unrestricted_stamp (IntegerStamp inBits lo hi))"
        using ok r32 by force 
      then have "outBits=1 \<or> outBits=8 \<or> outBits=16 \<or> outBits=32"
        using ok False by fastforce
      then show ?thesis
        unfolding u using ok v r32 larger_stamp32_always_valid by presburger 
    qed
  qed
qed


subsubsection \<open>Validity of UnaryZeroExtend\<close>

lemma unary_zero_extend_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval (UnaryZeroExtend inBits outBits) val"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr (UnaryZeroExtend inBits outBits) expr))"
  proof -
  (* make some deductions about the input stamp of expr *)
  have i: "is_IntegerStamp (stamp_expr expr)"
    using assms valid_value.elims(2) by fastforce 
  then obtain b lo hi where se:"stamp_expr expr = IntegerStamp b lo hi"
    by (auto simp add: assms valid_value.elims(2) is_IntegerStamp_def)
  then have u: "stamp_expr (UnaryExpr (UnaryZeroExtend inBits outBits) expr) 
             = unrestricted_stamp (IntegerStamp outBits lo hi)"
    by simp
  then show ?thesis
  proof (cases "is_IntVal64 val")
    case True
    then show ?thesis
      using assms u unrestricted_64bit_always_valid
      using is_IntVal64_def by fastforce
  next
    case False
    then obtain i32 where i32: "result = zero_extend_helper inBits outBits i32"
      using assms intval_zero_extend.simps
      by (metis is_IntVal64_def se unary_eval.simps(7) valid32or64)
    then have ok: "0 < inBits \<and> inBits \<le> 32 \<and> inBits \<le> outBits \<and> 
        outBits \<in> valid_int_widths \<and> inBits \<in> valid_int_widths"
      using assms zero_extend_helper_ok by blast
    then show ?thesis
    proof (cases "outBits = 64")
      case True
      then obtain r64 where "result = IntVal64 r64"
        by (metis assms(3) i32 zero_extend_helper.simps) 
      then show ?thesis
        using True u unrestricted_64bit_always_valid by presburger
    next
      case False
      then have le32: "outBits \<le> 32"
        using ok by force
      then obtain r32 where result32: "result = IntVal32 r32"
        using ok i32 by force
      then have r32: "r32 =  take_bit inBits i32"
        using ok i32 le32 zero_extend_helper.simps False by force 
      then show ?thesis
      proof (cases "inBits = 32")  (* we return the whole 32 bits, so signed. *)
        case True
        then have range32: "-(2 ^ (inBits - 1)) \<le> sint r32 \<and> sint r32 < 2 ^ (inBits - 1)"
          by (metis One_nat_def sint_range_size size32)
        then show ?thesis
          using ok True result32 u
          by (metis le32 le_antisym unrestricted_32bit_always_valid)
      next
        case False  (* inBits < 32 bits, so range is 0 .. 2^inBits *)
        then have lt32: "inBits < 32"
          using ok le32 by simp
        then have range16: "0 \<le> sint r32 \<and> sint r32 < 2 ^ inBits"
          using ok i32 result32 r32
          by (metis size32 word_size take_bit_smaller_range) 
        then show ?thesis
          unfolding u using ok i32 result32 r32 lt32  
(* The problem here is we cannot know the range / meaning of (IntVal32 0xFF).
   Is this a 32-bit value with value 255, or 8-bit with value -128?
   The unrestricted_stamp assumes signed ranges, but do not have enough context.
*)
      qed
      then have lohi: "-(2 ^ (inBits - 1)) \<le> sint r32 \<and> sint r32 < 2 ^ (inBits - 1)"
        using zero_extend_helper_output_range32
        by (smt (verit, ccfv_threshold) False Value.inject(1) assms(3) diff_le_self i32 linorder_not_le power_less_imp_less_exp zero_extend_helper.simps signed_take_bit_int_less_exp_word sint_lt) 
      then have bnds: "fst (bit_bounds inBits) \<le> sint r32 \<and> sint r32 \<le> snd (bit_bounds inBits)"
        unfolding bit_bounds.simps fst_def
        using ok lower_bounds_equiv upper_bounds_equiv by simp
      then have v: "valid_value result (unrestricted_stamp (IntegerStamp inBits lo hi))"
        using ok r32 by force 
      then have "outBits=1 \<or> outBits=8 \<or> outBits=16 \<or> outBits=32"
        using ok False by fastforce
      then show ?thesis
        unfolding u using ok v r32 larger_stamp32_always_valid by presburger 
    qed
  qed
qed



subsubsection \<open>Validity of all Unary Operators\<close>

lemma unary_eval_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
proof (cases op)
  case UnaryAbs
  then show ?thesis using assms unary_abs_implies_valid_value by presburger
next
  case UnaryNeg
  then show ?thesis using assms unary_neg_implies_valid_value by presburger
next
  case UnaryNot
  then show ?thesis using assms unary_not_implies_valid_value by presburger
next
  case UnaryLogicNegation
  then show ?thesis using assms unary_logic_negation_implies_valid_value by presburger
next
  case (UnaryNarrow x51 x52)
  then show ?thesis using assms unary_narrow_implies_valid_value by presburger
next
  case (UnarySignExtend x61 x62)
  then show ?thesis using assms unary_sign_extend_implies_valid_value by presburger
next
  case (UnaryZeroExtend x71 x72)
  then show ?thesis using assms unary_zero_extend_implies_valid_value by presburger
qed



subsubsection \<open>Support Lemmas for Binary Operators\<close>

lemma binary_undef: "v1 = UndefVal \<or> v2 = UndefVal \<Longrightarrow> bin_eval op v1 v2 = UndefVal"
  by (cases op; auto)

lemma binary_obj: "v1 = ObjRef x \<or> v2 = ObjRef y \<Longrightarrow> bin_eval op v1 v2 = UndefVal"
  by (cases op; auto)

(* Not true any more, now we have 16 and 8 bit stamps.
lemma binary_eval_bits_equal:
  assumes "result = bin_eval op val1 val2"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val1 (IntegerStamp b1 lo1 hi1)"
  assumes "valid_value val2 (IntegerStamp b2 lo2 hi2)"
  shows "b1 = b2"
  using assms 
  apply (cases op; cases val1; cases val2; auto) (*slow*)
  sorry
*)

(* Not true any more, now that the bit-shift operators can take mixed 32/64 bit arguments.
lemma binary_eval_values:
  assumes "\<exists>x y. result = IntVal32 x \<or> result = IntVal64 y"
  assumes "result = bin_eval op val1 val2"
  shows" \<exists>x32 x64 y32 y64. val1 = IntVal32 x32 \<and> val2 = IntVal32 y32 \<or> val1 = IntVal64 x64 \<and> val2 = IntVal64 y64"
  using assms apply (cases result)
      apply simp apply (cases op; cases val1; cases val2; auto)
    apply (cases op; cases val1; cases val2; auto) by auto+
*)

lemma binary_eval_implies_valid_value:
  assumes "[m,p] \<turnstile> expr1 \<mapsto> val1"
  assumes "[m,p] \<turnstile> expr2 \<mapsto> val2"
  assumes "result = bin_eval op val1 val2"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val1 (stamp_expr expr1)"
  assumes "valid_value val2 (stamp_expr expr2)"
  shows "valid_value result (stamp_expr (BinaryExpr op expr1 expr2))"
proof -
  have is_IntVal: "\<exists> x y. result = IntVal32 x \<or> result = IntVal64 y"
    using assms(1,2,3,4) apply (cases op; auto; cases val1; auto; cases val2; auto)
    by (meson Values.bool_to_val.elims)+
  then have expr1_intstamp: "is_IntegerStamp (stamp_expr expr1)"
    using assms(1,3,4,5) apply (cases "(stamp_expr expr1)"; auto simp: valid_VoidStamp binary_undef)
    using valid_ObjStamp binary_obj apply (metis assms(4))
    using valid_ObjStamp binary_obj by (metis assms(4))
  from is_IntVal have expr2_intstamp: "is_IntegerStamp (stamp_expr expr2)"
    using assms(2,3,4,6) apply (cases "(stamp_expr expr2)"; auto simp: valid_VoidStamp binary_undef)
    using valid_ObjStamp binary_obj apply (metis assms(4))
    using valid_ObjStamp binary_obj by (metis assms(4))
  from expr1_intstamp obtain b1 lo1 hi1 where stamp_expr1_def: "stamp_expr expr1 = (IntegerStamp b1 lo1 hi1)"
    using is_IntegerStamp_def by auto
  from expr2_intstamp obtain b2 lo2 hi2 where stamp_expr2_def: "stamp_expr expr2 = (IntegerStamp b2 lo2 hi2)"
    using is_IntegerStamp_def by auto

(* Problem: this is no longer true for the bit-shifting operators:
  have "\<exists> x32 x64 y32 y64 . (val1 = IntVal32 x32 \<and> val2 = IntVal32 y32) \<or> (val1 = IntVal64 x64 \<and> val2 = IntVal64 y64)"
    using is_IntVal assms(3) binary_eval_values
    by presburger
*)

(* TODO: we have a problem here with the 32-bit case, because
   the input stamps could be 32/16/8 bits.
   stamp_binary requires them to be the same, 
   but evaltree does not.
   Solution 1: add a graph invariant and then a tree invariant?
   Solution 2: relax stamp_binary to expand input stamps to 32-bit?
*)
  have "b1 = b2"
    using assms(3,4,5,6) stamp_expr1_def stamp_expr2_def
    sorry
  then have stamp_def: "stamp_expr (BinaryExpr op expr1 expr2) = 
      (if op \<notin> fixed_32 \<and> b1=64
             then unrestricted_stamp (IntegerStamp 64 lo1 hi1)
             else unrestricted_stamp (IntegerStamp 32 lo1 hi1))"
    using stamp_expr.simps(2) stamp_binary.simps(1)
    using stamp_expr1_def stamp_expr2_def by presburger
  show ?thesis 
    proof (cases "op \<notin> fixed_32 \<and> b1=64")
      case True
      then obtain x where bit64: "result = IntVal64 x" 
        using stamp_expr1_def assms by (cases op; cases val1; cases val2; simp) (*slow*)
      then show ?thesis
        by (metis True stamp_def unrestricted_64bit_always_valid) 
    next
      case False
      then obtain x where bit32: "result = IntVal32 x"
        using assms stamp_expr1_def apply (cases op; cases val1; cases val2; auto) (*slow*)
        by (meson Values.bool_to_val.elims)+
      then show ?thesis
        using False stamp_def unrestricted_32bit_always_valid by presburger 
    qed
  qed



subsubsection \<open>Validity of Stamp Meet and Join Operators\<close>

lemma stamp_meet_is_valid:
  assumes "valid_value val stamp1 \<or> valid_value val stamp2"
  assumes "meet stamp1 stamp2 \<noteq> IllegalStamp"
  shows "valid_value val (meet stamp1 stamp2)"
  using assms 
proof (cases stamp1)
  case VoidStamp
    then show ?thesis
      by (metis Stamp.exhaust assms(1) assms(2) meet.simps(1) meet.simps(37) meet.simps(44) meet.simps(51) meet.simps(58) meet.simps(65) meet.simps(66) meet.simps(67))
  next
  case (IntegerStamp b lo hi)
    obtain b2 lo2 hi2 where stamp2_def: "stamp2 = IntegerStamp b2 lo2 hi2"
      by (metis IntegerStamp assms(2) meet.simps(45) meet.simps(52) meet.simps(59) meet.simps(6) meet.simps(65) meet.simps(66) meet.simps(67) unrestricted_stamp.cases)
    then have "b = b2" using meet.simps(2) assms(2) 
      by (metis IntegerStamp)
    then have meet_def: "meet stamp1 stamp2 = (IntegerStamp b (min lo lo2) (max hi hi2))"
      by (simp add: IntegerStamp stamp2_def)
    then show ?thesis proof (cases "b = 64")
      case True
      then obtain x where val_def: "val = IntVal64 x"
        using IntegerStamp assms(1) valid64
        using \<open>b = b2\<close> stamp2_def by blast
      have min: "sint x \<ge> min lo lo2" 
        using val_def
        using IntegerStamp assms(1)
        using stamp2_def by force
      have max: "sint x \<le> max hi hi2" 
        using val_def
        using IntegerStamp assms(1)
        using stamp2_def by force
      from min max show ?thesis
        by (simp add: True meet_def val_def)
    next
      case False
      then have bit32: "b = 32 \<or> b = 16 \<or> b = 8 \<or> b = 1"
        using assms(1) IntegerStamp valid_value.simps valid32or64_both
        by (metis \<open>b = b2\<close> stamp2_def)
      then obtain x where val_def: "val = IntVal32 x"
        using IntegerStamp assms(1) valid32 valid_int16 valid_int8 valid_int1
        using \<open>b = b2\<close> stamp2_def by blast 
      have min: "sint x \<ge> min lo lo2" 
        using val_def
        using IntegerStamp assms(1)
        using stamp2_def by force
      have max: "sint x \<le> max hi hi2" 
        using val_def
        using IntegerStamp assms(1)
        using stamp2_def by force
      from min max show ?thesis
        using bit32 meet_def val_def valid_value.simps(1) by presburger
    qed
  next
    case (KlassPointerStamp x31 x32)
    then show ?thesis using assms valid_value.elims(2)
      by fastforce
  next
    case (MethodCountersPointerStamp x41 x42)
    then show ?thesis using assms valid_value.elims(2)
      by fastforce
  next
    case (MethodPointersStamp x51 x52)
    then show ?thesis using assms valid_value.elims(2)
      by fastforce
  next
    case (ObjectStamp x61 x62 x63 x64)
    then show ?thesis using assms
      using meet.simps(34) by blast
  next
    case (RawPointerStamp x71 x72)
    then show ?thesis using assms
      using meet.simps(35) by blast
  next
    case IllegalStamp
    then show ?thesis using assms
      using meet.simps(36) by blast
qed


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
    using assms
    by (metis Stamp.distinct(13) Stamp.distinct(25) compatible.elims(2) meet.simps(1) meet.simps(2))
  then show ?thesis using stamp_meet_is_valid using stamp_expr.simps(6)
    using assms(2) assms(6) by presburger
qed



subsubsection \<open>Validity of Whole Expression Tree Evaluation\<close>

experiment begin
lemma stamp_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  shows "valid_value val (stamp_expr expr)"
  using assms proof (induction expr val)
  case (UnaryExpr expr val result op)
    then show ?case using unary_eval_implies_valid_value by simp
  next
    case (BinaryExpr expr1 val1 expr2 val2 result op)
    then show ?case using binary_eval_implies_valid_value by simp
  next
    case (ConditionalExpr cond condv expr expr1 expr2 val)
    then show ?case using conditional_eval_implies_valid_value sorry
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

lemma upper_bound_32:
  assumes "val = IntVal32 v"
  assumes "\<exists> l h. s = (IntegerStamp 32 l h)"
  shows "valid_value val s \<Longrightarrow> sint v \<le> (stpi_upper s)"
  using assms by force

lemma upper_bound_64:
  assumes "val = IntVal64 v"
  assumes "\<exists> l h. s = (IntegerStamp 64 l h)"
  shows "valid_value val s \<Longrightarrow> sint v \<le> (stpi_upper s)"
  using assms by force

lemma lower_bound_32:
  assumes "val = IntVal32 v"
  assumes "\<exists> l h. s = (IntegerStamp 32 l h)"
  shows "valid_value val s \<Longrightarrow> sint v \<ge> (stpi_lower s)"
  using assms by force

lemma lower_bound_64:
  assumes "val = IntVal64 v"
  assumes "\<exists> l h. s = (IntegerStamp 64 l h)"
  shows "valid_value val s \<Longrightarrow> sint v \<ge> (stpi_lower s)"
  using assms
  by force

(* these two proofs should really not be so tricky *)
lemma stamp_under_semantics:
  assumes "stamp_under (stamp_expr x) (stamp_expr y)"
  assumes "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan x y) \<mapsto> v"
  assumes xvalid: "(\<forall>m p v. ([m, p] \<turnstile> x \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr x))"
  assumes yvalid: "(\<forall>m p v. ([m, p] \<turnstile> y \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr y))"
  shows "val_to_bool v"
proof -
  obtain xval where xval_def: "[m, p] \<turnstile> x \<mapsto> xval"
    using assms(2) by blast
  obtain yval where yval_def: "[m, p] \<turnstile> y \<mapsto> yval"
    using assms(2) by blast
  have "is_IntVal32 xval \<or> is_IntVal64 xval"
    by (metis BinaryExprE Value.collapse(3) Value.collapse(4) Value.exhaust_disc assms(2) binary_obj evalDet evaltree_not_undef valid_value.simps(19) xval_def xvalid)
  have "is_IntVal32 yval \<or> is_IntVal64 yval"
    by (metis BinaryExprE Value.collapse(3) Value.collapse(4) Value.exhaust_disc assms(2) binary_obj evalDet evaltree_not_undef valid_value.simps(19) yval_def yvalid)
  have "is_IntVal32 xval = is_IntVal32 yval"
    using BinaryExprE Value.collapse(2) \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> assms(2) bin_eval.simps(11) evalDet intval_less_than.simps(12) intval_less_than.simps(5) is_IntVal32_def xval_def yval_def
    by (smt (verit, ccfv_SIG) bin_eval.simps(12))
  have "is_IntVal64 xval = is_IntVal64 yval"
    using \<open>is_IntVal32 xval = is_IntVal32 yval\<close> \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> by blast
  have "(intval_less_than xval yval) \<noteq> UndefVal"
    using assms(2)
    by (metis bin_eval.simps(12) evalDet unfold_binary xval_def yval_def)
  have "is_IntVal32 xval \<Longrightarrow> ((\<exists> lo hi. stamp_expr x = IntegerStamp 32 lo hi) \<and> (\<exists> lo hi. stamp_expr y = IntegerStamp 32 lo hi))"
    (* using assms(2) binary_eval_bits_equal valid_value.elims(2) xval_def
    by (metis Value.distinct(9) Value.distinct_disc(9) \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> \<open>is_IntVal64 xval = is_IntVal64 yval\<close> is_IntVal32_def xvalid yval_def yvalid)
    *)
    sorry
  have "is_IntVal64 xval \<Longrightarrow> ((\<exists> lo hi. stamp_expr x = IntegerStamp 64 lo hi) \<and> (\<exists> lo hi. stamp_expr y = IntegerStamp 64 lo hi))"
    (* by (metis (full_types) \<open>is_IntVal64 xval = is_IntVal64 yval\<close> is_IntVal64_def stamprange valid_value.simps(2) xval_def xvalid yval_def yvalid)
    *)
    sorry
  have xvalid: "valid_value xval (stamp_expr x)"
    using xvalid xval_def by auto
  have yvalid: "valid_value yval (stamp_expr y)"
    using yvalid yval_def by auto
  { assume c: "is_IntVal32 xval"
    obtain xxval where x32: "xval = IntVal32 xxval"
      using c is_IntVal32_def by blast
    obtain yyval where y32: "yval = IntVal32 yyval"
      using \<open>is_IntVal32 xval = is_IntVal32 yval\<close> c is_IntVal32_def by auto
    have xs: "\<exists> lo hi. stamp_expr x = IntegerStamp 32 lo hi"
      by (simp add: \<open>is_IntVal32 xval \<Longrightarrow> (\<exists>lo hi. stamp_expr x = IntegerStamp 32 lo hi) \<and> (\<exists>lo hi. stamp_expr y = IntegerStamp 32 lo hi)\<close> c)
    have ys: "\<exists> lo hi. stamp_expr y = IntegerStamp 32 lo hi"
      using \<open>is_IntVal32 xval \<Longrightarrow> (\<exists>lo hi. stamp_expr x = IntegerStamp 32 lo hi) \<and> (\<exists>lo hi. stamp_expr y = IntegerStamp 32 lo hi)\<close> c by blast
    have "sint xxval \<le> stpi_upper (stamp_expr x)"
      using upper_bound_32 x32 xs xvalid by presburger
    have "stpi_lower (stamp_expr y) \<le> sint yyval"
      using lower_bound_32 y32 ys yvalid by presburger
    have "stpi_upper (stamp_expr x) < stpi_lower (stamp_expr y)"
      using assms(1) unfolding stamp_under.simps
      by auto
    then have "xxval <s yyval"
      using assms(1) unfolding stamp_under.simps
      using \<open>sint xxval \<sqsubseteq> stpi_upper (stamp_expr x)\<close> \<open>stpi_lower (stamp_expr y) \<sqsubseteq> sint yyval\<close> word_sless_alt by fastforce
    then have "(intval_less_than xval yval) = IntVal32 1"
      by (simp add: x32 y32)
  }
  note case32 = this
  { assume c: "is_IntVal64 xval"
    obtain xxval where x64: "xval = IntVal64 xxval"
      using c is_IntVal64_def by blast
    obtain yyval where y64: "yval = IntVal64 yyval"
      using \<open>is_IntVal64 xval = is_IntVal64 yval\<close> c is_IntVal64_def by auto
    have xs: "\<exists> lo hi. stamp_expr x = IntegerStamp 64 lo hi"
      by (simp add: \<open>is_IntVal64 xval \<Longrightarrow> (\<exists>lo hi. stamp_expr x = IntegerStamp 64 lo hi) \<and> (\<exists>lo hi. stamp_expr y = IntegerStamp 64 lo hi)\<close> c)
    have ys: "\<exists> lo hi. stamp_expr y = IntegerStamp 64 lo hi"
      using \<open>is_IntVal64 xval \<Longrightarrow> (\<exists>lo hi. stamp_expr x = IntegerStamp 64 lo hi) \<and> (\<exists>lo hi. stamp_expr y = IntegerStamp 64 lo hi)\<close> c by blast
    have "sint xxval \<le> stpi_upper (stamp_expr x)"
      using upper_bound_64 x64 xs xvalid by presburger
    have "stpi_lower (stamp_expr y) \<le> sint yyval"
      using lower_bound_64 y64 ys yvalid by presburger
    have "stpi_upper (stamp_expr x) < stpi_lower (stamp_expr y)"
      using assms(1) unfolding stamp_under.simps
      by auto
    then have "xxval <s yyval"
      using assms(1) unfolding stamp_under.simps
      using \<open>sint xxval \<sqsubseteq> stpi_upper (stamp_expr x)\<close> \<open>stpi_lower (stamp_expr y) \<sqsubseteq> sint yyval\<close> word_sless_alt by fastforce
    then have "(intval_less_than xval yval) = IntVal32 1"
      by (simp add: x64 y64)
  }
  note case64 = this
  have "(intval_less_than xval yval) = IntVal32 1"
    using \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> case32 case64 by fastforce
  then show ?thesis
    by (metis EvalTreeE(5) assms(2) bin_eval.simps(12) evalDet val_to_bool.simps(1) xval_def yval_def zero_neq_one)
qed

lemma stamp_under_semantics_inversed:
  assumes "stamp_under (stamp_expr y) (stamp_expr x)"
  assumes "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan x y) \<mapsto> v"
  assumes xvalid: "(\<forall>m p v. ([m, p] \<turnstile> x \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr x))"
  assumes yvalid: "(\<forall>m p v. ([m, p] \<turnstile> y \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr y))"
  shows "\<not>(val_to_bool v)"
proof -
  obtain xval where xval_def: "[m, p] \<turnstile> x \<mapsto> xval"
    using assms(2) by blast
  obtain yval where yval_def: "[m, p] \<turnstile> y \<mapsto> yval"
    using assms(2) by blast
  have "is_IntVal32 xval \<or> is_IntVal64 xval"
    by (metis BinaryExprE Value.discI(1) Value.discI(2) assms(2) bin_eval.simps(12) binary_obj 
       constantAsStamp.elims evalDet evaltree_not_undef intval_less_than.simps(9) xval_def)
  have "is_IntVal32 yval \<or> is_IntVal64 yval"
    by (metis BinaryExprE Value.discI(1) Value.discI(2) assms(2) bin_eval.simps(12) binary_obj 
        constantAsStamp.elims evalDet evaltree_not_undef intval_less_than.simps(16) yval_def)
  have "is_IntVal32 xval = is_IntVal32 yval"
    by (metis BinaryExprE Value.collapse(2) \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> assms(2) bin_eval.simps(12) evalDet intval_less_than.simps(12) intval_less_than.simps(5) is_IntVal32_def xval_def yval_def)
  have "is_IntVal64 xval = is_IntVal64 yval"
    using \<open>is_IntVal32 xval = is_IntVal32 yval\<close> \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> by blast
  have "(intval_less_than xval yval) \<noteq> UndefVal"
    using assms(2)
    by (metis BinaryExprE bin_eval.simps(12) evalDet xval_def yval_def)
  have "is_IntVal32 xval \<Longrightarrow> ((\<exists> lo hi. stamp_expr x = IntegerStamp 32 lo hi) \<and> (\<exists> lo hi. stamp_expr y = IntegerStamp 32 lo hi))"
    (* by (smt (verit) BinaryExprE Value.discI(2) Value.distinct_disc(9) assms(2) binary_eval_bits_equal xvalid yvalid valid_value.elims(2) xval_def)
    *)
    sorry
  have "is_IntVal64 xval \<Longrightarrow> ((\<exists> lo hi. stamp_expr x = IntegerStamp 64 lo hi) \<and> (\<exists> lo hi. stamp_expr y = IntegerStamp 64 lo hi))"
    (* by (smt (verit, best) BinaryExprE \<open>intval_less_than xval yval \<noteq> UndefVal\<close> assms(2) binary_eval_bits_equal intval_less_than.simps(5) is_IntVal64_def xvalid yvalid valid_value.elims(2) yval_def)
    *)
    sorry
  have xvalid: "valid_value xval (stamp_expr x)"
    using xvalid xval_def by auto
  have yvalid: "valid_value yval (stamp_expr y)"
    using yvalid yval_def by auto
  { assume c: "is_IntVal32 xval"
    obtain xxval where x32: "xval = IntVal32 xxval"
      using c is_IntVal32_def by blast
    obtain yyval where y32: "yval = IntVal32 yyval"
      using \<open>is_IntVal32 xval = is_IntVal32 yval\<close> c is_IntVal32_def by auto
    have xs: "\<exists> lo hi. stamp_expr x = IntegerStamp 32 lo hi"
      by (simp add: \<open>is_IntVal32 xval \<Longrightarrow> (\<exists>lo hi. stamp_expr x = IntegerStamp 32 lo hi) \<and> (\<exists>lo hi. stamp_expr y = IntegerStamp 32 lo hi)\<close> c)
    have ys: "\<exists> lo hi. stamp_expr y = IntegerStamp 32 lo hi"
      using \<open>is_IntVal32 xval \<Longrightarrow> (\<exists>lo hi. stamp_expr x = IntegerStamp 32 lo hi) \<and> (\<exists>lo hi. stamp_expr y = IntegerStamp 32 lo hi)\<close> c by blast
    have "sint yyval \<le> stpi_upper (stamp_expr y)"
      using y32 ys yvalid by force
    have "stpi_lower (stamp_expr x) \<le> sint xxval"
      using x32 xs xvalid by force
    have "stpi_upper (stamp_expr y) < stpi_lower (stamp_expr x)"
      using assms(1) unfolding stamp_under.simps
      by auto
    then have "yyval <s xxval"
      using assms(1) unfolding stamp_under.simps
      using \<open>sint yyval \<sqsubseteq> stpi_upper (stamp_expr y)\<close> \<open>stpi_lower (stamp_expr x) \<sqsubseteq> sint xxval\<close> word_sless_alt by fastforce
    then have "(intval_less_than xval yval) = IntVal32 0"
      using signed.less_not_sym x32 y32 by fastforce
  }
  note case32 = this
  { assume c: "is_IntVal64 xval"
    obtain xxval where x64: "xval = IntVal64 xxval"
      using c is_IntVal64_def by blast
    obtain yyval where y64: "yval = IntVal64 yyval"
      using \<open>is_IntVal64 xval = is_IntVal64 yval\<close> c is_IntVal64_def by auto
    have xs: "\<exists> lo hi. stamp_expr x = IntegerStamp 64 lo hi"
      by (simp add: \<open>is_IntVal64 xval \<Longrightarrow> (\<exists>lo hi. stamp_expr x = IntegerStamp 64 lo hi) \<and> (\<exists>lo hi. stamp_expr y = IntegerStamp 64 lo hi)\<close> c)
    have ys: "\<exists> lo hi. stamp_expr y = IntegerStamp 64 lo hi"
      using \<open>is_IntVal64 xval \<Longrightarrow> (\<exists>lo hi. stamp_expr x = IntegerStamp 64 lo hi) \<and> (\<exists>lo hi. stamp_expr y = IntegerStamp 64 lo hi)\<close> c by blast
    have "sint yyval \<le> stpi_upper (stamp_expr y)"
      using y64 ys yvalid by force
    have "stpi_lower (stamp_expr x) \<le> sint xxval"
      using x64 xs xvalid by force
    have "stpi_upper (stamp_expr y) < stpi_lower (stamp_expr x)"
      using assms(1) unfolding stamp_under.simps
      by auto
    then have "yyval <s xxval"
      using assms(1) unfolding stamp_under.simps
      using \<open>sint yyval \<sqsubseteq> stpi_upper (stamp_expr y)\<close> \<open>stpi_lower (stamp_expr x) \<sqsubseteq> sint xxval\<close> word_sless_alt by fastforce
    then have "(intval_less_than xval yval) = IntVal32 0"
      using signed.less_imp_triv x64 y64 by fastforce
  }
  note case64 = this
  have "(intval_less_than xval yval) = IntVal32 0"
    using \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> case32 case64 by fastforce
  then show ?thesis
    by (metis BinaryExprE assms(2) bin_eval.simps(12) evalDet val_to_bool.simps(1) xval_def yval_def)
qed

end