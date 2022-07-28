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

(* TODO: these will need constraints on v to make sure it fits into 32/64 bits
lemma unrestricted_32bit_always_valid [simp]:
  "valid_value (IntVal 32 v) (unrestricted_stamp (IntegerStamp 32 lo hi))"
  using valid_value.simps(1) bit_bounds_min32 bit_bounds_max32
  using unrestricted_stamp.simps(2) by presburger

lemma unrestricted_64bit_always_valid [simp]:
  "valid_value (IntVal64 v) (unrestricted_stamp (IntegerStamp 64 lo hi))"
  using valid_value.simps(2) bit_bounds_min64 bit_bounds_max64
  using unrestricted_stamp.simps(2) by presburger
*)

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

(* TODO: delete these now sign_extend_helper is gone?
lemma sign_extend_helper_output_range64:
  assumes "result = sign_extend_helper inBits outBits val"
  assumes "result = IntVal64 ival"
  shows "outBits = 64 \<and> -(2 ^ (inBits - 1)) \<le> sint ival \<and> sint ival \<le> 2 ^ (inBits - 1)"
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
*)



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


(* TODO: delete now zero_extend_helper is gone?
lemma zero_extend_helper_output_range32:
  assumes "result = zero_extend_helper inBits outBits val"
  assumes "result = IntVal32 ival"
  shows "outBits \<le> 32 \<and> -(2 ^ (inBits - 1)) \<le> sint ival \<and> sint ival \<le> 2 ^ (inBits - 1)"
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
*)

subsubsection \<open>Support Lemmas for integer input/output size of unary and binary operators\<close>

text \<open>These help us to deduce integer sizes through expressions.  Not used yet.\<close>

(*
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
*)


subsubsection \<open>Validity of UnaryAbs\<close>


text \<open>A set of lemmas for each evaltree step.
   Questions: 
   1. do we need separate 32/64 lemmas?  
      Yes, I think so, because almost every operator behaves differently on each width.
      And it makes the matching more direct, does not need is\_IntVal\_def etc.
   2. is this top-down approach (assume the result node evaluation) best?
      Maybe.  It seems to be the shortest/simplest trigger?
\<close>

lemma unary_abs_result:
  assumes "[m,p] \<turnstile> (UnaryExpr UnaryAbs e) \<mapsto> IntVal b v"
  obtains ve where "([m, p] \<turnstile> e \<mapsto> IntVal b ve) \<and>
           v = (if ve <s 0 then -ve else ve)"
  sorry


lemma unary_abs_implies_valid_value:
  assumes 1:"[m,p] \<turnstile> expr \<mapsto> val"
  assumes 2:"result = unary_eval UnaryAbs val"
  assumes 3:"result \<noteq> UndefVal"
  assumes 4:"valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr UnaryAbs expr))"
  sorry


subsubsection \<open>Validity of UnaryNeg\<close>



subsubsection \<open>Validity of all Unary Operators\<close>

lemma unary_eval_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
  sorry



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
  sorry


subsubsection \<open>Validity of Stamp Meet and Join Operators\<close>

lemma stamp_meet_is_valid:
  assumes "valid_value val stamp1 \<or> valid_value val stamp2"
  assumes "meet stamp1 stamp2 \<noteq> IllegalStamp"
  shows "valid_value val (meet stamp1 stamp2)"
  using assms 
  sorry

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

(* these two proofs should really not be so tricky *)
lemma stamp_under_semantics:
  assumes "stamp_under (stamp_expr x) (stamp_expr y)"
  assumes "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan x y) \<mapsto> v"
  assumes xvalid: "(\<forall>m p v. ([m, p] \<turnstile> x \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr x))"
  assumes yvalid: "(\<forall>m p v. ([m, p] \<turnstile> y \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr y))"
  shows "val_to_bool v"
  sorry

lemma stamp_under_semantics_inversed:
  assumes "stamp_under (stamp_expr y) (stamp_expr x)"
  assumes "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan x y) \<mapsto> v"
  assumes xvalid: "(\<forall>m p v. ([m, p] \<turnstile> x \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr x))"
  assumes yvalid: "(\<forall>m p v. ([m, p] \<turnstile> y \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr y))"
  shows "\<not>(val_to_bool v)"
  sorry

end