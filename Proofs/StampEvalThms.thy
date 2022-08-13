subsection \<open>Evaluation Stamp Theorems\<close>

theory StampEvalThms
  imports ValueThms
          Semantics.IRTreeEvalThms
begin

(* TODO: these will need constraints on v to make sure it fits into 32/64 bits
lemma unrestricted_32bit_always_valid [simp]:
  "valid_value (new_int 32 v) (unrestricted_stamp (IntegerStamp 32 lo hi))"
  apply auto
  using valid_value.simps(1) bit_bounds_min32 bit_bounds_max32 new_int.simps
  using unrestricted_stamp.simps(2) 
*)

(* TODO:
lemma unrestricted_64bit_always_valid [simp]:
  "valid_value (IntVal 64 v) (unrestricted_stamp (IntegerStamp 64 lo hi))"
  using valid_value.simps(2) bit_bounds_min64 bit_bounds_max64
  using unrestricted_stamp.simps(2) by presburger
*)

lemma unary_undef: "val = UndefVal \<Longrightarrow> unary_eval op val = UndefVal"
  by (cases op; auto)

lemma unary_obj: "val = ObjRef x \<Longrightarrow> unary_eval op val = UndefVal"
  by (cases op; auto)


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

text \<open>A valid int must have the expected number of bits.\<close>
lemma valid_int_same_bits:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "b = bits"
  by (meson assms valid_value.simps(1))

text \<open>A valid int means a valid non-empty stamp.\<close>
lemma valid_int_not_empty:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "lo \<le> hi"
  by (metis assms order.trans valid_value.simps(1))

text \<open>A valid int fits into the given number of bits (and other bits are zero).\<close>
lemma valid_int_fits:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "take_bit bits val = val"
  by (metis assms valid_value.simps(1))

lemma valid_int_is_zero_masked:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "and val (not (mask bits)) = 0"
  by (metis (no_types, lifting) assms bit.conj_cancel_right take_bit_eq_mask valid_int_fits 
             word_bw_assocs(1) word_log_esimps(1))

text \<open>Unsigned ints have bounds $0$ up to $2^bits$.\<close>
lemma valid_int_unsigned_bounds:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  (* Not actually needed: assumes "0 \<le> lo" *)
  shows "uint val < 2 ^ bits"
  by (metis assms(1) mask_eq_iff take_bit_eq_mask valid_value.simps(1))

text \<open>Signed ints have the usual two-complement bounds.\<close>
lemma valid_int_signed_upper_bound:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "int_signed_value bits val < 2 ^ (bits - 1)"
  by (metis (mono_tags, opaque_lifting) diff_le_mono int_signed_value.simps less_imp_diff_less 
       linorder_not_le one_le_numeral order_less_le_trans power_increasing signed_take_bit_int_less_exp_word sint_lt)

lemma valid_int_signed_lower_bound:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "-(2 ^ (bits - 1)) \<le> int_signed_value bits val"
  by (smt (verit) diff_le_self int_signed_value.simps linorder_not_less power_increasing_iff signed_take_bit_int_greater_eq_minus_exp_word sint_greater_eq)

text \<open>and $bit\_bounds$ versions of the above bounds.\<close>
lemma valid_int_signed_upper_bit_bound:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "int_signed_value bits val \<le> snd (bit_bounds bits)"
proof - 
  have "b = bits" using assms valid_int_same_bits by blast 
  then show ?thesis 
    using assms by force 
qed

lemma valid_int_signed_lower_bit_bound:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows " fst (bit_bounds bits) \<le> int_signed_value bits val"
proof - 
  have "b = bits" using assms valid_int_same_bits by blast 
  then show ?thesis
    using assms by force 
qed


text \<open>Valid values satisfy their stamp bounds.\<close>

lemma valid_int_signed_range:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "lo \<le> int_signed_value bits val \<and> int_signed_value bits val \<le> hi"
  by (metis assms valid_value.simps(1))



subsubsection \<open>Validity of UnaryAbs\<close>

text \<open>A set of lemmas for each evaltree step.
   Questions: 
   1. is this top-down approach (assume the result node evaluation) best?
      Maybe.  It seems to be the shortest/simplest trigger?
\<close>

lemma unary_abs_result:
  assumes "[m,p] \<turnstile> (UnaryExpr UnaryAbs e) \<mapsto> IntVal b v"
  obtains ve where "([m, p] \<turnstile> e \<mapsto> ve) \<and>
           IntVal b v = intval_abs ve"
  using assms by force

lemma unary_abs_implies_valid_value:
  assumes 1:"[m,p] \<turnstile> e1 \<mapsto> r1"
  assumes 2:"result = unary_eval UnaryAbs r1"
  assumes 3:"result \<noteq> UndefVal"
  assumes 4:"valid_value r1 (stamp_expr e1)"
  shows "valid_value result (stamp_expr (UnaryExpr UnaryAbs e1))"
proof -
  have "[m,p] \<turnstile> (UnaryExpr UnaryAbs e1) \<mapsto> result"
    using assms by blast
  then obtain b1 v1 where r1: "IntVal b1 v1 = r1"
    using assms by (metis intval_abs.elims unary_eval.simps(1))
  then obtain lo1 hi1 where s1: "stamp_expr e1 = IntegerStamp b1 lo1 hi1"
    by (smt (z3) "2" "3" "4" intval_bits.simps unary_obj valid_value.elims(2))
  then obtain v2 where r2: "result = IntVal b1 v2"
    using assms by (metis intval_abs.simps(1) new_int.simps r1 unary_eval.simps(1)) 
  then have "(stamp_expr (UnaryExpr UnaryAbs e1)) = unrestricted_stamp (IntegerStamp b1 lo1 hi1)"
    by (simp add: s1)
  then obtain sb lo2 hi2 where s2: "(stamp_expr (UnaryExpr UnaryAbs e1)) = IntegerStamp sb lo2 hi2"
    by (metis unrestricted_stamp.simps(2))
  then have b2: "sb = b1"
    by (metis Stamp.inject(1) insert_iff s1 stamp_expr.simps(1) stamp_unary.simps(1) unrestricted_stamp.simps(2))
  then show ?thesis
    unfolding r2 s2 valid_value.simps b2
    using 4 r1 s1
    sorry
qed

(* TODO: intval_abs needs to expand up to 32 bits too? 
   Or stamp could leave size unchanged? 
*)


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