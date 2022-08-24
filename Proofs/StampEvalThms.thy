subsection \<open>Evaluation Stamp Theorems\<close>

theory StampEvalThms
  imports Graph.ValueThms
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


lemma unrestricted_stamp_valid:
  assumes "s = unrestricted_stamp (IntegerStamp b lo hi)"
  assumes "0 < b \<and> b \<le> 64"
  shows "valid_stamp s"
  using assms
  by (smt (z3) Stamp.inject(1) bit_bounds.simps not_exp_less_eq_0_int prod.sel(1) prod.sel(2) unrestricted_stamp.simps(2) upper_bounds_equiv valid_stamp.elims(1)) 

lemma unrestricted_stamp_valid_value [simp]:
  assumes 1: "result = IntVal b ival"
  assumes "take_bit b ival = ival"
  assumes "0 < b \<and> b \<le> 64"
  shows "valid_value result (unrestricted_stamp (IntegerStamp b lo hi))"
proof -
  have "valid_stamp (unrestricted_stamp (IntegerStamp b lo hi))"
    using assms unrestricted_stamp_valid by blast 
  then show ?thesis
    unfolding 1 unrestricted_stamp.simps valid_value.simps
    using assms int_signed_value_bounds by presburger
qed


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

text \<open>Valid int implies some useful facts.\<close>
lemma valid_int_gives:
  assumes "valid_value (IntVal b val) stamp"
  obtains lo hi where "stamp = IntegerStamp b lo hi \<and>
       valid_stamp (IntegerStamp b lo hi) \<and>
       take_bit b val = val \<and>
       lo \<le> int_signed_value b val \<and> int_signed_value b val \<le> hi"
  using assms
  by (smt (z3) Value.distinct(7) Value.inject(1) valid_value.elims(1))

text \<open>And the corresponding lemma where we know the stamp rather than the value.\<close>
lemma valid_int_stamp_gives:
  assumes "valid_value val (IntegerStamp b lo hi)"
  obtains ival where "val = IntVal b ival \<and>
       valid_stamp (IntegerStamp b lo hi) \<and>
       take_bit b ival = ival \<and>
       lo \<le> int_signed_value b ival \<and> int_signed_value b ival \<le> hi"
  by (metis assms valid_int valid_value.simps(1))


text \<open>A valid int must have the expected number of bits.\<close>
lemma valid_int_same_bits:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "b = bits"
  by (meson assms valid_value.simps(1))

text \<open>A valid value means a valid stamp.\<close>
lemma valid_int_valid_stamp:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "valid_stamp (IntegerStamp bits lo hi)"
  by (metis assms valid_value.simps(1))

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
    by (metis "4" valid_int_gives)
  then obtain v2 where r2: "result = IntVal b1 v2"
    using assms by (metis intval_abs.simps(1) new_int.simps r1 unary_eval.simps(1))
  then have r: "result = intval_abs (IntVal b1 v1)"
    using "2" r1 unary_eval.simps(1) by presburger
  then have b1: "0 < b1 \<and> b1 \<le> 64"
    by (metis "4" r1 s1 valid_stamp.simps(1) valid_value.simps(1))
  then have bnds1: "fst (bit_bounds b1) \<le> int_signed_value b1 v2 \<and> int_signed_value b1 v2 \<le> snd (bit_bounds b1)"
    using int_signed_value_bounds by blast 
  then have s: "(stamp_expr (UnaryExpr UnaryAbs e1)) = unrestricted_stamp (IntegerStamp b1 lo1 hi1)"
    by (simp add: s1)
  then show ?thesis
    unfolding s unrestricted_stamp.simps r2 valid_value.simps
    using "4" bnds1 r r1 r2 s1 by auto
qed



subsubsection \<open>Validity of all Unary Operators\<close>

lemma eval_normal_unary_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes op: "op \<in> normal_unary"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
proof -
  obtain b1 v1 where v1: "val = IntVal b1 v1"
    by (metis Value.exhaust assms(1) assms(2) assms(4) assms(5) evaltree_not_undef unary_obj valid_value.simps(11))
  then obtain b2 v2 where v2: "result = IntVal b2 v2"
    using assms(2) assms(4) is_IntVal_def unary_eval_int by presburger
  then have "result = unary_eval op (IntVal b1 v1)"
    using assms(2) v1 by blast
  then obtain vtmp where vtmp: "result = new_int b2 vtmp"
    using assms(3) v2 by auto
  obtain b' lo' hi' where "stamp_expr expr = IntegerStamp b' lo' hi'"
    by (metis assms(5) v1 valid_int_gives)
  then have "stamp_unary op (stamp_expr expr) =
    unrestricted_stamp
     (IntegerStamp (if op \<in> normal_unary then b' else ir_resultBits op) lo' hi')"
    using stamp_unary.simps(1) by presburger
  then obtain lo2 hi2 where s: "(stamp_expr (UnaryExpr op expr)) = unrestricted_stamp (IntegerStamp b2 lo2 hi2)"
    unfolding stamp_expr.simps 
    using vtmp op
    by (smt (verit, best) Value.inject(1) \<open>(result::Value) = unary_eval (op::IRUnaryOp) (IntVal (b1::nat) (v1::64 word))\<close> \<open>stamp_expr (expr::IRExpr) = IntegerStamp (b'::nat) (lo'::int) (hi'::int)\<close> assms(5) insertE intval_abs.simps(1) intval_logic_negation.simps(1) intval_negate.simps(1) intval_not.simps(1) new_int.elims singleton_iff unary_eval.simps(1) unary_eval.simps(2) unary_eval.simps(3) unary_eval.simps(4) v1 valid_int_same_bits)
  then have "0 < b1 \<and> b1 \<le> 64"
    using valid_int_gives
    by (metis assms(5) v1 valid_stamp.simps(1)) 
  then have "fst (bit_bounds b2) \<le> int_signed_value b2 v2 \<and>
             int_signed_value b2 v2 \<le> snd (bit_bounds b2)"
    by (smt (verit, del_insts) Stamp.inject(1) assms(3) assms(5) int_signed_value_bounds s stamp_expr.simps(1) stamp_unary.simps(1) unrestricted_stamp.simps(2) v1 valid_int_gives)
  then show ?thesis
    unfolding s v2 unrestricted_stamp.simps valid_value.simps
    by (smt (z3) assms(3) assms(5) is_stamp_empty.simps(1) new_int_take_bits s stamp_expr.simps(1) stamp_unary.simps(1) unrestricted_stamp.simps(2) v1 v2 valid_int_gives valid_stamp.simps(1) vtmp)
qed

lemma narrow_widen_output_bits:
  assumes "unary_eval op val \<noteq> UndefVal"
  assumes "op \<notin> normal_unary"
  shows "0 < (ir_resultBits op) \<and> (ir_resultBits op) \<le> 64"
proof -
  consider ib ob where "op = UnaryNarrow ib ob"
         | ib ob where "op = UnarySignExtend ib ob"
         | ib ob where "op = UnaryZeroExtend ib ob"
    using IRUnaryOp.exhaust_sel assms(2) by blast
  then show ?thesis
  proof (cases)
    case 1
    then show ?thesis using assms intval_narrow_ok by force
  next
    case 2
    then show ?thesis using assms intval_sign_extend_ok by force
  next
    case 3
    then show ?thesis using assms intval_zero_extend_ok by force
  qed
qed


lemma eval_widen_narrow_unary_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes op: "op \<notin> normal_unary"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
proof -
  obtain b1 v1 where v1: "val = IntVal b1 v1"
    by (metis Value.exhaust assms(1) assms(2) assms(4) assms(5) evaltree_not_undef unary_obj valid_value.simps(11))
  then have "result = unary_eval op (IntVal b1 v1)"
    using assms(2) v1 by blast
  then obtain v2 where v2: "result = new_int (ir_resultBits op) v2"
    using assms by (cases op; simp; (meson new_int.simps)+)
  then obtain v3 where v3: "result = IntVal (ir_resultBits op) v3"
    using assms by (cases op; simp; (meson new_int.simps)+)
  then obtain lo2 hi2 where s: "(stamp_expr (UnaryExpr op expr)) = unrestricted_stamp (IntegerStamp (ir_resultBits op) lo2 hi2)"
    unfolding stamp_expr.simps stamp_unary.simps
    using assms(3) assms(5) v1 valid_int_gives by fastforce 
  then have outBits: "0 < (ir_resultBits op) \<and> (ir_resultBits op) \<le> 64"
    using assms narrow_widen_output_bits
    by blast 
  then have "fst (bit_bounds (ir_resultBits op)) \<le> int_signed_value (ir_resultBits op) v3 \<and>
             int_signed_value (ir_resultBits op) v3 \<le> snd (bit_bounds (ir_resultBits op))"
    using int_signed_value_bounds 
    by (smt (verit, del_insts) Stamp.inject(1) assms(3) assms(5) int_signed_value_bounds s stamp_expr.simps(1) stamp_unary.simps(1) unrestricted_stamp.simps(2) v1 valid_int_gives)
  then show ?thesis
    unfolding s v3 unrestricted_stamp.simps valid_value.simps
    using outBits v2 v3 by auto
qed

lemma eval_unary_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
  proof (cases "op \<in> normal_unary")
    case True
    then show ?thesis by (metis assms eval_normal_unary_implies_valid_value)
  next
    case False
    then show ?thesis by (metis assms eval_widen_narrow_unary_implies_valid_value)
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
  sorry


subsubsection \<open>Validity of Stamp Meet and Join Operators\<close>

lemma stamp_meet_integer_is_valid_stamp:
  assumes "valid_stamp stamp1"
  assumes "valid_stamp stamp2"
  assumes "is_IntegerStamp stamp1"
  assumes "is_IntegerStamp stamp2"
  shows "valid_stamp (meet stamp1 stamp2)"
  using assms unfolding is_IntegerStamp_def valid_stamp.simps meet.simps
  by (smt (verit, del_insts) meet.simps(2) valid_stamp.simps(1) valid_stamp.simps(8))

lemma stamp_meet_is_valid_stamp:
  assumes 1: "valid_stamp stamp1"
  assumes 2: "valid_stamp stamp2"
  shows "valid_stamp (meet stamp1 stamp2)"
  by (cases stamp1; cases stamp2; insert stamp_meet_integer_is_valid_stamp[OF 1 2]; auto)


lemma stamp_meet_commutes: "meet stamp1 stamp2 = meet stamp2 stamp1"
  by (cases stamp1; cases stamp2; auto)

lemma stamp_meet_is_valid_value1:
  assumes "valid_value val stamp1"  (*  \<or> valid_value val stamp2" *)
  assumes "valid_stamp stamp2"
  assumes "stamp1 = IntegerStamp b1 lo1 hi1"
  assumes "stamp2 = IntegerStamp b2 lo2 hi2"
  assumes "meet stamp1 stamp2 \<noteq> IllegalStamp"
  shows "valid_value val (meet stamp1 stamp2)"
proof -
  have m: "meet stamp1 stamp2 = IntegerStamp b1 (min lo1 lo2) (max hi1 hi2)"
    using assms by (metis meet.simps(2)) 
  obtain ival where val: "val = IntVal b1 ival"
    using assms valid_int by blast 
  then have v: "valid_stamp (IntegerStamp b1 lo1 hi1) \<and>
       take_bit b1 ival = ival \<and>
       lo1 \<le> int_signed_value b1 ival \<and> int_signed_value b1 ival \<le> hi1"
    using assms by (metis valid_value.simps(1)) 
  then have mm: "min lo1 lo2 \<le> int_signed_value b1 ival \<and> int_signed_value b1 ival \<le> max hi1 hi2"
    by linarith
  then have "valid_stamp (IntegerStamp b1 (min lo1 lo2) (max hi1 hi2))"
    using assms v stamp_meet_is_valid_stamp
    by (metis meet.simps(2)) 
  then show ?thesis 
    unfolding m val valid_value.simps
    using mm v by presburger 
qed

text \<open>and the symmetric lemma follows by the commutativity of meet.\<close>

lemma stamp_meet_is_valid_value:
  assumes "valid_value val stamp2"
  assumes "valid_stamp stamp1"
  assumes "stamp1 = IntegerStamp b1 lo1 hi1"
  assumes "stamp2 = IntegerStamp b2 lo2 hi2"
  assumes "meet stamp1 stamp2 \<noteq> IllegalStamp"
  shows "valid_value val (meet stamp1 stamp2)"
  using assms stamp_meet_commutes stamp_meet_is_valid_value1
  by metis 



subsubsection \<open>Validity of conditional expressions\<close>

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
  have def: "meet (stamp_expr expr1) (stamp_expr expr2) \<noteq> IllegalStamp"
    using assms
    by (metis Stamp.distinct(13) Stamp.distinct(25) compatible.elims(2) meet.simps(1) meet.simps(2))
  then have "valid_stamp (meet (stamp_expr expr1) (stamp_expr expr2))"
    using assms
    by (smt (verit, best) compatible.elims(2) stamp_meet_is_valid_stamp valid_stamp.simps(2)) 
  then show ?thesis using stamp_meet_is_valid_value 
    using assms def
    by (smt (verit, best) compatible.elims(2) never_void stamp_expr.simps(6) stamp_meet_commutes) 
qed



subsubsection \<open>Validity of Whole Expression Tree Evaluation\<close>

text \<open> TODO: find a way to encode that conditional expressions must have
  compatible (and valid) stamps?  One approach would be for all the 
  stamp\_expr operators to require that all input stamps are valid.\<close>

experiment begin
lemma stamp_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  shows "valid_value val (stamp_expr expr)"
  using assms proof (induction expr val)
  case (UnaryExpr expr val result op)
  then show ?case using eval_unary_implies_valid_value by simp
  next
    case (BinaryExpr expr1 val1 expr2 val2 result op)
    then show ?case using binary_eval_implies_valid_value by simp
  next
    case (ConditionalExpr cond condv expr expr1 expr2 val)
    have "compatible (stamp_expr expr1) (stamp_expr expr2)"
      using assms sorry
    then show ?case 
      using assms conditional_eval_implies_valid_value
      using ConditionalExpr.IH(1) ConditionalExpr.IH(2) ConditionalExpr.hyps(1) ConditionalExpr.hyps(2) ConditionalExpr.hyps(3) ConditionalExpr.hyps(4) by blast
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