subsection \<open>Evaluation Stamp Theorems\<close>

theory StampEvalThms
  imports Semantics.IRTreeEvalThms
begin

subsubsection \<open>Evaluated Value Satisfies Stamps\<close>

(* these two were weirdly hard to prove given it should be by definition *)
lemma size32: "size v = 32" for v :: "32 word"
  using size_word.rep_eq
  using One_nat_def add.right_neutral add_Suc_right len_of_numeral_defs(2) len_of_numeral_defs(3) mult.right_neutral mult_Suc_right numeral_2_eq_2 numeral_Bit0
  by (smt (verit, del_insts) mult.commute)

lemma size64: "size v = 64" for v :: "64 word"
  using size_word.rep_eq
  using One_nat_def add.right_neutral add_Suc_right len_of_numeral_defs(2) len_of_numeral_defs(3) mult.right_neutral mult_Suc_right numeral_2_eq_2 numeral_Bit0
  by (smt (verit, del_insts) mult.commute)

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

lemma unrestricted_32bit_always_valid:
  "valid_value (IntVal32 v) (unrestricted_stamp (IntegerStamp 32 lo hi))"
  using valid_value.simps(1) bit_bounds_min32 bit_bounds_max32
  using unrestricted_stamp.simps(2) by presburger

lemma unrestricted_64bit_always_valid:
  "valid_value (IntVal64 v) (unrestricted_stamp (IntegerStamp 64 lo hi))"
  using valid_value.simps(2) bit_bounds_min64 bit_bounds_max64
  using unrestricted_stamp.simps(2) by presburger

lemma unary_undef: "val = UndefVal \<Longrightarrow> unary_eval op val = UndefVal"
  by (cases op; auto)

lemma unary_obj: "val = ObjRef x \<Longrightarrow> unary_eval op val = UndefVal"
  by (cases op; auto)


text \<open>A set of lemmas for each evaltree step.
   Questions: 
   1. do we need separate 32/64 lemmas?  
      Yes, I think so, because almost every operator behaves differently on each width.
      And it makes the matching more direct, does not need is_IntVal_def etc.
   2. is this top-down approach (assume the result node evaluation) best?
      Maybe.  It seems to be the shortest/simplest trigger?
\<close>
lemma unary_abs_result64:
  assumes 1:"[m,p] \<turnstile> (UnaryExpr UnaryAbs e) \<mapsto> IntVal64 v"
  shows "\<exists> ve. ([m, p] \<turnstile> e \<mapsto> IntVal64 ve) \<and>
           v = (if ve <s 0 then -ve else ve)"
proof -
  obtain ve where "[m,p] \<turnstile> e \<mapsto> IntVal64 ve"
    by (smt (verit, best) 1 UnaryExprE Value.distinct evalDet intval_abs.elims unary_eval.simps(1))
  then show ?thesis
    by (metis 1 UnaryExprE Value.inject(2) evalDet intval_abs.simps(2) unary_eval.simps(1))
qed
(* or backwards proof:
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
    by (metis "2" "3" Value.collapse(1) Value.collapse(2) is_IntVal_def unary_eval_int)
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
    then have "((b=32 \<or> b=16 \<or> b=8) \<and> (sint ve \<ge> lo) \<and> (sint ve \<le> hi))"
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
    then have range64: "b=64 \<and> (sint ve \<ge> lo) \<and> (sint ve \<le> hi)"
      using 4 64 se by simp
    then have "stamp_expr (UnaryExpr UnaryAbs expr) = unrestricted_stamp (IntegerStamp b lo hi)"
      using se by simp
    then show ?thesis
      by (metis "2" range64 unrestricted_64bit_always_valid)
  qed
qed


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


text \<open>Possibly helpful lemmas about signed_take_bit, to help with UnaryNarrow.
  Note: we could use signed to convert between bit-widths, instead of 
  signed_take_bit.  But this has to be done separately for each bit-width type.\<close>

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


lemma unary_narrow_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval (UnaryNarrow inBits outBits) val"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr (UnaryNarrow inBits outBits) expr))"
proof -
  have i: "is_IntegerStamp (stamp_expr expr)"
    using assms valid_value.elims(2) by fastforce 
  have "result = intval_narrow inBits outBits val"
    by (simp add: assms(2)) 
  then consider i32 where "val = IntVal32 i32" | i64 where "val = IntVal64 i64"
    using assms by (metis intval_narrow.elims)
  then show ?thesis
  proof cases
    case 1
    then have r1: "result = narrow_helper inBits outBits i32"
      using assms by simp
    then have r2: "result =  (IntVal32 (signed_take_bit (outBits - 1) i32))"
      using assms by (metis narrow_helper.simps)
    then obtain r32 where 
      r32: "result = IntVal32 r32 \<and> r32 = signed_take_bit (outBits - 1) i32"
      by simp
    obtain b lo hi where "stamp_expr expr = IntegerStamp b lo hi"
      using assms 1 valid_value.elims(2) by blast
    (* now make stamp deductions *)
    then have u: "stamp_expr (UnaryExpr (UnaryNarrow inBits outBits) expr) 
             = unrestricted_stamp (IntegerStamp outBits lo hi)"
      using i by simp
    then consider "outBits=32" | "outBits=16" | "outBits=8"
      by (metis r1 assms(3) insertE narrow_helper.elims singletonD) 
    then show ?thesis
    proof (cases)
      case 1  (* narrow to 32 bits *)
      then show ?thesis 
        using r2 u unrestricted_32bit_always_valid by presburger 
    next
      (* TODO: these next two cases have same proof - can we combine them? *)
      case 2  (* narrow to 16 bits *)
      then show ?thesis
      proof -
        have hi: "sint r32 < 2^(outBits-1)"
          using r32 signed_take_bit_int_less_exp_word
          by (metis diff_le_mono less_imp_diff_less linorder_not_le one_le_numeral 
                power_increasing sint_above_size word_size)
        then have lo: "- (2^(outBits-1)) \<le> sint r32"
          using r32 signed_take_bit_int_greater_eq_minus_exp_word
          by (metis 2 add_diff_cancel_left' diff_less less_imp_diff_less numeral_Bit0 
             size32 wsst_TYs(3) zero_less_numeral)
        then show ?thesis
          using 2 u r32 lo hi by simp
      qed
    next
      case 3  (* narrow to 8 bits *)
      then show ?thesis
      proof -
        have hi: "sint r32 < 2^(outBits-1)"
          using r32 signed_take_bit_int_less_exp_word
          by (metis diff_le_mono less_imp_diff_less linorder_not_le one_le_numeral 
                power_increasing sint_above_size word_size)
        then have lo: "- (2^(outBits-1)) \<le> sint r32"
          using r32 signed_take_bit_int_greater_eq_minus_exp_word
          by (metis 3 add_diff_cancel_left' diff_less less_imp_diff_less numeral_Bit0 
             size32 wsst_TYs(3) zero_less_numeral)
        then show ?thesis
          using 3 u r32 lo hi by simp
      qed
    qed
  next (* TODO: proof is identical to above - combine them! *)
    case 2  (* input is IntVal64 *)
    print_facts
    then have r1: "result = narrow_helper inBits outBits (scast i64)"
      using assms by simp
    then have r2: "result =  (IntVal32 (signed_take_bit (outBits - 1) (scast i64)))"
      using assms by (metis narrow_helper.simps)
    then obtain r32 where 
      r32: "result = IntVal32 r32 \<and> r32 = signed_take_bit (outBits - 1) (scast i64)"
      by simp
    obtain b lo hi where "stamp_expr expr = IntegerStamp b lo hi"
      using assms 2 valid_value.elims(2) by blast
    (* now make stamp deductions *)
    then have u: "stamp_expr (UnaryExpr (UnaryNarrow inBits outBits) expr) 
             = unrestricted_stamp (IntegerStamp outBits lo hi)"
      using i by simp
    then consider "outBits=32" | "outBits=16" | "outBits=8"
      by (metis r1 assms(3) insertE narrow_helper.elims singletonD) 
    then show ?thesis
    proof (cases)
      case 1  (* narrow to 32 bits *)
      then show ?thesis 
        using r2 u unrestricted_32bit_always_valid by presburger 
    next      (* TODO: these next two cases have same proof - can we combine them? *)
      case 2  (* narrow to 16 bits *)
      then show ?thesis
      proof -
        have hi: "sint r32 < 2^(outBits-1)"
          using r32 signed_take_bit_int_less_exp_word
          by (metis diff_le_mono less_imp_diff_less linorder_not_le one_le_numeral 
                power_increasing sint_above_size word_size)
        then have lo: "- (2^(outBits-1)) \<le> sint r32"
          using r32 signed_take_bit_int_greater_eq_minus_exp_word
          by (metis 2 add_diff_cancel_left' diff_less less_imp_diff_less numeral_Bit0 
             size32 wsst_TYs(3) zero_less_numeral)
        then show ?thesis
          using 2 u r32 lo hi by simp
      qed
    next
      case 3  (* narrow to 8 bits *)
      then show ?thesis
      proof -
        have hi: "sint r32 < 2^(outBits-1)"
          using r32 signed_take_bit_int_less_exp_word
          by (metis diff_le_mono less_imp_diff_less linorder_not_le one_le_numeral 
                power_increasing sint_above_size word_size)
        then have lo: "- (2^(outBits-1)) \<le> sint r32"
          using r32 signed_take_bit_int_greater_eq_minus_exp_word
          by (metis 3 add_diff_cancel_left' diff_less less_imp_diff_less numeral_Bit0 
             size32 wsst_TYs(3) zero_less_numeral)
        then show ?thesis
          using 3 u r32 lo hi by simp
      qed
    qed
  qed
qed


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
  then show ?thesis sorry
next
  case UnaryNot
  then show ?thesis sorry
next
  case UnaryLogicNegation
  then show ?thesis sorry
next
  case (UnaryNarrow x51 x52)
  then show ?thesis using assms unary_narrow_implies_valid_value by presburger
next
  case (UnarySignExtend x61 x62)
  then show ?thesis sorry
next
  case (UnaryZeroExtend x71 x72)
  then show ?thesis sorry
qed


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

lemma binary_eval_values:
  assumes "\<exists>x y. result = IntVal32 x \<or> result = IntVal64 y"
  assumes "result = bin_eval op val1 val2"
  shows" \<exists>x32 x64 y32 y64. val1 = IntVal32 x32 \<and> val2 = IntVal32 y32 \<or> val1 = IntVal64 x64 \<and> val2 = IntVal64 y64"
  using assms apply (cases result)
      apply simp apply (cases op; cases val1; cases val2; auto)
    apply (cases op; cases val1; cases val2; auto) by auto+

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

  have "\<exists> x32 x64 y32 y64 . (val1 = IntVal32 x32 \<and> val2 = IntVal32 y32) \<or> (val1 = IntVal64 x64 \<and> val2 = IntVal64 y64)"
    using is_IntVal assms(3) binary_eval_values
    by presburger

(* TODO: we have a problem here with the 32-bit case, because
   the input stamps could be 32/16/8 bits.
   stamp_binary requires them to be the same, 
   but evaltree does not.
   Solution 1: add a graph invariant and then a tree invariant?
   Solution 2: relax stamp_binary to expand input stamps to 32-bit?
*)
  have "b1 = b2"
    using assms(3,4,5,6) stamp_expr1_def stamp_expr2_def
    using binary_eval_values
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
      then have bit32: "b = 32 \<or> b = 16 \<or> b = 8"
        using assms(1) IntegerStamp valid_value.simps valid32or64_both
        by (metis \<open>b = b2\<close> stamp2_def)
      then obtain x where val_def: "val = IntVal32 x"
        using IntegerStamp assms(1) valid32 valid_int16 valid_int8
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
    by (metis BinaryExprE Value.exhaust_disc assms(2) bin_eval.simps(11) binary_obj binary_undef evalDet intval_less_than.simps(9) is_ObjRef_def is_ObjStr_def xval_def)
  have "is_IntVal32 yval \<or> is_IntVal64 yval"
    by (metis BinaryExprE Value.exhaust_disc assms(2) bin_eval.simps(11) binary_obj binary_undef evalDet intval_less_than.simps(16) is_ObjRef_def is_ObjStr_def yval_def)
  have "is_IntVal32 xval = is_IntVal32 yval"
    by (metis BinaryExprE Value.collapse(2) \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> assms(2) bin_eval.simps(11) evalDet intval_less_than.simps(12) intval_less_than.simps(5) is_IntVal32_def xval_def yval_def)
  have "is_IntVal64 xval = is_IntVal64 yval"
    using \<open>is_IntVal32 xval = is_IntVal32 yval\<close> \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> by blast
  have "(intval_less_than xval yval) \<noteq> UndefVal"
    using assms(2)
    by (metis BinaryExprE bin_eval.simps(11) evalDet xval_def yval_def)
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
    by (metis BinaryExprE assms(2) bin_eval.simps(11) evalDet val_to_bool.simps(1) xval_def yval_def zero_neq_one)
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
    by (metis BinaryExprE Value.discI(1) Value.discI(2) assms(2) bin_eval.simps(11) binary_obj 
       constantAsStamp.elims evalDet evaltree_not_undef intval_less_than.simps(9) xval_def)
  have "is_IntVal32 yval \<or> is_IntVal64 yval"
    by (metis BinaryExprE Value.discI(1) Value.discI(2) assms(2) bin_eval.simps(11) binary_obj 
        constantAsStamp.elims evalDet evaltree_not_undef intval_less_than.simps(16) yval_def)
  have "is_IntVal32 xval = is_IntVal32 yval"
    by (metis BinaryExprE Value.collapse(2) \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> assms(2) bin_eval.simps(11) evalDet intval_less_than.simps(12) intval_less_than.simps(5) is_IntVal32_def xval_def yval_def)
  have "is_IntVal64 xval = is_IntVal64 yval"
    using \<open>is_IntVal32 xval = is_IntVal32 yval\<close> \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> by blast
  have "(intval_less_than xval yval) \<noteq> UndefVal"
    using assms(2)
    by (metis BinaryExprE bin_eval.simps(11) evalDet xval_def yval_def)
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
    by (metis BinaryExprE assms(2) bin_eval.simps(11) evalDet val_to_bool.simps(1) xval_def yval_def)
qed

end