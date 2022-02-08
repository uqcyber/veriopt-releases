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

lemma unary_eval_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
proof -
  have is_IntVal: "\<exists> x y. result = IntVal32 x \<or> result = IntVal64 y"
    using assms(2,3) apply (cases op; auto; cases val; auto)
    apply metis
    by metis
  then have "is_IntegerStamp (stamp_expr expr)"
    using assms(2,3,4) apply (cases "(stamp_expr expr)"; auto) 
    using valid_VoidStamp unary_undef apply simp
    using valid_VoidStamp unary_undef apply simp
    using valid_ObjStamp unary_obj apply fastforce
    using valid_ObjStamp unary_obj by fastforce
  then obtain b lo hi where stamp_expr_def: "stamp_expr expr = (IntegerStamp b lo hi)"
    using is_IntegerStamp_def by auto
  then have "stamp_expr (UnaryExpr op expr) = unrestricted_stamp (IntegerStamp b lo hi)"
    using stamp_expr.simps(1) stamp_unary.simps(1) by presburger
  from stamp_expr_def have bit32: "b = 32 \<Longrightarrow> \<exists> x. result = IntVal32 x"
    using assms(2,3,4) by (cases op; auto; cases val; auto) 
  from stamp_expr_def have bit64: "b = 64 \<Longrightarrow> \<exists> x. result = IntVal64 x" 
    using assms(2,3,4) by (cases op; auto; cases val; auto) 

  show ?thesis using valid_value.simps(1,2)
    unrestricted_32bit_always_valid unrestricted_64bit_always_valid stamp_expr_def
    bit32 bit64
    by (metis \<open>stamp_expr (UnaryExpr op expr) = unrestricted_stamp (IntegerStamp b lo hi)\<close> assms(4) valid32or64_both)
qed

lemma binary_undef: "v1 = UndefVal \<or> v2 = UndefVal \<Longrightarrow> bin_eval op v1 v2 = UndefVal"
  by (cases op; auto)

lemma binary_obj: "v1 = ObjRef x \<or> v2 = ObjRef y \<Longrightarrow> bin_eval op v1 v2 = UndefVal"
  by (cases op; auto)

lemma binary_eval_bits_equal:
  assumes "result = bin_eval op val1 val2"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val1 (IntegerStamp b1 lo1 hi1)"
  assumes "valid_value val2 (IntegerStamp b2 lo2 hi2)"
  shows "b1 = b2"
  using assms 
  by (cases op; cases val1; cases val2; auto) (*slow*)

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
    
  have "b1 = b2"
    using assms(3,4,5,6) stamp_expr1_def stamp_expr2_def
    using binary_eval_bits_equal
    by auto 
  then have stamp_def: "stamp_expr (BinaryExpr op expr1 expr2) = 
    (case op \<in> fixed_32 of True \<Rightarrow> unrestricted_stamp (IntegerStamp 32 lo1 hi1)| False \<Rightarrow> unrestricted_stamp (IntegerStamp b1 lo1 hi1))"
    using stamp_expr.simps(2) stamp_binary.simps(1)
    using stamp_expr1_def stamp_expr2_def by presburger
  from stamp_expr1_def have bit32: "b1 = 32 \<Longrightarrow> \<exists> x. result = IntVal32 x"
    using assms apply (cases op; cases val1; cases val2; auto) (*slow*)
    by (meson Values.bool_to_val.elims)+
  from stamp_expr1_def have bit64: "b1 = 64 \<and> op \<notin> fixed_32 \<Longrightarrow> \<exists> x y. result = IntVal64 x" 
    using assms apply (cases op; cases val1; cases val2; simp) (*slow*)
    using fixed_32_def by auto+
  from stamp_expr1_def have fixed: "op \<in> fixed_32 \<Longrightarrow> \<exists> x y. result = IntVal32 x" 
    using assms unfolding fixed_32_def apply (cases op; auto)
    apply (cases val1; cases val2; auto)
    using bit32 apply fastforce 
      apply (meson Values.bool_to_val.elims)
     apply (cases val1; cases val2; auto) 
    using bit32 apply fastforce
     apply (meson Values.bool_to_val.elims)
      apply (cases val1; cases val2; auto) 
    using bit32 apply fastforce
    by (meson Values.bool_to_val.elims)

  show ?thesis apply (cases "op \<in> fixed_32") defer using valid_value.simps(1,2)
    unrestricted_32bit_always_valid unrestricted_64bit_always_valid stamp_expr1_def
    bit32 bit64 stamp_def apply auto
    using \<open>\<exists>x32 x64 y32 y64. val1 = IntVal32 x32 \<and> val2 = IntVal32 y32 \<or> val1 = IntVal64 x64 \<and> val2 = IntVal64 y64\<close> assms(5) apply auto[1]
    using fixed by force
qed

lemma stamp_meet_is_valid:
  assumes "valid_value val stamp1 \<or> valid_value val stamp2"
  assumes "meet stamp1 stamp2 \<noteq> IllegalStamp"
  shows "valid_value val (meet stamp1 stamp2)"
  using assms proof (cases stamp1)
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
  then show ?thesis proof (cases "b = 32")
    case True
    then obtain x where val_def: "val = IntVal32 x"
      using IntegerStamp assms(1) valid32
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
    then have bit64: "b = 64"
      using assms(1) IntegerStamp valid_value.simps
      valid32or64_both
      by (metis \<open>b = b2\<close> stamp2_def)
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
      by (simp add: bit64 meet_def val_def)
  qed
next
  case (KlassPointerStamp x31 x32)
  then show ?thesis using assms valid_value.elims(2)
    by (metis meet.simps(14) valid_value.simps(21))
next
  case (MethodCountersPointerStamp x41 x42)
  then show ?thesis using assms valid_value.elims(2)
    by (metis meet.simps(39) valid_value.simps(22))
next
  case (MethodPointersStamp x51 x52)
then show ?thesis using assms valid_value.elims(2)
  by (metis meet.simps(40) valid_value.simps(23))
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
    using assms(2) binary_eval_bits_equal valid_value.elims(2) xval_def
    by (metis Value.distinct(9) Value.distinct_disc(9) \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> \<open>is_IntVal64 xval = is_IntVal64 yval\<close> is_IntVal32_def xvalid yval_def yvalid)
  have "is_IntVal64 xval \<Longrightarrow> ((\<exists> lo hi. stamp_expr x = IntegerStamp 64 lo hi) \<and> (\<exists> lo hi. stamp_expr y = IntegerStamp 64 lo hi))"
    by (metis (full_types) \<open>is_IntVal64 xval = is_IntVal64 yval\<close> is_IntVal64_def stamprange valid_value.simps(2) xval_def xvalid yval_def yvalid)
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
    by (metis is_IntVal32_def is_IntVal64_def xvalid valid_value.elims(2) xval_def)
  have "is_IntVal32 yval \<or> is_IntVal64 yval"
    by (metis is_IntVal32_def is_IntVal64_def yvalid valid_value.elims(2) yval_def)
  have "is_IntVal32 xval = is_IntVal32 yval"
    by (metis BinaryExprE Value.collapse(2) \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> assms(2) bin_eval.simps(11) evalDet intval_less_than.simps(12) intval_less_than.simps(5) is_IntVal32_def xval_def yval_def)
  have "is_IntVal64 xval = is_IntVal64 yval"
    using \<open>is_IntVal32 xval = is_IntVal32 yval\<close> \<open>is_IntVal32 xval \<or> is_IntVal64 xval\<close> \<open>is_IntVal32 yval \<or> is_IntVal64 yval\<close> by blast
  have "(intval_less_than xval yval) \<noteq> UndefVal"
    using assms(2)
    by (metis BinaryExprE bin_eval.simps(11) evalDet xval_def yval_def)
  have "is_IntVal32 xval \<Longrightarrow> ((\<exists> lo hi. stamp_expr x = IntegerStamp 32 lo hi) \<and> (\<exists> lo hi. stamp_expr y = IntegerStamp 32 lo hi))"
    by (smt (verit) BinaryExprE Value.discI(2) Value.distinct_disc(9) assms(2) binary_eval_bits_equal xvalid yvalid valid_value.elims(2) xval_def)
  have "is_IntVal64 xval \<Longrightarrow> ((\<exists> lo hi. stamp_expr x = IntegerStamp 64 lo hi) \<and> (\<exists> lo hi. stamp_expr y = IntegerStamp 64 lo hi))"
    by (smt (verit, best) BinaryExprE \<open>intval_less_than xval yval \<noteq> UndefVal\<close> assms(2) binary_eval_bits_equal intval_less_than.simps(5) is_IntVal64_def xvalid yvalid valid_value.elims(2) yval_def)
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