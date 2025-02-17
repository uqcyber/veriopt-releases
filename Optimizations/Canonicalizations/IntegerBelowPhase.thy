(* x |<| (n |<| C ? 0 : n - C) \<mapsto> (x < n-c)*)
theory IntegerBelowPhase
  imports Common Proofs.StampEvalThms SubPhase
begin

phase IntegerBelowPhase
  terminating size
begin

(* Word level *)
lemma "uint(x) < uint(y) = (x < y)"
  by (simp add: word_less_def)

lemma pos_signed_unsigned:
  assumes "sint (x) \<ge> 0"
  shows "sint(x) = uint(x)"
proof -
  have "bit x (LENGTH('a)-Suc(0)) = False"
    using assms bit_last_iff by force
  then have "signed_take_bit (LENGTH('a)-Suc(0)) x = take_bit (LENGTH('a)-Suc(0)) x"
    by (simp add: signed_take_bit_eq_if_positive)
  then show ?thesis
    by (metis \<open>bit (x::'a word) (LENGTH('a) - Suc (0::nat)) = False\<close> bit_uint_iff 
        drop_bit_eq_zero_iff_not_bit_last signed_take_bit_eq_if_positive sint_uint 
        take_bit_eq_self_iff_drop_bit_eq_0 unsigned_take_bit_eq)
qed

lemma bin_below_eq_less:
  assumes "sint (x) \<ge> 0"
  assumes "sint (y) \<ge> 0"  
  shows "bin[less x y] = bin[word_sless x y]"
proof -
  have "(sint(x) < sint(y)) =  (uint(x) < uint(y))"
    by (metis assms(1) assms(2) pos_signed_unsigned)
  then show ?thesis
    by (simp add: word_less_iff_unsigned word_sless_alt)
qed

lemma bin_negate_below: "x \<noteq> y \<and> \<not>(x < y) \<Longrightarrow> y < x" for x y::int64
  by auto

lemma bin_negate_less: "x \<noteq> y \<and> \<not>(x <s y) \<Longrightarrow> y <s x" for x y::int64
  by auto

lemma bin_inverse_negate_less: "x \<noteq> y \<and> (x <s y) \<Longrightarrow> \<not>(y <s x)" for x y::int64
  by auto

lemma bin_below_sub: "(0 \<le>s x)\<and>(0 \<le>s y) \<Longrightarrow> (x <s y \<longleftrightarrow> (x - y) <s 0)" for x y::int64
  apply transfer apply auto
  apply (smt (verit) signed_take_bit_diff signed_take_bit_int_greater_self_iff signed_take_bit_int_less_exp signed_take_bit_negative_iff)


(* Value level *)

fun isIntValWf:: "Value \<Rightarrow> bool" where
"isIntValWf (IntVal n v) = ((take_bit n v = v) \<and> (1 < n) \<and> (n \<le> 64))" |
"isIntValWf _ = False"
(* "isValPositive (IntVal n v) = ((sint (signed_take_bit (n-Suc 0) v) \<ge> 0)\<and>(take_bit (n-1) v = v))" *)

fun isValPositive:: "Value \<Rightarrow> bool" where
"isValPositive (IntVal n v) = (\<not>bit v (n-Suc(0)))"

lemma newint_intval: 
  assumes "x = IntVal n v"
  assumes "isIntValWf x"
  shows "x = new_int n v"
proof -
  have "(take_bit n v) = v" 
    using assms by auto
  then show ?thesis
    by (simp add: assms(1))
qed

lemma tb_n1:
  assumes "x = IntVal n v"
  assumes "isIntValWf x" and "isValPositive x"
  shows "take_bit (n-1) v = v"
proof -
  have c1: "take_bit n v = (\<Sum>k::nat = 0::nat..<n. push_bit k (of_bool (bit v k)))"
    using take_bit_sum by auto
  have c2: "take_bit (n-1) v = (\<Sum>k::nat = 0::nat..<(n-1). push_bit k (of_bool (bit v k)))"
    using take_bit_sum by auto
  then have "(take_bit n v - take_bit (n-1) v) = push_bit (n-1) (of_bool (bit v (n-1)))"
    by (smt (verit) One_nat_def assms(1) assms(3) bit_take_bit_iff eq_iff_diff_eq_0 isValPositive.simps less_Suc_eq less_nat_zero_code linordered_semidom_class.add_diff_inverse not_gr_zero of_bool_eq(1) plus_1_eq_Suc push_bit_of_0 signed_take_bit_code signed_take_bit_eq_if_positive zero_less_diff)
  then have "... = 0"
    by (metis One_nat_def assms(1) assms(3) isValPositive.simps of_bool_eq(1) push_bit_of_0)
  then show ?thesis
    using \<open>take_bit (n::nat) (v::64 word) - take_bit (n - (1::nat)) v = push_bit (n - (1::nat)) (of_bool (bit v (n - (1::nat))))\<close> assms(1) assms(2) by force 
qed

lemma val_pos_def:
  assumes "n>1" and "n \<le> 64"
  fixes v::int64
  assumes "\<not> bit v (n-1)"
  assumes "take_bit n v = v"
  shows "0 \<le> sint (signed_take_bit (n-1) v)"
proof -
  have last_bit: "\<not> bit v (64-1)"
    by (metis Suc_mono add_diff_inverse_nat assms(2) assms(3) assms(4) bit_take_bit_iff 
        le_less_Suc_eq not_numeral_less_one plus_1_eq_Suc)
  show ?thesis using assms last_bit apply transfer using signed_take_bit_nonnegative_iff apply auto
    by (smt (verit) Suc_lessD Suc_pred signed_take_bit_int_eq_self_iff signed_take_bit_int_less_eq 
        signed_take_bit_negative_iff signed_take_bit_take_bit 
        take_bit_int_less_exp take_bit_nonnegative)
qed

lemma val_pos_bit:
  assumes "n>1" and "n \<le> 64"
  fixes v::int64
  assumes "take_bit n v = v"
  assumes "0 \<le> sint (signed_take_bit (n-1) v)"
  shows "\<not> bit v (n-1)" using assms apply transfer
  by (smt (verit, del_insts) One_nat_def Suc_leI bit_take_bit_iff diff_Suc_1 min.absorb2 min_diff signed_take_bit_nonnegative_iff signed_take_bit_signed_take_bit)

lemma val_bit_stake_eq:
  assumes "n>1" and "n \<le> 64"
  fixes v::int64
  assumes "take_bit n v = v"
  shows "(0 \<le> sint (signed_take_bit (n-1) v)) = (\<not> bit v (n-1))"
  by (metis assms(1) assms(2) assms(3) dual_order.refl order.strict_iff_not 
      signed_take_bit_eq_if_positive sint_0 take_bit_of_0 val_pos_bit val_pos_def)

lemma pos_greater_zero:
  assumes "x = IntVal n v"
  assumes "isIntValWf x"
  assumes "isValPositive x"
  shows "val[x < (IntVal n 0)] = IntVal 32 0"
proof -
  have "0 \<le> sint (signed_take_bit (n-1) v)"
    using assms(1) assms(2) assms(3) val_pos_def by auto
  then have "\<not>(sint (signed_take_bit (n-1) v) < 0)"
    by auto
  then show ?thesis using assms val_pos_def by auto
qed

lemma val_neg_def:
  assumes "n>1" and "n \<le> 64"
  fixes v::int64
  assumes "bit v (n-1)"
  shows "sint (signed_take_bit (n-1) v) < 0"
proof -
  have "signed_take_bit (n-1) v = or (take_bit (n-1) v) (not (mask (n-1)))"
    using assms(3) signed_take_bit_eq_if_negative by auto
  then show ?thesis using assms apply transfer using signed_take_bit_negative_iff apply auto
    by (simp add: bit_take_bit_iff)
qed

lemma neg_less_zero:
  assumes "x = IntVal n v"
  assumes "isIntValWf x"
  assumes "\<not>isValPositive x"
  shows "val[x < (IntVal n 0)] = IntVal 32 1"
proof -
  have "sint (signed_take_bit (n-1) v) < 0"
    using assms val_neg_def by simp
  then have "sint (signed_take_bit (n-1) v) < sint (signed_take_bit (n-1) 0)"
    by auto
  then show ?thesis using assms by simp
qed

(* Should be move to Less than phase *)
lemma pos_less_neg: 
  assumes "x = IntVal n vx" and "y = IntVal n vy"
  assumes "isIntValWf x" and "isIntValWf y"
  assumes "isValPositive x"
  assumes "\<not>isValPositive y"
  shows "val[x < y] = IntVal 32 0"
proof -
  have "val[y < (IntVal n 0)] = IntVal 32 1"
    using assms neg_less_zero by blast
  then have sint1: "sint (signed_take_bit (n - 1) vy) < sint (signed_take_bit (n - 1) 0)"
    using assms apply simp
    by (smt (verit, del_insts) Value.inject(1) bool_to_val.simps(2) zero_neq_one)
  have "val[x < IntVal n 0] = IntVal 32 0"
    using assms(1) assms(3) assms(5) pos_greater_zero by blast
  then have sint2: "sint (signed_take_bit (n - 1) 0) \<le> sint (signed_take_bit (n - 1) vx)"
    using assms apply simp
    using Value.inject(1) by fastforce
  have "sint (signed_take_bit (n - 1) vy) < sint (signed_take_bit (n - 1) vx)"
    using sint1 sint2 by auto
  then have "val[y < x] = IntVal 32 1"
    using assms by simp
  then have "\<not>val_to_bool(val[x < y])"
    using assms bin_inverse_negate_less apply simp
    by (metis (full_types) bool_to_val.simps(1) bool_to_val.simps(2) 
        signed.less_asym val_to_bool.simps(1) word_sless_alt)
  then show ?thesis
    using assms bin_negate_less apply simp
    by (metis (full_types) bool_to_val.simps(1) bool_to_val.simps(2) val_to_bool.simps(1))
qed

lemma verify_isValPositive:
  assumes "x = IntVal n v"
  assumes "isIntValWf x"
  assumes "isValPositive x"
  shows "sint(v) \<ge> 0"
  using assms pos_greater_zero apply auto
  using signed_take_bit_eq_if_positive tb_n1 val_pos_def by fastforce

lemma prot2:
  assumes "x = IntVal n vx"
  assumes "y = IntVal n vy"
  assumes "isValPositive x"
  assumes "isValPositive y"
  assumes "isIntValWf x"
  assumes "isIntValWf y"
  shows "(vx - vy) <s 0 \<longleftrightarrow> signed_take_bit (n-1) (take_bit n (vx - vy)) <s 0"
  sorry

lemma below_sub_inv:
  assumes "y = IntVal n vy"
  assumes "z = IntVal n vz"
  assumes "isValPositive y"
  assumes "isValPositive z"
  assumes "isIntValWf y"
  assumes "isIntValWf z"
  assumes "val_to_bool(val[y |<| z])"
  shows "\<not>isValPositive(val[y-z])"
proof -
  obtain tv where o1: "val[y-z] = IntVal n (take_bit n tv)"
    using assms(1) assms(2) by auto
  have "0 \<le>s vy"
    by (metis assms(1) assms(3) assms(5) signed_0 verify_isValPositive word_sle_eq)
  have "0 \<le>s vz"
    by (metis assms(2) assms(4) assms(6) signed_0 verify_isValPositive word_sle_eq)
  have "take_bit n (take_bit n tv) = take_bit n tv"
    by auto
  then have subIsWf: "isIntValWf (IntVal n (take_bit n tv))" 
    using assms by auto
  have subUnfold: "val[y-z] = IntVal n (take_bit n (vy - vz))"
    by (simp add: assms(1) assms(2))
  have "vy < vz" 
    using assms val_to_bool.elims(2) by fastforce 
  then have "vy <s vz"
    using assms bin_below_eq_less
    using verify_isValPositive by blast 
  then have "(vy - vz) <s 0"
    using bin_below_sub \<open>0 \<le>s vy\<close> \<open>0 \<le>s vz\<close> by auto
  then have "signed_take_bit (n-1) (take_bit n (vy - vz)) <s 0"
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) prot2 by blast
  then have subNotNeg: "\<not>(0 \<le> sint(signed_take_bit (n-1) (take_bit n (vy - vz))))"
    by (simp add: word_sless_alt)
  show ?thesis
    using subUnfold subIsWf subNotNeg val_pos_def by force
qed

lemma below_sub:
  assumes "y = IntVal n vy"
  assumes "z = IntVal n vz"
  assumes "isValPositive y"
  assumes "isValPositive z"
  assumes "isIntValWf y"
  assumes "isIntValWf z"
  assumes "val[y-z] \<noteq> UndefVal"
  assumes "\<not>val_to_bool(val[y |<| z])"
  shows "isValPositive(val[y-z])"
proof (cases "y = z")
  case True
  then have "val[y-z] = new_int n 0"
    using assms(1) by auto
  then have "val[y-z] = IntVal n (take_bit n 0)"
    by auto
  then have "val[y-z] = IntVal n 0"
    by simp
  then show ?thesis
    by (simp add: \<open>intval_sub (y::Value) (z::Value) = IntVal (n::nat) (0::64 word)\<close>)
next
  case False
  have "vz \<noteq> vy"
    using False assms(1) assms(2) by auto
  then have "\<not>(vy < vz)"
    using False assms by auto
  then have "vz < vy"
    using \<open>(vz::64 word) \<noteq> (vy::64 word)\<close> bin_negate_below by blast
  moreover have "sint(vz) \<ge> 0" 
    using assms verify_isValPositive by auto
  moreover have "sint(vy) \<ge> 0"
    using assms verify_isValPositive by auto
  ultimately have "vz <s vy" 
    using assms bin_below_eq_less by auto
  then have "\<not>(vy <s vz)"
    using \<open>vz \<noteq> vy\<close> bin_negate_less by auto
  then have "\<not>((vy - vz) <s 0)"
    using bin_below_sub by auto
  then have subPositive: "0 <s (vy-vz)"
    by (metis \<open>(vz::64 word) \<noteq> (vy::64 word)\<close> bin_negate_less eq_iff_diff_eq_0)
  obtain tv where o1: "val[y-z] = IntVal n (take_bit n tv)"
    using assms(1) assms(2) by auto
  have "take_bit n (take_bit n tv) = take_bit n tv"
    by auto
  then have subIsWf: "isIntValWf (IntVal n (take_bit n tv))" 
    using assms by auto
  have subUnfold: "val[y-z] = IntVal n (take_bit n (vy - vz))"
    by (simp add: assms(1) assms(2))
  have "\<not>(signed_take_bit (n-1) (take_bit n (vy - vz)) <s 0)"
    using \<open>\<not>((vy - vz) <s 0)\<close> prot2
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by blast
  then have subNotNeg: "0 \<le> sint(signed_take_bit (n-1) (take_bit n (vy - vz)))"
    by (simp add: word_sless_alt)
  show ?thesis
    using subIsWf subNotNeg subUnfold val_neg_def by fastforce
qed

lemma val_below_eq_less_self:
  assumes "x = IntVal n vx"
  assumes "isIntValWf x"
  assumes "isValPositive x" 
  shows "val[x |<| x] = val[x < x]"
proof -
  have "val[x |<| x] = IntVal 32 0" 
    using assms by auto
  moreover have "val[x < x] = IntVal 32 0"
    using assms by auto
  ultimately show ?thesis by auto
qed

lemma val_below_eq_less: 
  assumes "x = IntVal n vx" and "y = IntVal n vy"
  assumes "isIntValWf x" and "isIntValWf y"
  assumes "isValPositive x" 
  assumes "isValPositive y" 
  assumes "x \<noteq> y"
  assumes "val[x |<| y] \<noteq> UndefVal" and "val[x < y] \<noteq> UndefVal"
  shows "val[x |<| y] = val[x < y]"
proof (cases "val_to_bool(val[x |<| y])")
  case True
  have "vx < vy"
    using assms True apply simp
    by (metis (mono_tags, opaque_lifting) bool_to_val.simps(2) val_to_bool.simps(1))
  then have "(vx <s vy)"
    using assms verify_isValPositive apply simp
    by (smt (verit, ccfv_SIG) One_nat_def bin_below_eq_less order.trans
        signed_take_bit_eq_if_positive val_pos_def zero_less_one_class.zero_le_one)
  then have "sint vx < sint vy"
    using assms word_sless_alt by auto
  have "take_bit (n-1) vx = vx"
    using assms tb_n1 by blast
  then have "signed_take_bit (n-1) vx = vx"
    using assms by (simp add: signed_take_bit_eq_if_positive)
  have "take_bit (n-1) vy = vy"
    using assms tb_n1 by blast
  then have "signed_take_bit (n-1) vy = vy"
    using assms by (simp add: signed_take_bit_eq_if_positive)
  then have lift_word_val: "sint (signed_take_bit (n-1) vx) < sint (signed_take_bit (n-1) vy)"
    using \<open>signed_take_bit ((n::nat) - (1::nat)) (vx::64 word) = vx\<close> 
          \<open>sint (vx::64 word) < sint (vy::64 word)\<close> by auto
  then have "val_to_bool(val[x < y])"
    by (simp add: assms(1) assms(2))
  then show ?thesis
    using \<open>(vx::64 word) < (vy::64 word)\<close> assms(1) assms(2) lift_word_val by auto
next
  case False
  have "val_to_bool(val[y |<| x])"
    using assms False bin_negate_below
    by (metis (full_types) bool_to_val.simps(1) bool_to_val_bin.elims 
        intval_below.simps(1) val_to_bool.simps(1) zero_neq_one) 
  have "vy < vx"
    using assms False apply simp
    using linorder_less_linear by fastforce
  then have "(vy <s vx)"
    using assms verify_isValPositive apply simp
    by (smt (verit, ccfv_SIG) One_nat_def bin_below_eq_less order.trans
        signed_take_bit_eq_if_positive val_pos_def zero_less_one_class.zero_le_one)
  then have "sint vy < sint vx"
    using assms word_sless_alt by auto
  have "take_bit (n-1) vx = vx"
    using assms tb_n1 by blast
  then have "signed_take_bit (n-1) vx = vx"
    using assms by (simp add: signed_take_bit_eq_if_positive)
  have "take_bit (n-1) vy = vy"
    using assms tb_n1 by blast
  then have "signed_take_bit (n-1) vy = vy"
    using assms by (simp add: signed_take_bit_eq_if_positive)
  then have lift_word_val: "sint (signed_take_bit (n-1) vy) < sint (signed_take_bit (n-1) vx)"
    using \<open>signed_take_bit ((n::nat) - (1::nat)) (vx::64 word) = vx\<close> 
          \<open>sint (vy::64 word) < sint (vx::64 word)\<close> by auto
  then have "val_to_bool(val[y < x])"
    by (simp add: assms(1) assms(2))
  then have "\<not>val_to_bool(val[x < y])"
    using assms False bin_inverse_negate_less apply auto
    by (metis (no_types, opaque_lifting) bool_to_val.elims order.asym val_to_bool.simps(1))
  then show ?thesis
    using \<open>(vy::64 word) < (vx::64 word)\<close> \<open>signed_take_bit ((n::nat) - (1::nat)) (vx::64 word) = vx\<close> 
          \<open>signed_take_bit ((n::nat) - (1::nat)) (vy::64 word) = vy\<close> 
          \<open>sint (vy::64 word) < sint (vx::64 word)\<close> assms(1) assms(2) order_less_imp_not_less 
          by force
qed

lemma below_zero: 
  shows "val[(IntVal b v) |<| (IntVal b 0)] = IntVal 32 0"
  by auto

lemma val_below_less:
  assumes "x = IntVal n vx" and "y = IntVal n vy" and "z = IntVal n vz"
  assumes "isIntValWf x" and "isIntValWf y" and  "isIntValWf z" and "isIntValWf val[(y-z)]"
  assumes "isValPositive x"
  assumes "isValPositive y"
  assumes "isValPositive z"
  assumes "val[y-z] \<noteq> UndefVal"
  assumes "val[x |<| (y - z)] \<noteq> UndefVal"
  assumes "val[x < (y - z)] \<noteq> UndefVal"
  shows "val[(x |<| ((y |<| z)? (IntVal n 0) : (y - z)))] = val[x < (y-z)]"
proof(cases "val_to_bool (val[y |<| z])")
  case True
  then have unfoldCond: "val[(x |<| ((y |<| z)? 
                         (IntVal n 0) : (y - z)))] = val[x |<| (IntVal n 0)]"
    by simp
  then have t1: "val[x |<| (IntVal n 0)] = IntVal 32 0"
    using below_zero assms by auto  
  then have "\<not>isValPositive(val[y-z])"
    using True assms(10) assms(13) assms(2) assms(3) assms(5) assms(6) assms(9) below_sub_inv by auto
  then have "val[x < (y-z)] = IntVal 32 0"
    using assms pos_less_neg by simp
  then show ?thesis
    by (simp add: True t1)
next
  case False
  then have unfoldCond: "val[(x |<| ((y |<| z)? (IntVal n 0) : (y - z)))] = val[x |<| (y - z)]"
    by simp
  then have l2_1: "isValPositive(val[y-z])"
    using False assms(10) assms(13) assms(2) assms(3) assms(5) assms(6) assms(9) below_sub by auto
  obtain vyz where yz: "val[y-z] = new_int n vyz"
    using assms(2) assms(3) by auto
  then have "val[x |<| (y-z)] = val[x < (y-z)]" using bin_below_eq_less apply simp
    by (smt (verit, del_insts) assms(1) assms(12) assms(13) assms(4) assms(7) assms(8) l2_1 
        val_below_eq_less val_below_eq_less_self)
  then show ?thesis
    using unfoldCond by auto
qed

(* Exp level *)

(* Function to check is an integer stamp is not negative *)
fun isStampPos :: "Stamp \<Rightarrow> bool" where
  "isStampPos (IntegerStamp b lo hi) = ((lo \<ge> 0) \<and> (b \<le> 64) \<and> (1 < b))" |
  "isStampPos _ = False"

lemma lower_stamp2:
  assumes "isStampPos (stamp_expr x)" 
  assumes "wf_stamp x"
  assumes "[m,p] \<turnstile> x \<mapsto> xv"
  shows "\<exists>v n. xv = IntVal n v \<and> isIntValWf(xv)"
proof -
  obtain xVal where o1: "valid_value xVal (stamp_expr x)"
    using assms(2) assms(3) wf_stamp_def by auto
  obtain xValb xValv where o2: "xVal = IntVal xValb xValv"
    by (metis Value.exhaust \<open>valid_value (xVal::Value) (stamp_expr (x::IRExpr))\<close> assms(1) 
        isStampPos.elims(2) valid_value.simps(11) valid_value.simps(12) valid_value.simps(3) 
        valid_value.simps(5))
  obtain sB sLo sHi where o3:"(IntegerStamp sB sLo sHi) = (stamp_expr x)"
    by (metis \<open>(xVal::Value) = IntVal (xValb::nat) (xValv::64 word)\<close> 
        \<open>valid_value (xVal::Value) (stamp_expr (x::IRExpr))\<close> valid_int_gives)
  have bitEqual: "xValb = sB"
    by (metis \<open>(xVal::Value) = IntVal (xValb::nat) (xValv::64 word)\<close> 
        \<open>IntegerStamp (sB::nat) (sLo::int) (sHi::int) = stamp_expr (x::IRExpr)\<close> 
        \<open>valid_value (xVal::Value) (stamp_expr (x::IRExpr))\<close> valid_value.simps(1))
  then show ?thesis
    using assms bitEqual by (smt (verit, ccfv_SIG) eval_unused_bits_zero evaltree_not_undef 
          isIntValWf.elims(1) isStampPos.simps(1) o3 valid_int_same_bits 
          valid_value.simps(11) valid_value.simps(12) valid_value.simps(5) wf_stamp_def)
qed

lemma lower_stamp:
  assumes "isStampPos (stamp_expr x)" 
  assumes "wf_stamp x"
  assumes "[m,p] \<turnstile> x \<mapsto> xv"
  shows "isValPositive xv"
proof -
  obtain tb tv where "xv = IntVal tb tv"
    using assms(1) assms(2) assms(3) lower_stamp2 by blast
  then have "valid_value xv (stamp_expr x)"
    using assms(2) assms(3) wf_stamp_def by auto
  obtain sB sLo sHi where hi:"(IntegerStamp sB sLo sHi) = (stamp_expr x)"
    by (metis \<open>(xv::Value) = IntVal (tb::nat) (tv::64 word)\<close> 
        \<open>valid_value (xv::Value) (stamp_expr (x::IRExpr))\<close> valid_int_gives)
  have "tb = sB"
    by (metis \<open>(xv::Value) = IntVal (tb::nat) (tv::64 word)\<close> \<open>valid_value (xv::Value) 
        (stamp_expr (x::IRExpr))\<close> hi valid_value.simps(1))
  then have "sLo \<le> int_signed_value tb tv"
    by (metis \<open>(xv::Value) = IntVal (tb::nat) (tv::64 word)\<close> 
              \<open>valid_value (xv::Value) (stamp_expr (x::IRExpr))\<close> hi valid_value.simps(1))
  have "isStampPos (IntegerStamp sB sLo sHi)"
    by (simp add: assms(1) hi)
  then have "sLo \<ge> 0"
    using assms hi apply simp
    by (metis isStampPos.simps(1))
  then have "0 \<le> sint (signed_take_bit (tb-1) tv)"
    using \<open>(sLo::int) \<sqsubseteq> int_signed_value (tb::nat) (tv::64 word)\<close> by auto
  then have "sint (signed_take_bit (tb-1) 0) \<le> sint (signed_take_bit (tb-1) tv)"
    by simp
  then have "\<not> (bit tv (tb-1))"
    using assms signed_take_bit_nonnegative_iff apply simp
    by (metis (mono_tags, lifting) One_nat_def Suc_eq_plus1 \<open>(tb::nat) = (sB::nat)\<close> 
        \<open>isStampPos (IntegerStamp (sB::nat) (sLo::int) (sHi::int))\<close> bit_take_bit_iff 
        isStampPos.simps(1) less_diff_conv less_numeral_extra(3) linorder_not_less nat_diff_split 
        plus_1_eq_Suc take_bit_0 val_neg_def)
  then show ?thesis
    by (simp add: \<open>(xv::Value) = IntVal (tb::nat) (tv::64 word)\<close>)
qed

lemma exp_below_less: 
  assumes "isStampPos (stamp_expr x)" and "wf_stamp x"
  assumes "isStampPos (stamp_expr y)" and "wf_stamp y"
  assumes "isStampPos (stamp_expr z)" and "wf_stamp z"
  assumes "stamp_expr y = IntegerStamp b lo hi"
  shows "exp[(x |<| ((y |<| z)? const (IntVal b 0) : (y - z)))] \<ge> exp[x < (y-z)]"
  apply auto
  subgoal premises prems for m p xa ya xaa yaa xb yb
  proof-
    have xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(1) by auto
    then have xaPos: "isValPositive xa"
      using assms(1) assms(2) lower_stamp by auto
    then have lhsDef: "val[xa |<| ya] \<noteq> UndefVal"
      using xa evalDet prems(1) prems(2) by blast
    then have "val[xaa |<| yaa] \<noteq> UndefVal"
      by (simp add: prems(3))
    then have wfCond: "[m,p] \<turnstile> (if (val_to_bool(val[xaa |<| yaa])) 
                        then exp[const (IntVal b 0)] else exp[(y - z)]) \<mapsto> ya"
      by (simp add: prems(4))
    then have "val[ya] \<noteq> UndefVal"
      by (simp add: prems(5))
    obtain yab yav where ya: "ya = IntVal yab yav"
      by (metis Value.collapse(1) bin_eval.simps(15) defined_eval_is_intval lhsDef)
    have "val[xb - yb] \<noteq> UndefVal"
      by (simp add: prems)
    have yValue: "[m,p] \<turnstile> y \<mapsto> xaa"
      by (simp add: prems)
    then have xaaPos: "isValPositive xaa"
      using assms(3) assms(4) lower_stamp by auto
    have zValue: "[m,p] \<turnstile> z \<mapsto> yaa"
      by (simp add: prems)
    then have yaaPos: "isValPositive yaa"
      using assms(5) assms(6) lower_stamp by auto
    have "[m,p] \<turnstile> y \<mapsto> xb"
      by (simp add: prems)
    have "[m,p] \<turnstile> z \<mapsto> yb"
      by (simp add: prems)
    have "wf_value (IntVal b 0)"
      by (simp add: prems(11))
    obtain vxb vx where xa: "xa = IntVal vxb vx"
      using assms(1) assms(2) lower_stamp2 xa by blast
    have "vxb = yab" using ya
      by (metis bool_to_val_bin.simps intval_below.simps(1) lhsDef xa)
    obtain vyb vy where hello1: "xaa = IntVal vyb vy"
      by (meson assms(3) assms(4) lower_stamp2 yValue)
    obtain vzb vz where hello2: "yaa = IntVal vzb vz"
      using assms(5) assms(6) lower_stamp2 zValue by blast
    have "vyb = vzb"
      using bool_to_val_bin.simps hello1 hello2 intval_below.simps(1) prems(3) by presburger
    have wf_rhs1:"[m,p] \<turnstile> exp[y-z] \<mapsto> val[xaa - yaa]"
      using yValue zValue
      by (metis bin_eval.simps(2) evalDet prems(10) prems(6) prems(9) unfold_binary)
    then have sub_iv: "val[xaa - yaa] = new_int b (vy - vz)"
      using hello1 hello2 prems
      by (metis \<open>(vyb::nat) = (vzb::nat)\<close> assms(4) assms(7) intval_sub.simps(1) 
          new_int_bin.simps valid_int_same_bits wf_stamp_def)
    then obtain vdiff where hello3: "val[xaa-yaa] = IntVal b vdiff"
      by simp
    have "vxb = b" using hello3
      by (smt (verit) ConstantExprE Value.inject(1) \<open>(vxb::nat) = (yab::nat)\<close> 
          evalDet wfCond wf_rhs1 ya)
    then have "val[xa < (xaa - yaa)] \<noteq> UndefVal"
      using xa hello3 apply auto
      by (metis Value.distinct(1) bool_to_val.simps(1) bool_to_val.simps(2))
    then have wf_rhs:"[m,p] \<turnstile> exp[x < (y-z)] \<mapsto> val[xa < (xaa - yaa)]"
      apply (auto simp add: unfold_binary)
      by (metis intval_less_than.simps(6) prems(1) yValue zValue)
    then have "[m,p] \<turnstile> exp[x < (y-z)] \<mapsto> val[xa |<| ya]"
    proof (cases "val_to_bool(val[xaa |<| yaa])")
      case True
      have "isIntValWf(val[xaa - yaa])"
        using \<open>intval_sub (xaa::Value) (yaa::Value) = new_int (b::nat) ((vy::64 word) - (vz::64 word))\<close> assms(3) assms(7) by auto
      then have "\<not>isValPositive(val[xaa - yaa])"
        using lower_stamp below_sub_inv sub_iv xaaPos yaaPos
        by (smt (verit) True \<open>(vyb::nat) = (vzb::nat)\<close> assms(3) assms(4) assms(5) assms(6) 
            below_zero cancel_comm_monoid_add_class.diff_cancel hello1 hello2 intval_below.simps(1) 
            lower_stamp2 val_to_bool.simps(1) word_sub_less_iff yValue zValue)
      then have "val_to_bool(val[xa |<| ya]) = False"
        using True assms(7) prems(4) xa \<open>(vxb::nat) = (b::nat)\<close> by auto
      then have "val[xa < (xaa - yaa)] = IntVal 32 0"
        using wf_rhs assms pos_less_neg \<open>\<not> isValPositive (intval_sub (xaa::Value) (yaa::Value))\<close> xaPos apply simp
        by (metis \<open>(vxb::nat) = (b::nat)\<close> \<open>isIntValWf (intval_sub (xaa::Value) (yaa::Value))\<close> hello3 lower_stamp2 pos_less_neg prems(1) xa)
      then have "val[xa |<| ya] = IntVal 32 0"
        using True \<open>(vxb::nat) = (b::nat)\<close> wfCond xa by auto
      then show ?thesis
        using \<open>intval_less_than (xa::Value) (intval_sub (xaa::Value) (yaa::Value)) = IntVal (32::nat) (0::64 word)\<close> wf_rhs by auto 
    next
      case False
      then have "isValPositive(val[xaa-yaa])"
        using assms below_sub lower_stamp
        by (metis Value.distinct(1) \<open>(vyb::nat) = (vzb::nat)\<close> hello1 hello2 hello3 
            lower_stamp2 yValue zValue)
      then have "val[xa |<| ya] = val[xa |<| (xaa-yaa)]"
        by (metis False evalDet prems(4) wf_rhs1)
      then have "val[xa |<| (xaa - yaa)] = val[xa < (xaa - yaa)]"
        using assms val_below_eq_less xaPos wf_rhs
        by (smt (verit, del_insts) False \<open>(vxb::nat) = (b::nat)\<close> \<open>(vxb::nat) = (yab::nat)\<close> 
            \<open>intval_less_than (xa::Value) (intval_sub (xaa::Value) (yaa::Value)) \<noteq> UndefVal\<close> 
            \<open>isValPositive (intval_sub (xaa::Value) (yaa::Value))\<close> evalDet isIntValWf.simps(1) 
            lhsDef lower_stamp2 new_int_unused_bits_zero prems(1) sub_iv val_below_eq_less_self 
            wfCond wf_rhs1 xa ya)
      then show ?thesis
        by (simp add: \<open>intval_below (xa::Value) (ya::Value) = intval_below xa (intval_sub (xaa::Value) (yaa::Value))\<close> wf_rhs)
    qed
    then show ?thesis
      by auto
  qed
  done

optimization test1: "(x |<| ((y |<| z)? const (IntVal b 0) : (y - z))) \<longmapsto> x < (y-z)
                      when ((isStampPos (stamp_expr x)) \<and> (wf_stamp x) \<and>
                             (isStampPos (stamp_expr y)) \<and> (wf_stamp y) \<and>
                             (isStampPos (stamp_expr z)) \<and> (wf_stamp z)) \<and>
                               stamp_expr y = IntegerStamp b lo hi"
  using exp_below_less by blast