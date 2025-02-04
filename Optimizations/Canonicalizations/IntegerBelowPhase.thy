(* x |<| (n |<| C ? 0 : n - C) \<mapsto> (x < n-c)*)
theory IntegerBelowPhase
  imports Common Proofs.StampEvalThms
begin

phase IntegerBelowPhase
  terminating size
begin

(* Word level *)
lemma "uint(x) < uint(y) = (x < y)"
  by (simp add: word_less_def)

value"sint(3::int64) - sint(4::int64)"

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

lemma below_transitive: "x < y \<and> y < z \<Longrightarrow> x < z" for x y z::int64
  by auto

lemma bin_below_zero: "x < 0 \<and> 0 < y \<Longrightarrow> ~(y < z)" for x y z::int64
  using word_not_simps(1) by blast

lemma bin_negate_below: "x \<noteq> y \<and> \<not>(x < y) \<Longrightarrow> y < x" for x y::int64
  by auto

lemma bin_negate_less: "x \<noteq> y \<and> \<not>(x <s y) \<Longrightarrow> y <s x" for x y::int64
  by auto

lemma bin_inverse_negate_less: "x \<noteq> y \<and> (x <s y) \<Longrightarrow> \<not>(y <s x)" for x y::int64
  by auto

lemma bin_below_sub: "x < y \<Longrightarrow> (x - y) <s 0" for x y::int64
  sorry

(* Value level *)

fun isIntValWf:: "Value \<Rightarrow> bool" where
"isIntValWf (IntVal n v) = (take_bit n v = v)" |
"isIntValWf _ = False"
(* "isValPositive (IntVal n v) = ((sint (signed_take_bit (n-Suc 0) v) \<ge> 0)\<and>(take_bit (n-1) v = v))" *)

fun isValPositive:: "Value \<Rightarrow> bool" where
"isValPositive (IntVal n v) = (\<not>bit v (n-Suc(0)))"

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
    by (metis (no_types, lifting) One_nat_def Suc_diff_1 add_cancel_right_right assms(1) assms(2) assms(3) bit_take_bit_iff c1 cancel_comm_monoid_add_class.diff_cancel isIntValWf.simps isValPositive.simps less_imp_diff_less of_bool_def push_bit_of_0 sum.atLeast0_lessThan_Suc sum.neutral)
  then have "... = 0"
    by (metis One_nat_def assms(1) assms(3) isValPositive.simps of_bool_eq(1) push_bit_of_0)
  then show ?thesis
    using \<open>take_bit (n::nat) (v::64 word) - take_bit (n - (1::nat)) v = push_bit (n - (1::nat)) (of_bool (bit v (n - (1::nat))))\<close> assms(1) assms(2) by force 
qed

lemma neg_sub:
  shows "(val_to_bool val[y < z]) \<Longrightarrow> val[y-z] = IntVal 32 0"
  oops

lemma val_pos_def:
  (* assumes "n>1" and "n \<le> 64" *)
  assumes "n = 64"
  fixes v::int64
  assumes " v \<noteq> 0"
  assumes "\<not> bit v (n-1)"
  assumes "take_bit n v = v"
  shows "0 < sint (signed_take_bit (n-1) v)"
proof -
 (* have "signed_take_bit (n-1) v = take_bit (n-1) v"
    using assms(4) signed_take_bit_eq_if_positive by auto
  then have "0 \<le> sint (signed_take_bit (n-1) v) = (0 \<le> sint (v))"
    using assms(5) by auto*)
  have last_bit: "\<not> bit v (64-1)"
    by (metis assms bit_take_bit_iff less_diff_iff less_or_eq_imp_le one_le_numeral verit_comp_simplify1(3))
  (*then have "signed_take_bit (64-1) v = take_bit (64-1) v"
    by (simp add: signed_take_bit_eq_if_positive)*)
  show ?thesis using assms last_bit apply transfer using signed_take_bit_nonnegative_iff apply auto
    by (smt (verit) Suc_numeral bit_take_bit_iff not_take_bit_negative semiring_norm(2) semiring_norm(8) signed_take_bit_int_less_eq signed_take_bit_int_less_self_iff signed_take_bit_negative_iff take_bit_int_less_exp)
qed

lemma pos_greater_zero:
  assumes "x = IntVal n v"
  (* assumes "n > 1" and "n \<le> 64" *)
  assumes "isIntValWf x"
  assumes "n = 64"
  assumes "isValPositive x"
  assumes "v \<noteq> 0"
  shows "val[(IntVal n 0) < x] = IntVal 32 1"
  using assms val_pos_def by auto

lemma val_neg_def:
  (* assumes "n>1" and "n \<le> 64" *)
  assumes "n=64"
  fixes v::int64
  assumes "v \<noteq> 0"
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
  (* assumes "n > 1" and "n \<le> 64" *)
  assumes "n = 64"
  assumes "\<not>isValPositive x"
  assumes "v \<noteq> 0"
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
  (* assumes "n > 1" and "n \<le> 64" *)
  assumes "isIntValWf x" and "isIntValWf y"
  assumes "n = 64"
  assumes "vx \<noteq> 0" and "vy \<noteq> 0"
  assumes "vx \<noteq> vy"
  assumes "isValPositive x"
  assumes "\<not>isValPositive y"
  shows "val[x < y] = IntVal 32 0"
proof -
  have "val[y < (IntVal n 0)] = IntVal 32 1"
    using assms neg_less_zero by blast
  then have sint1: "sint (signed_take_bit (n - 1) vy) < sint (signed_take_bit (n - 1) 0)"
    using assms apply simp
    by (smt (verit, del_insts) Value.inject(1) bool_to_val.simps(2) zero_neq_one)
  have "val[(IntVal n 0) < x] = IntVal 32 1"
    using assms pos_greater_zero by blast
  then have sint2: "sint (signed_take_bit (n - 1) 0) < sint (signed_take_bit (n - 1) vx)"
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
  assumes "n = 64"
  assumes "isValPositive x"
  assumes "v \<noteq> 0"
  shows "sint(v) \<ge> 0"
  using assms pos_greater_zero apply auto
  using signed_take_bit_eq_if_positive tb_n1 val_pos_def by fastforce

lemma below_sub:
  assumes "isValPositive y"
  assumes "isValPositive z"
  shows "(\<not>val_to_bool (val[y |<| z])) \<Longrightarrow> isValPositive(val[y-z])"
  using assms bin_below_sub
  sorry

lemma below_sub_inv:
  assumes "isValPositive y"
  assumes "isValPositive z"
  assumes "isIntValWf y"
  assumes "isIntValWf z"
  assumes "y \<noteq> z"
  assumes "val_to_bool(val[y |<| z])"
  shows "\<not>isValPositive(val[y-z])"
  using assms bin_below_sub apply auto
  sorry

lemma val_below_eq_less: 
  assumes "x = IntVal n vx" and "y = IntVal n vy"
  (* assumes "n > 1" and "n \<le> 64" *)
  assumes "isIntValWf x" and "isIntValWf y"
  assumes "n = 64"
  assumes "vx \<noteq> 0" and "vy \<noteq> 0" and "vx \<noteq> vy"
  assumes "isValPositive x" 
  assumes "isValPositive y" 
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
  assumes "n = 64"
  assumes "isIntValWf x" and "isIntValWf y" and  "isIntValWf z" and "isIntValWf val[(y-z)]"
  assumes "vx \<noteq> vy"
  assumes "isValPositive x"
  assumes "isValPositive y"
  assumes "isValPositive z"
  assumes "val[y-z] \<noteq> UndefVal"
  assumes "vx \<noteq> (vy - vz)"
  assumes "vx \<noteq> 0" and "vy \<noteq> 0" and "vz \<noteq> 0"
  assumes "vy \<noteq> vz"
  assumes "val[x |<| (y - z)] \<noteq> UndefVal"
  assumes "val[x < (y - z)] \<noteq> UndefVal"
  shows "val[(x |<| ((y |<| z)? (IntVal 64 0) : (y - z)))] = val[x < (y-z)]"
proof(cases "val_to_bool (val[y |<| z])")
  case True
  then have unfoldCond: "val[(x |<| ((y |<| z)? 
                         (IntVal 64 0) : (y - z)))] = val[x |<| (IntVal 64 0)]"
    by simp
  then have t1: "val[x |<| (IntVal 64 0)] = IntVal 32 0"
    using below_zero assms by auto  
  then have "\<not>isValPositive(val[y-z])"
    by (simp add: True assms(11) assms(12) below_sub_inv)
  then have "val[x < (y-z)] = IntVal 32 0"
    using assms pos_less_neg apply simp
    by (metis (no_types, opaque_lifting) ValueThms.take_bit_dist_subL bit_take_bit_iff diff_zero take_bit_0)
  then show ?thesis
    by (simp add: True t1)
next
  case False
  then have unfoldCond: "val[(x |<| ((y |<| z)? (IntVal 64 0) : (y - z)))] = val[x |<| (y - z)]"
    by simp
  then have l2_1: "isValPositive(val[y-z])"
    by (simp add: False assms(12) assms(11) below_sub)
  obtain vyz where yz: "val[y-z] = new_int n vyz"
    using assms by (simp add: yz)
  obtain yz where yz: "yz = new_int n vyz"
    by auto
  have "isIntValWf yz"
    by (simp add: yz)
  moreover have "isValPositive(yz)"
    using yz l2_1
  moreover have "val[x |<| yz] \<noteq> UndefVal"
    sorry
  moreover have "val[x < yz] \<noteq> UndefVal"
    sorry
  moreover have "vyz \<noteq> 0"
    sorry
  ultimately have "val[x |<| yz] = val[x < yz]"
    (* using assms val_below_eq_less yz by blast *)
    sorry
  then show ?thesis
    (* using unfoldCond by auto *)
    sorry
qed

(* Exp level *)

(* Function to check is an integer stamp is not negative *)
fun isStampPos :: "Stamp \<Rightarrow> bool" where
  "isStampPos (IntegerStamp b lo hi) = ((lo \<ge> 0) \<and> (b = 64))" |
  "isStampPos _ = False"

lemma lower_stamp:
  assumes "isStampPos (stamp_expr x)" 
  assumes "wf_stamp x"
  assumes "[m,p] \<turnstile> x \<mapsto> xv"
  shows "isValPositive xv"
proof -
  obtain xVal where "valid_value xVal (stamp_expr x)"
    using assms(2) assms(3) wf_stamp_def by auto
  obtain xValb xValv where "xVal = IntVal xValb xValv"
    by (metis Value.exhaust \<open>valid_value (xVal::Value) (stamp_expr (x::IRExpr))\<close> assms(1) 
        isStampPos.elims(2) valid_value.simps(11) valid_value.simps(12) valid_value.simps(3) 
        valid_value.simps(5))
  obtain sB sLo sHi where hi:"(IntegerStamp sB sLo sHi) = (stamp_expr x)"
    by (metis \<open>(xVal::Value) = IntVal (xValb::nat) (xValv::64 word)\<close> 
        \<open>valid_value (xVal::Value) (stamp_expr (x::IRExpr))\<close> valid_int_gives)
  have "xValb = sB"
    by (metis \<open>(xVal::Value) = IntVal (xValb::nat) (xValv::64 word)\<close> 
        \<open>IntegerStamp (sB::nat) (sLo::int) (sHi::int) = stamp_expr (x::IRExpr)\<close> 
        \<open>valid_value (xVal::Value) (stamp_expr (x::IRExpr))\<close> valid_value.simps(1))
  then have "sLo \<le> int_signed_value xValb xValv"
    by (metis \<open>(xVal::Value) = IntVal (xValb::nat) (xValv::64 word)\<close> \<open>IntegerStamp (sB::nat) (sLo::int) (sHi::int) = stamp_expr (x::IRExpr)\<close> \<open>valid_value (xVal::Value) (stamp_expr (x::IRExpr))\<close> valid_value.simps(1))
  have "isStampPos (IntegerStamp sB sLo sHi)"
    by (simp add: assms(1) hi)
  then have "sLo \<ge> 0"
    using assms hi apply simp
    by (metis isStampPos.simps(1))
  then have "0 \<le> sint (signed_take_bit (xValb-1) xValv)"
    using assms
    using \<open>(sLo::int) \<sqsubseteq> int_signed_value (xValb::nat) (xValv::64 word)\<close> by auto
  then have "sint (signed_take_bit (xValb-1) 0) \<le> sint (signed_take_bit (xValb-1) xValv)"
    by simp
  then have "\<not> (bit xValv (xValb-1))"
    using assms signed_take_bit_nonnegative_iff apply simp

lemma lower_stamp2:
  assumes "isStampPos (stamp_expr x)" 
  assumes "wf_stamp x"
  assumes "[m,p] \<turnstile> x \<mapsto> xv"
  shows "\<exists>v. xv = IntVal 64 v"
proof -
  obtain xVal where "valid_value xVal (stamp_expr x)"
    using assms(2) assms(3) wf_stamp_def by auto
  obtain xValb xValv where "xVal = IntVal xValb xValv"
    by (metis Value.exhaust \<open>valid_value (xVal::Value) (stamp_expr (x::IRExpr))\<close> assms(1) 
        isStampPos.elims(2) valid_value.simps(11) valid_value.simps(12) valid_value.simps(3) 
        valid_value.simps(5))
  obtain sB sLo sHi where "(IntegerStamp sB sLo sHi) = (stamp_expr x)"
    by (metis \<open>(xVal::Value) = IntVal (xValb::nat) (xValv::64 word)\<close> 
        \<open>valid_value (xVal::Value) (stamp_expr (x::IRExpr))\<close> valid_int_gives)
  have "xValb = sB"
    by (metis \<open>(xVal::Value) = IntVal (xValb::nat) (xValv::64 word)\<close> 
        \<open>IntegerStamp (sB::nat) (sLo::int) (sHi::int) = stamp_expr (x::IRExpr)\<close> 
        \<open>valid_value (xVal::Value) (stamp_expr (x::IRExpr))\<close> valid_value.simps(1))
  then show ?thesis
    by (metis assms(1) assms(2) assms(3) isStampPos.elims(2) valid_int wf_stamp_def)
qed

lemma exp_below_less: 
  assumes "isStampPos (stamp_expr x)" and "wf_stamp x"
  assumes "isStampPos (stamp_expr y)" and "wf_stamp y"
  assumes "isStampPos (stamp_expr z)" and "wf_stamp z"
  assumes "b = 64"
  assumes "exp[x] \<noteq> exp[(y-z)]"
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
    then have "[m,p] \<turnstile> (if (val_to_bool(val[xaa |<| yaa])) 
                        then exp[const (IntVal b 0)] else exp[(y - z)]) \<mapsto> ya"
      by (simp add: prems(4))
    then have "val[ya] \<noteq> UndefVal"
      by (simp add: prems(5))
    then have "val[xb - yb] \<noteq> UndefVal"
      by (simp add: prems)
    then have yValue: "[m,p] \<turnstile> y \<mapsto> xaa"
      by (simp add: prems)
    then have zValue: "[m,p] \<turnstile> z \<mapsto> yaa"
      by (simp add: prems)
    then have "[m,p] \<turnstile> y \<mapsto> xb"
      by (simp add: prems)
    then have "[m,p] \<turnstile> z \<mapsto> yb"
      by (simp add: prems)
    then have "wf_value (IntVal b 0)"
      by (simp add: prems(11))
    obtain vx where xa: "xa = IntVal 64 vx"
      using assms(1) assms(2) lower_stamp2 xa by blast
      (* by (metis Value.collapse(1) bin_eval.simps(15) defined_eval_is_intval evalDet prems(1) prems(2) xa) *)
    obtain vy where hello1: "xaa = IntVal 64 vy"
      by (meson assms(3) assms(4) lower_stamp2 yValue)
    obtain vz where hello2: "yaa = IntVal 64 vz"
      using assms(5) assms(6) lower_stamp2 zValue by blast
    have wf_rhs1:"[m,p] \<turnstile> exp[y-z] \<mapsto> val[xaa - yaa]"
      using yValue zValue
      by (metis bin_eval.simps(2) evalDet prems(10) prems(6) prems(9) unfold_binary)
    then have "val[xaa - yaa] = new_int 64 (vy - vz)"
      using hello1 hello2 prems by auto
    then obtain vdiff where hello3: "val[xaa-yaa] = IntVal 64 vdiff"
      by simp
    then have "val[xa < (xaa - yaa)] \<noteq> UndefVal"
      using xa apply auto
      by (metis Value.distinct(1) bool_to_val.simps(1) bool_to_val.simps(2))
    then have wf_rhs:"[m,p] \<turnstile> exp[x < (y-z)] \<mapsto> val[xa < (xaa - yaa)]"
      apply (auto simp add: unfold_binary)
      by (metis intval_less_than.simps(6) prems(1) yValue zValue)
    then have "[m,p] \<turnstile> exp[x < (y-z)] \<mapsto> val[xa |<| ya]"
    proof (cases "val_to_bool(val[xaa |<| yaa])")
      case True
      then have "\<not>isValPositive(val[xaa - yaa])"
        using lower_stamp and below_sub_inv apply auto
        using assms(3) assms(4) assms(5) assms(6) prems(7) prems(8) by auto
      then have "val_to_bool(val[xa |<| ya]) = False"
        using True assms(7) prems(4) xa by auto
      then have "val_to_bool(val[xa < (xaa - yaa)]) = False"
        by (simp add: \<open>\<not> isValPositive (intval_sub (xaa::Value) (yaa::Value))\<close> pos_less_neg xaPos)
      then have "val[xa < (xaa - yaa)] = IntVal 32 0"
        by (simp add: \<open>\<not> isValPositive (intval_sub (xaa::Value) (yaa::Value))\<close> pos_less_neg xaPos)
      then have "val[xa |<| ya] = IntVal 32 0"
        using True assms(7) prems(4) xa by force
      then show ?thesis
        using \<open>intval_less_than (xa::Value) (intval_sub (xaa::Value) (yaa::Value)) = IntVal (32::nat) (0::64 word)\<close> wf_rhs by auto 
    next
      case False
      then have "isValPositive(val[xaa-yaa])"
        using assms(3) assms(4) assms(5) assms(6) below_sub lower_stamp yValue zValue by blast
      then have "val[xa |<| ya] = val[xa |<| (xaa-yaa)]"
        by (metis False evalDet prems(4) wf_rhs1)
      then have "val[xa |<| (xaa - yaa)] = val[xa < (xaa - yaa)]"
        using assms val_below_eq_less xaPos
        using \<open>isValPositive (intval_sub (xaa::Value) (yaa::Value))\<close> by blast
      then show ?thesis
        by (simp add: \<open>intval_below (xa::Value) (ya::Value) = intval_below xa (intval_sub (xaa::Value) (yaa::Value))\<close> wf_rhs)
    qed
    then show ?thesis
      by auto
  qed
  done

value"exp[False]"

(* optimization test1: "(x |<| ((y |<| z)? const (IntVal 32 0) : (y - z))) \<longmapsto> x < (y-z) *)
                     (* when ((isStampPos (stamp_expr x)) \<and> (wf_stamp x) \<and> *)
                            (* (isStampPos (stamp_expr y)) \<and> (wf_stamp y) \<and> *)
                            (* (isStampPos (stamp_expr z)) \<and> (wf_stamp z))" *)
  (* apply auto *)
  (* (* by (metis Value.distinct(1) below_zero intval_below.simps(2)) *) *)
  (* sorry *)
