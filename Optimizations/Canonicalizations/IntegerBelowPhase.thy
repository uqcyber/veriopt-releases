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
  
(* Value level *)

fun isValPositive:: "Value \<Rightarrow> bool" where
"isValPositive (IntVal n v) = ((\<not>bit v (n-Suc(0)))\<and>(take_bit (n-1) v = v))"
(* "isValPositive (IntVal n v) = ((sint (signed_take_bit (n-Suc 0) v) \<ge> 0)\<and>(take_bit (n-1) v = v))" *)

lemma neg_sub:
  shows "(val_to_bool val[y < z]) \<Longrightarrow> val[y-z] = IntVal 32 0"
  oops

lemma
  assumes "isValPositive x" and "\<not>isValPositive y"
  shows "val_to_bool(val[x < y]) = False"
  using assms apply auto
  oops

lemma verify_isValPositive: 
  assumes "isValPositive (new_int 64 v)"
  shows "sint(v) \<ge> 0"
  apply (induction v)
  apply auto
  sorry

lemma below_sub:
  assumes "isValPositive y"
  assumes "isValPositive z"
  shows "(\<not>val_to_bool (val[y |<| z])) \<Longrightarrow> isValPositive(val[y-z])"
  sorry

lemma below_sub_inv:
  assumes "isValPositive y"
  assumes "isValPositive z"
  shows "(val_to_bool (val[y |<| z])) \<Longrightarrow> \<not>isValPositive(val[y-z])"
  sorry

(* Should be move to Less than phase *)
lemma pos_less_neg: 
  assumes "isValPositive x"
  assumes "\<not>isValPositive y"
  shows "val[x < y] = IntVal 32 0"
  sorry

lemma val_below_eq_less: 
  assumes "isValPositive x" 
  assumes "isValPositive y" 
  shows "val[x |<| y] = val[x < y]"
  using assms verify_isValPositive bin_below_eq_less
  by (metis Value.distinct(1) intval_less_than.simps(2) intval_less_than.simps(6) neg_le_0_iff_le not_one_le_zero pos_less_neg signed_minus_1 verit_minus_simplify(4))

lemma below_zero: 
  shows "val[(IntVal b v) |<| (IntVal b 0)] = IntVal 32 0"
  by auto

lemma val_below_less:
  assumes "x = IntVal 64 vx" and "y = IntVal 64 vy" and "z = IntVal 64 vz"
  assumes "isValPositive x"
  assumes "isValPositive y"
  assumes "isValPositive z"
  shows "val[(x |<| ((y |<| z)? (IntVal 64 0) : (y - z)))] = val[x < (y-z)]"
proof(cases "val_to_bool (val[y |<| z])")
  case True
  then have unfoldCond: "val[(x |<| ((y |<| z)? 
                         (IntVal 64 0) : (y - z)))] = val[x |<| (IntVal 64 0)]"
    by simp
  then have t1: "val[x |<| (IntVal 64 0)] = IntVal 32 0"
    using below_zero assms by auto  
  then have "\<not>isValPositive(val[y-z])"
    by (simp add: True assms(5) assms(6) below_sub_inv)
  then have "val[x < (y-z)] = IntVal 32 0"
    using assms pos_less_neg by blast
  then show ?thesis
    by (simp add: True t1)
next
  case False
  then have unfoldCond: "val[(x |<| ((y |<| z)? (IntVal 64 0) : (y - z)))] = val[x |<| (y - z)]"
    by simp
  then have "isValPositive(val[y-z])"
    by (simp add: False assms(5) assms(6) below_sub)
  then have "val[x |<| (y - z)] = val[x < (y-z)]"
    by (simp add: assms(4) val_below_eq_less)
  then show ?thesis
    using unfoldCond by auto
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
  sorry

lemma lower_stamp2:
  assumes "isStampPos (stamp_expr x)" 
  assumes "wf_stamp x"
  assumes "[m,p] \<turnstile> x \<mapsto> xv"
  shows "\<exists>v. xv = IntVal 64 v"
  sorry

lemma exp_below_less: 
  assumes "isStampPos (stamp_expr x)" and "wf_stamp x"
  assumes "isStampPos (stamp_expr y)" and "wf_stamp y"
  assumes "isStampPos (stamp_expr z)" and "wf_stamp z"
  assumes "b = 64"
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
