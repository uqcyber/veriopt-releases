theory IntegerEqualsPhase
  imports Common Proofs.StampEvalThms
begin

phase IntegerEqualsPhase
  terminating size
begin

(* ----------------Word level---------------- *)

lemma bin_addition_equality: "((x+y) = (x+z)) \<longleftrightarrow> (y = z)" for x y z::int64
  by simp

lemma bin_subtraction_equality: "((x-y) = (x-z)) \<longleftrightarrow> (y = z)" for x y z::int64
  by auto

lemma bin_add_zero_equality: "(x = (x + y)) \<longleftrightarrow> y = 0" for x y::int64
  by simp

lemma bin_sub_zero_equality: "(x = (x-y)) \<longleftrightarrow> y = 0" for x y::int64
  by simp

lemma bin_add_commulative: "(x+y) = (y+x)" for x y z::int64
  by simp

(* ----------------Value level---------------- *)

lemma val_addition_equality: 
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "z = new_int n vz"
  assumes "val[(x + y) eq (x + z)] \<noteq> UndefVal"
  shows "val[(x + y) eq (x + z)] = val[y eq z]"
proof -
    have unfold_lhs: "val[x+z] = IntVal n (take_bit n (vx + vz))"
      by (simp add: assms(1) assms(3))
    show ?thesis
    proof (cases "val_to_bool (val[(x + y) eq (x + z)])")
      case True
      have "take_bit n (vx + vy) = take_bit n (vx + vz)" 
        using assms True apply auto
        by (metis (full_types) bool_to_val.simps(2) val_to_bool.simps(1))
      then have eq_word: "take_bit n vy = take_bit n vz"
        by (metis (no_types, opaque_lifting) ValueThms.take_bit_dist_subR add.right_neutral 
            diff_conv_add_uminus diff_diff_eq2 diff_self verit_minus_simplify(3)) 
      then show ?thesis using True
        using eq_word unfold_lhs assms(2) assms(3) by auto  
    next
      case False
      have noneq_sumword: "take_bit n (vx + vy) \<noteq> take_bit n (vx + vz)"
        using assms False by auto
      then have noneq_word:  "take_bit n vy \<noteq> take_bit n vz"
        by (metis ValueThms.take_bit_dist_addR)
      then show ?thesis using False
        by (simp add: noneq_sumword assms(1) assms(2) assms(3)) 
    qed
  qed

lemma val_subtraction_equality:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "z = new_int n vz"
  assumes "val[(x - y) eq (x - z)] \<noteq> UndefVal"
  shows "val[(x - y) eq (x - z)] = val[y eq z]"
proof -
  have unfold_lhs: "val[x-z] = IntVal n (take_bit n (vx - vz))"
    by (simp add: assms(1) assms(3))
  then show ?thesis
    by (smt (verit) ValueThms.take_bit_dist_subL ValueThms.take_bit_dist_subR add_diff_cancel_left' 
        assms(1) assms(2) assms(3) bool_to_val_bin.elims diff_add_cancel intval_equals.simps(1) 
        intval_sub.simps(1) intval_word.simps new_int.elims new_int_bin.elims new_int_take_bits) 
  qed

lemma val_add_zero_equality:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "val[x eq (x + y)] \<noteq> UndefVal"
  shows "val[x eq (x + y)] = val[y eq (new_int n 0)]" 
  using assms bin_add_zero_equality apply auto
  by (smt (verit, ccfv_threshold) ValueThms.take_bit_dist_addR bin_add_zero_equality 
      minus_add_cancel take_bit_of_0)

lemma val_sub_zero_equality:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "val[x eq (x - y)] \<noteq> UndefVal"
  shows "val[x eq (x - y)] = val[y eq (new_int n 0)]"
proof (cases "val_to_bool val[x eq (x - y)]")
  case True
  then have "take_bit n vx = take_bit n (vx - vy)"
    using assms apply auto
    by (metis (full_types) bool_to_val.simps(2) val_to_bool.simps(1))
  moreover have "take_bit n vx = take_bit n (vx - 0)"
    by simp
  ultimately have "take_bit n (vx - vy) = take_bit n (vx - 0)"
    by metis
  then have "take_bit n vy = 0"
    by (metis (no_types, opaque_lifting) ValueThms.take_bit_dist_subR add.inverse_inverse 
        add.left_commute add.right_inverse add.right_neutral take_bit_of_0 uminus_add_conv_diff)
  then have "val_to_bool val[y eq (new_int n 0)]"
    by (simp add: assms(2))
  then show ?thesis using True apply auto
    by (simp add: \<open>take_bit (n::nat) (vy::64 word) = (0::64 word)\<close> assms(1) assms(2))
next
  case False
  have "val[x eq (x - y)] = IntVal 32 0"
    using assms False intval_equals_result by fastforce 
  then have "take_bit n vx \<noteq> take_bit n (vx - vy)"
    using assms by auto
  moreover have "take_bit n vx = take_bit n (vx - 0)"
    by simp 
  ultimately have "take_bit n vy \<noteq> 0"
    by (metis ValueThms.take_bit_dist_subR)
  then have "val[y eq (new_int n 0)] = IntVal 32 0"
    using assms(2) by auto
  then show ?thesis 
    using \<open>val[x eq (x - y)] = IntVal 32 0\<close> by auto
qed


lemma val_add_commulative:
  assumes "x = new_int n vx"
  assumes "y = new_int n vy"
  assumes "val[x + y] \<noteq> UndefVal"
  shows "val[x + y] = val[y + x]"
  by (simp add: intval_add_sym)


(* ----------------Expression level ---------------- *)

lemma new_intZero [simp]: 
  assumes "1 \<le> b"
  assumes "b \<le> 64"
  shows "new_int b 0 = IntVal b 0"
  unfolding new_int.simps by simp

lemma wfZero [simp]: 
  assumes "1 \<le> b"
  assumes "b \<le> 64"
  shows "wf_value (IntVal b 0)"
  unfolding wf_value_def stamp_expr.simps(3) valid_value.simps apply auto
  using assms(1) apply auto[1]
  apply (simp add: assms(2))
  by (metis ValueThms.upper_bounds_equiv assms(1) gr0I less_numeral_extra(1) 
      linorder_not_less not_exp_less_eq_0_int)

lemma exp_cumulative_addition: 
  assumes "wf_stamp x" 
  assumes "wf_stamp y"
  shows "exp[x + y] \<ge> exp[y + x]"
  apply auto
  subgoal premises prems for m p xa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(1) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using prems(2) by auto
    have "val[xa + ya] \<noteq> UndefVal"
      by (metis evalDet prems(1) prems(2) prems(3) xa ya)
    have "[m,p] \<turnstile> exp[y + x] \<mapsto> val[xa + ya]"
      using \<open>intval_add (xa::Value) (ya::Value) \<noteq> UndefVal\<close> intval_add_sym xa ya by auto
    then show ?thesis
      by (metis evalDet prems(1) prems(2) xa ya) 
  qed
  done

lemma exp_cumulative_equal:
  shows "exp[x eq y] \<ge> exp[y eq x]"
  apply auto
  subgoal premises prems for m p xa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(1) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using prems(2) by auto
    have "val[xa eq ya] \<noteq> UndefVal"
      by (metis evalDet prems(1) prems(2) prems(3) xa ya)
    have "val[ya eq xa] \<noteq> UndefVal"
      by (smt (z3) \<open>intval_equals (xa::Value) (ya::Value) \<noteq> UndefVal\<close> bool_to_val_bin.simps 
          intval_equals.elims intval_equals.simps(1))
    then have "[m,p] \<turnstile> exp[y eq x] \<mapsto> val[ya eq xa]"
      using xa ya by auto
    then have "val[ya eq xa] = val[xa eq ya]"
      by (smt (verit) BinaryExprE bool_to_val_bin.simps defined_eval_is_intval evalDet 
          intval_equals.simps(1) is_IntVal_def xa ya)
    then have "[m,p] \<turnstile> exp[y eq x] \<mapsto> val[xa eq ya]"
      using \<open>intval_equals (xa::Value) (ya::Value) \<noteq> UndefVal\<close> xa ya by auto
    then show ?thesis
      by (metis evalDet prems(1) prems(2) xa ya) 
  qed
  done

lemma exp_addition_equality:
  shows "exp[(x+y) eq (x+z)] \<ge> exp[(y eq z)]"
  apply auto
  subgoal premises prem for m p xa ya xb yb
  proof -
  have "val[(xa + ya) eq (xb + yb)] \<noteq> UndefVal"
    by (simp add: prem(1))
  obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
    using prem(2) by auto
  obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
    using prem(3) by auto
  have l_add: "val[xa + ya] \<noteq> UndefVal"
    by (metis evalDet prem(2) prem(3) prem(4) xa ya)
  obtain xb where xb: "[m,p] \<turnstile> x \<mapsto> xb"
    using prem(2) by auto
  obtain yb where yb: "[m,p] \<turnstile> z \<mapsto> yb"
    using prem(6) by auto
  have r_add: "val[xb + yb] \<noteq> UndefVal"
    by (metis evalDet prem(5) prem(6) prem(7) xb yb)
  have "xa = xb"
    using evalDet xa xb by auto
  obtain xn xv where o1: "xa = IntVal xn xv"
    by (metis evaltree_not_undef intval_add.simps(3) intval_add.simps(4) intval_add.simps(5) 
        intval_logic_negation.cases l_add xa)
  then have "xa = new_int xn xv"
    using eval_unused_bits_zero xa by auto
  obtain yn yv where o2: "ya = IntVal yn yv"
    by (metis evaltree_not_undef intval_add.simps(7) intval_add.simps(8) intval_add.simps(9) 
        intval_logic_negation.cases l_add ya)
  then have "ya = new_int yn yv"
    using eval_unused_bits_zero ya by auto
  obtain zn zv where o3: "yb = IntVal zn zv"
    by (metis evaltree_not_undef intval_add.simps(5) intval_add.simps(7) intval_add.simps(8) 
        intval_add_sym intval_logic_negation.cases r_add yb)
  then have "yb = new_int zn zv"
    using eval_unused_bits_zero yb by auto
  have "xn = yn" using l_add o1 o2 apply auto
    by presburger
  moreover have "xn = zn" using \<open>xa = xb\<close> r_add o1 o3 apply auto
    by presburger
  ultimately have "yn = zn" 
    by auto
  then have eq_value_level: "val[(xa + ya) eq (xb + yb)] = val[ya eq yb]" 
    using prem(1) \<open>xn=yn\<close> \<open>xa = new_int xn xv\<close> \<open>ya = new_int yn yv\<close> 
          \<open>yb = new_int zn zv\<close> \<open>xa = xb\<close> val_addition_equality
    by (metis evalDet prem(2) prem(3) prem(5) prem(6) xb ya yb)
  then have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[ya eq yb]"
    by (metis \<open>(xa::Value) = (xb::Value)\<close> bin_eval.simps(13) evalDet prem(1) prem(2) prem(3) 
        prem(5) prem(6) unfold_binary xb ya yb)
  moreover have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[(xa + ya) eq (xb + yb)]"
    by (simp add: \<open>[m,p] \<turnstile> exp[y eq z] \<mapsto> val[ya eq yb]\<close> eq_value_level)
  ultimately show ?thesis apply auto
    by (metis \<open>(xa::Value) = (xb::Value)\<close> 
        \<open>[m::nat \<Rightarrow> Value,p::Value list] \<turnstile> BinaryExpr BinIntegerEquals (y::IRExpr) (z::IRExpr) \<mapsto> intval_equals (ya::Value) (yb::Value)\<close> 
        evalDet prem(2) prem(3) prem(5) prem(6) xa ya yb)
qed
  done

lemma exp_subtraction_equality:
  shows "exp[(x-y) eq (x-z)] \<ge> exp[(y eq z)]"
  apply auto
  subgoal premises prem for m p xa ya xb yb
proof -
  obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
    using prem(2) by auto
  obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
    using prem(3) by auto
  have l_add: "val[xa - ya] \<noteq> UndefVal"
    by (metis evalDet prem(2) prem(3) prem(4) xa ya)
  obtain xb where xb: "[m,p] \<turnstile> x \<mapsto> xb"
    using prem(2) by auto
  obtain yb where yb: "[m,p] \<turnstile> z \<mapsto> yb"
    using prem(6) by auto
  have r_add: "val[xb - yb] \<noteq> UndefVal"
    by (metis evalDet prem(5) prem(6) prem(7) xb yb)
  have "xa = xb"
    using evalDet xa xb by auto
  obtain xn xv where o1: "xa = IntVal xn xv"
    by (metis \<open>(xa::Value) = (xb::Value)\<close> intval_is_null.cases intval_sub.simps(2) 
        intval_sub.simps(3) intval_sub.simps(4) intval_sub.simps(5) r_add)
  then have "xa = new_int xn xv"
    using eval_unused_bits_zero xa by auto
  obtain yn yv where o2: "ya = IntVal yn yv"
    by (metis intval_logic_negation.cases intval_sub.simps(6) intval_sub.simps(7) 
        intval_sub.simps(8) intval_sub.simps(9) l_add)
  then have "ya = new_int yn yv"
    using eval_unused_bits_zero ya by auto
  obtain zn zv where o3: "yb = IntVal zn zv"
    by (metis intval_logic_negation.cases intval_sub.simps(6) intval_sub.simps(7) 
        intval_sub.simps(8) intval_sub.simps(9) r_add)
  then have "yb = new_int zn zv"
    using eval_unused_bits_zero yb by auto
  have "xn = yn" using l_add o1 o2 apply auto
    by presburger
  moreover have "xn = zn" using \<open>xa = xb\<close> r_add o1 o3 apply auto
    by presburger
  ultimately have "yn = zn" 
    by auto
  then have eq_value_level: "val[(xa - ya) eq (xb - yb)] = val[ya eq yb]" 
    using prem(1) \<open>xn=yn\<close> \<open>xa = new_int xn xv\<close> \<open>ya = new_int yn yv\<close> 
          \<open>yb = new_int zn zv\<close> \<open>xa = xb\<close>
    by (metis evalDet prem(2) prem(3) prem(5) prem(6) val_subtraction_equality xb ya yb)
  then have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[ya eq yb]"
    by (metis \<open>(xa::Value) = (xb::Value)\<close> bin_eval.simps(13) evalDet prem(1) prem(2) prem(3) 
        prem(5) prem(6) unfold_binary xb ya yb)
  moreover have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[(xa - ya) eq (xb - yb)]"
    by (simp add: \<open>[m,p] \<turnstile> exp[y eq z] \<mapsto> val[ya eq yb]\<close> eq_value_level)
  ultimately show ?thesis apply auto
    by (metis \<open>(xa::Value) = (xb::Value)\<close> 
        \<open>[m::nat \<Rightarrow> Value,p::Value list] \<turnstile> BinaryExpr BinIntegerEquals (y::IRExpr) (z::IRExpr) \<mapsto> intval_equals (ya::Value) (yb::Value)\<close> 
        evalDet prem(2) prem(3) prem(5) prem(6) xa ya yb)
qed
  done

lemma exp_add_zero_equality:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[x eq (x+y)] \<ge> exp[y eq const (IntVal b 0)]"
  apply auto
  subgoal premises prems for m p xa xaa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(1) by auto
    have "val[xa eq (xaa + ya)] \<noteq> UndefVal"
      using evalDet prems(1) prems(2) xa by blast
    have "xa = xaa"
      using evalDet prems(3) xa by auto
    obtain ya where y: "[m,p] \<turnstile> y \<mapsto> ya"
      using prems(4) by auto
    have "val[xaa + ya] \<noteq> UndefVal"
      using evalDet prems(4) prems(5) y by blast
    obtain xn xv where "xa = IntVal xn xv"
      by (smt (z3) \<open>(xa::Value) = (xaa::Value)\<close> intval_add.elims prems(5))
    then have "xa = new_int xn xv"
      using eval_unused_bits_zero xa by auto
    obtain yn yv where ya:"ya = IntVal yn yv"
      by (metis \<open>intval_add (xaa::Value) (ya::Value) \<noteq> UndefVal\<close> array_length.cases 
          intval_add.simps(2) intval_add.simps(7) intval_add.simps(8) intval_add.simps(9) 
          intval_add_sym)
    then have "ya = new_int yn yv"
      using eval_unused_bits_zero y by auto
    have "xn = yn"
      by (metis \<open>(xa::Value) = (xaa::Value)\<close> \<open>(xa::Value) = IntVal (xn::nat) (xv::64 word)\<close> 
          \<open>(ya::Value) = IntVal (yn::nat) (yv::64 word)\<close> 
          \<open>intval_add (xaa::Value) (ya::Value) \<noteq> UndefVal\<close> intval_add.simps(1))
    have "wf_value (IntVal b 0)" 
      using wfZero assms(3) assms(4) by auto
    moreover have "yn = b" using calculation y ya assms
      by (metis valid_int_same_bits wf_stamp_def) 
    ultimately have "val[ya eq (IntVal b 0)] \<noteq> UndefVal"
      using y ya assms apply (auto)
      by (metis Value.distinct(1) bool_to_val.simps(1) bool_to_val.simps(2))
    then have "val[ya eq (new_int b 0)] \<noteq> UndefVal"
      using new_intZero by auto
    then have "val[xa eq (xaa + ya)] = val[ya eq (new_int b 0)]"
      by (metis \<open>(xa::Value) = (xaa::Value)\<close> \<open>(xa::Value) = new_int (xn::nat) (xv::64 word)\<close> 
          \<open>(xn::nat) = (yn::nat)\<close> \<open>(ya::Value) = new_int (yn::nat) (yv::64 word)\<close> 
          \<open>(yn::nat) = (b::nat)\<close> evalDet prems(1) prems(2) prems(4) val_add_zero_equality xa y)
    then have eq_value_level: "val[xa eq (xaa + ya)] = val[ya eq (IntVal b 0)]"
      using new_intZero y ya by auto
    have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[ya eq (IntVal b 0)]"
      using \<open>intval_equals (ya::Value) (IntVal (b::nat) (0::64 word)) \<noteq> UndefVal\<close> 
            \<open>wf_value (IntVal (b::nat) (0::64 word))\<close> y by auto
    then have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[xa eq (xaa + ya)]"
      using eq_value_level by auto
    then show ?thesis
      by (metis \<open>(xa::Value) = (xaa::Value)\<close> evalDet prems(1) prems(3) prems(4) y)
  qed
  done

lemma exp_add_zero_equality_flipped:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[(x+y) eq x] \<ge> exp[y eq const (IntVal b 0)]"
proof -
  have "exp[x eq (x+y)] \<ge> exp[(x+y) eq x]"
    using exp_cumulative_equal by auto
  then have "exp[x eq (x+y)] \<ge> exp[y eq const (IntVal b 0)]"
    using assms(1) assms(2) assms(3) assms(4) exp_add_zero_equality by blast
  then show ?thesis
    using exp_cumulative_equal order.trans by blast
qed

lemma exp_sub_zero_equality:
  assumes "stamp_expr y = IntegerStamp b lo hi"
  assumes "wf_stamp y"
  assumes "1 \<le> b" and "b \<le> 64"
  shows "exp[x eq (x-y)] \<ge> exp[y eq const (IntVal b 0)]"
  apply auto
  subgoal premises prems for m p xa xaa ya
  proof - 
    obtain xa where x: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(1) by simp
    then have "val[xa eq (xaa - ya)] \<noteq> UndefVal"
      using evalDet prems(1) prems(2) by blast
    have "xaa = xa"
      using evalDet prems(3) x by auto
    obtain ya where y: "[m,p] \<turnstile> y \<mapsto> ya"
      using prems(4) by auto
    then have "val[xaa - ya] \<noteq> UndefVal"
      using evalDet prems(4) prems(5) by blast
    obtain xn xv where xa: "xa = IntVal xn xv"
      by (metis \<open>(xaa::Value) = (xa::Value)\<close> intval_logic_negation.elims intval_sub.simps(2) 
          intval_sub.simps(3) intval_sub.simps(4) intval_sub.simps(5) prems(5))
    then have "xa = new_int xn xv"
      using eval_unused_bits_zero x by auto
    obtain yn yv where ya: "ya = IntVal yn yv"
      by (metis evalDet intval_logic_negation.cases intval_sub.simps(6) intval_sub.simps(7) 
          intval_sub.simps(8) intval_sub.simps(9) prems(4) prems(5) y)
    then have "ya = new_int yn yv"
      using eval_unused_bits_zero y by auto
    have "wf_value (IntVal b 0)"
      using wfZero assms by auto
    moreover have "yn = b"
      using calculation assms y
      by (metis valid_int_same_bits wf_stamp_def ya)
    ultimately have "val[ya eq (IntVal b 0)] \<noteq> UndefVal"
      using assms ya apply auto
      by (metis Value.distinct(1) bool_to_val.simps(1) bool_to_val.simps(2))
    then have "val[ya eq (new_int b 0)] \<noteq> UndefVal"
      using new_intZero by auto
    then have "val[xa eq (xaa - ya)] = val[ya eq (new_int b 0)]"
      by (metis \<open>xa = new_int xn xv\<close> \<open>xaa = xa\<close> \<open>(ya::Value) = new_int (yn::nat) (yv::64 word)\<close> 
          \<open>(yn::nat) = (b::nat)\<close> \<open>intval_sub (xaa::Value) (ya::Value) \<noteq> UndefVal\<close> evalDet 
          intval_sub.simps(1) new_int.simps new_int_bin.elims prems(1) prems(2) prems(3) prems(4) 
          take_bit_of_0 val_sub_zero_equality y)
    then have eq_value_level: "val[xa eq (xaa - ya)] = val[ya eq (new_int b 0)]"
      by auto
    have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[ya eq (IntVal b 0)]"
      using \<open>intval_equals (ya::Value) (IntVal (b::nat) (0::64 word)) \<noteq> UndefVal\<close> 
            \<open>wf_value (IntVal (b::nat) (0::64 word))\<close> y by auto
    then have "[m,p] \<turnstile> exp[y eq const (IntVal b 0)] \<mapsto> val[xa eq (xaa - ya)]"
      using eq_value_level by auto
    then show ?thesis
      by (metis \<open>(xaa::Value) = (xa::Value)\<close> evalDet prems(1) prems(3) prems(4) y) 
    qed
    done

(* ----------------Optimizations ---------------- *)

lemma canonical_size_binop_equality: "Canonicalization.size (BinaryExpr BinIntegerEquals y z)
    < Suc (Suc (Canonicalization.size (BinaryExpr op x y) + Canonicalization.size (BinaryExpr op x z)))"
  by (cases z; cases y; auto)

lemma canonical_size_binop_equality_swapped: "Canonicalization.size (BinaryExpr BinIntegerEquals y z)
    < Suc (Suc (Canonicalization.size (BinaryExpr op x y) + Canonicalization.size (BinaryExpr op z x)))"
  by (cases z; cases y; cases x; auto)

lemma canonical_size_add_zero_equality_swapped: "Suc (Suc (Canonicalization.size y))
    < Canonicalization.size (BinaryExpr BinIntegerEquals (BinaryExpr BinAdd x y) x)"
  by (cases x; cases y; auto)


optimization AdditionEquality: "exp[(x+y) eq (x+z)] \<longmapsto> exp[(y eq z)]"
  using canonical_size_binop_equality apply simp
  using exp_addition_equality by blast

optimization AdditionEquality2: "exp[(x+y) eq (z+x)] \<longmapsto> exp[(y eq z)] 
                                                when wf_stamp x \<and> wf_stamp y \<and> wf_stamp z"
  using canonical_size_binop_equality_swapped apply simp
  using exp_addition_equality exp_cumulative_addition
  by (meson dual_order.trans mono_binary) 

optimization SubtractionEquality: "exp[(x-y) eq (x-z)] \<longmapsto> exp[(y eq z)]"
  using canonical_size_binop_equality apply simp
  using exp_subtraction_equality by blast

optimization EqualAddZero: "exp[x eq (x + y)] \<longmapsto> exp[y eq (const (IntVal b 0))] 
                          when wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  using exp_add_zero_equality by simp

optimization EqualAddZero_Flipped: "exp[(x + y) eq x] \<longmapsto> exp[y eq (const (IntVal b 0))] 
                          when wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  using canonical_size_add_zero_equality_swapped apply simp
  using exp_add_zero_equality_flipped by simp

optimization EqualSubZero: "exp[x eq (x - y)] \<longmapsto> exp[y eq (const (IntVal b 0))] 
                          when wf_stamp y \<and> stamp_expr y = IntegerStamp b lo hi \<and> (1 \<le> b) \<and> (b \<le> 64)"
  using exp_sub_zero_equality by simp


(* optimization EqualNot: "exp[x eq (~ x)] \<longmapsto> exp[ *)





















