subsection \<open>LeftShiftNode Phase\<close>

theory LeftShiftPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase LeftShiftNode
  terminating size
begin

lemma "x \<noteq> 0 \<Longrightarrow> x << 64 = 0" for x::int64
  unfolding shiftl_def by auto

lemma "x \<noteq> 0 \<and> 64 \<le> a \<Longrightarrow> x << a = 0" for x::int64
  unfolding shiftl_def by auto

lemma bin_LeftShiftBecomesZero: "(64 \<le> y + z) \<Longrightarrow> (x << y) << z = 0" for x::int64
  unfolding shiftl_def by auto

lemma bin_combine_left_shift: "(x << y) << z = x << (y+z)" for x::int64
  unfolding shiftl_def apply auto
  by (metis add.commute)

(* Value level proofs *)

lemma val_EliminateRHS:
  assumes "x = new_int bx vx"
  assumes "1 \<le> bx" 
  assumes "bx \<le> 64"
  assumes "y = IntVal by vy"
  assumes "(shift_amount bx vy) = 0"
  assumes "val[x << y] \<noteq> UndefVal"
shows "val[x << y] = x"
proof -
  have "vx << (0::nat) = vx"
    unfolding shiftl_def by simp
  obtain ivX where x: "x = IntVal bx ivX"
    by (simp add: assms(1))
  have "val[x << y] = val[x << (IntVal bx 0)]"
    using assms by auto
  then have "val[x << y] = new_int bx (ivX << (0::nat))"
    by (simp add: x)
  moreover have "ivX << (0::nat) = ivX"
    unfolding shiftl_def by simp
  ultimately have "val[x << y] = new_int bx ivX"
    by simp
  have "ivX = take_bit bx vx"
    using assms(1) x by auto
  show ?thesis
    using \<open>(ivX::64 word) = take_bit (bx::nat) (vx::64 word)\<close> 
      \<open>intval_left_shift (x::Value) (y::Value) = new_int (bx::nat) (ivX::64 word)\<close> assms(1) by auto
qed

lemma left_shift_to_zero_64:
  assumes "x = new_int bx vx"
  assumes "bx \<le> a" 
  assumes "bx = 64"
  shows "take_bit bx (vx << a) = 0"
  unfolding shiftl_def using assms by auto

lemma nested_take_bit_left_shift_64:
  assumes "x = new_int bx vx"
  assumes "bx = 64"
  shows "take_bit bx ((take_bit bx (vx << a)) << b) = take_bit bx ((vx << a) << b)"
  unfolding shiftl_def using assms
  by (simp add: push_bit_take_bit)

lemma val_left_shift_becomes_zero_64:
  assumes "x = new_int bx vx"
  assumes "y = IntVal by vy"
  assumes "z = IntVal bz vz"
  assumes "bx = 64"
  assumes "bx \<le> (shift_amount bx vy) + (shift_amount bx vz)"
  assumes "val[(x << y) << z] \<noteq> UndefVal"
  shows "val[(x << y) << z] = IntVal bx 0"
proof -
  obtain ivX where x: "x = IntVal bx ivX"
    by (simp add: assms(1))
  have unfoldXY: "val[x << y] = new_int bx (ivX << shift_amount bx vy)"
    using assms(2) x by auto
  then obtain xy where xy: "xy = new_int bx (ivX << shift_amount bx vy)"
    by auto
  then have "xy = IntVal bx (take_bit bx (ivX << shift_amount bx vy))"
    by simp
  then have 1: "val[xy << z] = new_int bx 
                        ((take_bit bx (ivX << shift_amount bx vy)) << shift_amount bx vz)"
    using assms(3) by auto
  then have 2: "\<dots> = IntVal bx (take_bit bx ((take_bit bx (ivX << shift_amount bx vy)) << shift_amount bx vz))"
    using assms(4) by auto
  then have 3: "... = IntVal bx (take_bit bx ((ivX << shift_amount bx vy) << shift_amount bx vz))"
    using nested_take_bit_left_shift_64 assms(4) assms(5) bin_LeftShiftBecomesZero by presburger 
  then have 4: "... = IntVal bx (take_bit bx (ivX << (shift_amount bx vy + shift_amount bx vz)))"
    by (simp add: bin_combine_left_shift)
  then have 5: "... = IntVal bx 0"
    using left_shift_to_zero_64 assms(5)
    by (simp add: assms(4))
  then show ?thesis
    using "1" "3" "4" unfoldXY xy by force
qed

lemma left_shift_to_zero_less64:
  assumes "x = new_int bx vx"
  assumes "bx \<le> a" 
  assumes "1 \<le> bx" and "bx < 64"
  shows "take_bit bx (vx << a) = 0"
  unfolding shiftl_def using assms
  by (simp add: take_bit_push_bit)

lemma nested_take_bit_left_shift_less64:
  assumes "x = new_int bx vx"
  assumes "1 \<le> bx" and "bx < 64"
  shows "take_bit bx ((take_bit bx (vx << a)) << b) = take_bit bx ((vx << a) << b)"
  unfolding shiftl_def using assms
  by (simp add: push_bit_take_bit)

lemma val_left_shift_becomes_zero_less64:
  assumes "x = new_int bx vx"
  assumes "y = IntVal by vy"
  assumes "z = IntVal bz vz"
  assumes "1 \<le> bx" and "bx < 64"
  assumes "bx \<le> (shift_amount bx vy) + (shift_amount bx vz)"
  assumes "val[(x << y) << z] \<noteq> UndefVal"
  shows "val[(x << y) << z] = IntVal bx 0"
proof -
  obtain ivX where x: "x = IntVal bx ivX"
    by (simp add: assms(1))
  have unfoldXY: "val[x << y] = new_int bx (ivX << shift_amount bx vy)"
    using assms(2) x by auto
  then obtain xy where xy: "xy = new_int bx (ivX << shift_amount bx vy)"
    by auto
  then have "xy = IntVal bx (take_bit bx (ivX << shift_amount bx vy))"
    by simp
  then have 1: "val[xy << z] = new_int bx 
                        ((take_bit bx (ivX << shift_amount bx vy)) << shift_amount bx vz)"
    using assms(3) by auto
  then have 2: "\<dots> = IntVal bx (take_bit bx ((take_bit bx (ivX << shift_amount bx vy)) << shift_amount bx vz))"
    using assms(4) by auto
  then have 3: "... = IntVal bx (take_bit bx ((ivX << shift_amount bx vy) << shift_amount bx vz))"
    using nested_take_bit_left_shift_less64 assms(4) assms(5)
    using assms(6) bin_combine_left_shift left_shift_to_zero_less64 by presburger
  then have 4: "... = IntVal bx (take_bit bx (ivX << (shift_amount bx vy + shift_amount bx vz)))"
    by (simp add: bin_combine_left_shift)
  then have 5: "... = IntVal bx 0"
    using assms(6) assms(4) assms(5) left_shift_to_zero_less64 by presburger 
  then show ?thesis
    using "1" "3" "4" unfoldXY xy by force
qed

lemma val_left_shift_becomes_zero:
  assumes "x = new_int bx vx"
  assumes "y = IntVal by vy"
  assumes "z = IntVal bz vz"
  assumes "1 \<le> bx" and "bx \<le> 64"
  assumes "bx \<le> (shift_amount bx vy) + (shift_amount bx vz)"
  assumes "val[(x << y) << z] \<noteq> UndefVal"
  shows "val[(x << y) << z] = IntVal bx 0"
  using val_left_shift_becomes_zero_64 val_left_shift_becomes_zero_less64
  by (meson assms le_neq_implies_less)

(* Exp level proofs *)

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

lemma exp_EliminateRHS:
  assumes "stamp_expr x = IntegerStamp b lo hi" 
  assumes "wf_stamp x"
  assumes "shift_amount b vy = 0" 
  shows "exp[x << const(IntVal c vy)] \<ge> x"
  apply auto
  subgoal premises p for m p xa
    proof -
      obtain xa where x: "[m,p] \<turnstile> x \<mapsto> xa"
        using p by auto
      then have "val[xa << (IntVal c vy)] \<noteq> UndefVal"
        using evalDet p(1,2) x by blast
      then have "wf_value (IntVal c vy)"
        by (auto simp: p(3))
      obtain xan xav where xa: "xa = IntVal xan xav"
        by (metis Value.exhaust evalDet intval_left_shift.simps(2) intval_left_shift.simps(3) 
            intval_left_shift.simps(4) intval_left_shift.simps(5) p(1) p(2) x)
      then have "xa = new_int xan xav"
        using eval_unused_bits_zero x by auto
      then have "xan = b"
        using assms x xa
        by (metis valid_int_same_bits wf_stamp_def)
      then have "val[xa << (IntVal c vy)] = xa" 
        using assms val_EliminateRHS \<open>xa = new_int xan xav\<close>  
              \<open>intval_left_shift xa (IntVal c vy) \<noteq> UndefVal\<close>
        by (metis eval_bits_1_64 less_one linorder_le_less_linear not_gr_zero x xa)
      then show ?thesis
        by (metis evalDet p(1) x)
    qed
    done

lemma exp_left_shift_becomes_zero:
  assumes "stamp_expr x = IntegerStamp b lo hi" 
  assumes "wf_stamp x"
  assumes "1 \<le> b" and "b \<le> 64"
  assumes "(b \<le> (shift_amount b vy + shift_amount b vz))"
  shows "exp[((x << const(IntVal by vy)) << const(IntVal bz vz))] \<ge> exp[const(IntVal b 0)]"
  apply auto
  subgoal premises prems for m p xa
  proof -
    have validValLHS: "val[(xa << (IntVal by vy)) << (IntVal bz vz)] \<noteq> UndefVal"
      using prems(1) by auto
    obtain xa where x: "[m,p] \<turnstile> x \<mapsto> xa"
      using prems(2) by auto
    then have "val[xa << (IntVal by vy)] \<noteq> UndefVal"
      using evalDet prems(2) prems(3) by blast
    obtain bx vx where xa: "xa = new_int bx vx"
      using assms(1) assms(2) x apply auto
      by (metis eval_unused_bits_zero valid_int wf_stamp_def)
    then obtain ivX where "xa = IntVal bx ivX"
      by simp
    moreover have "bx = b"
      using assms(1) assms(2) x calculation apply auto
      by (metis valid_int_same_bits wf_stamp_def)
    then have eq_value_level: "val[(xa << (IntVal by vy)) << (IntVal bz vz)] = IntVal b 0"
      using val_left_shift_becomes_zero \<open>xa = new_int bx vx\<close> 
            validValLHS assms(3) assms(4) assms(5) by auto
    have "wf_value (IntVal b 0)"
      using assms(3) assms(4) by simp
    then have "[m,p] \<turnstile> exp[const(IntVal b 0)] \<mapsto> val[(xa << (IntVal by vy)) << (IntVal bz vz)]"
      by (simp add: eq_value_level unfold_const)
    then show ?thesis
      by (metis evalDet prems(2) x)
  qed
  done

text \<open>Optimisations\<close>

optimization EliminateRHS: "(x << const(IntVal by vy)) \<longmapsto> x when 
                               wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and> 
                               (shift_amount b vy = 0)"
  using exp_EliminateRHS
  by (smt (verit, del_insts) One_nat_def le_refl one_le_numeral shift_amount.elims)

optimization LeftShiftBecomesZero: "((x << const(IntVal by vy)) << const(IntVal bz vz)) \<longmapsto> const(IntVal b 0)  
                          when wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and> 
                               1 \<le> b \<and> b \<le> 64 \<and> 
                               (b \<le> (shift_amount b vy + shift_amount b vz))"
  using exp_left_shift_becomes_zero apply simp
  using numeral_1_eq_Suc_0 by fastforce

(*Unsure if this is to represent comebined left shift"
fun getCombineShiftAmount:: "nat \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
"getCombineShiftAmount b (IntVal by vy) (IntVal bz vz) = 
                    (IntVal b (word_of_nat(shift_amount b vy + shift_amount b vz)::int64))"*)

(* Unsure
optimization CombineLeftShift: "((x << const(IntVal by vy)) << const(IntVal bz vz))
                     \<longmapsto> x << const(getCombineShiftAmount b (IntVal by vy) (IntVal bz vz))
                          when wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and> 
                               1 \<le> b \<and> b \<le> 64 \<and> 
                               ((shift_amount b vy + shift_amount b vz) < b)"
  oops*)

end (* End of ShiftNode *)

end (* End of file *)