subsection \<open>LeftShiftNode Phase\<close>

theory LeftShiftPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase LeftShiftNode
  terminating size
begin

(* Word level proofs *)
lemma "x \<noteq> 0 \<Longrightarrow> x << 64 = 0" for x::int64
  unfolding shiftl_def by auto

lemma "x \<noteq> 0 \<and> 64 \<le> a \<Longrightarrow> x << a = 0" for x::int64
  unfolding shiftl_def by auto

lemma bin_LeftShiftBecomesZero: "(64 \<le> y + z) \<Longrightarrow> (x << y) << z = 0" for x::int64
  unfolding shiftl_def by auto

lemma bin_combine_left_shift: "(x << y) << z = x << (y + z)" for x::int64
  unfolding shiftl_def apply auto by (metis add.commute)

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
  have "(take_bit bx vx) << 0 = (take_bit bx vx)"
    unfolding shiftl_def by simp
  then show ?thesis
    using assms(1,4,5) by force
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
  unfolding shiftl_def by (simp add: push_bit_take_bit)

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
  then show ?thesis
    using assms(5) by (simp add: assms(3,4) nested_take_bit_left_shift_64 bin_LeftShiftBecomesZero)
qed

lemma left_shift_to_zero_less64:
  assumes "x = new_int bx vx"
  assumes "bx \<le> a"
  assumes "1 \<le> bx" and "bx < 64"
  shows "take_bit bx (vx << a) = 0"
  unfolding shiftl_def by (simp add: assms take_bit_push_bit)

lemma nested_take_bit_left_shift_less64:
  assumes "x = new_int bx vx"
  assumes "1 \<le> bx" and "bx < 64"
  shows "take_bit bx ((take_bit bx (vx << a)) << b) = take_bit bx ((vx << a) << b)"
  unfolding shiftl_def by (simp add: push_bit_take_bit)

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
  then show ?thesis
    using assms(3,4,5,6) left_shift_to_zero_less64 bin_combine_left_shift new_int.simps
          nested_take_bit_left_shift_less64 intval_left_shift.simps(1)
    by presburger
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
      obtain xv where xa: "xa = new_int b xv"
        by (metis wf_stamp_def eval_unused_bits_zero assms(1,2) new_int.elims valid_int x)
      then have "val[xa << (IntVal c vy)] \<noteq> UndefVal"
        using evalDet p(1,2) x by blast
      then have "val[xa << (IntVal c vy)] = xa"
        by (metis xa val_EliminateRHS eval_bits_1_64 less_one not_gr_zero x new_int.elims assms(3)
            linorder_le_less_linear)
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
  using assms apply auto
  subgoal premises prems for m p xa
  proof -
    obtain vx where xa: "xa = new_int b vx"
      apply auto by (metis assms(1,2) eval_unused_bits_zero prems(7) valid_int wf_stamp_def)
    then show ?thesis
      using assms(3,5) prems(4) unfold_const val_left_shift_becomes_zero by force
  qed
  done

text \<open>Optimisations\<close>

optimization EliminateRHS: "(x << const(IntVal by vy)) \<longmapsto> x
                             when wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and>
                               (shift_amount b vy = 0)"
  by (smt (verit, del_insts) exp_EliminateRHS One_nat_def le_refl one_le_numeral shift_amount.elims)

optimization LeftShiftBecomesZero: "((x << const(IntVal by vy)) << const(IntVal bz vz))
                                      \<longmapsto> const(IntVal b 0)
                                      when wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and>
                                      1 \<le> b \<and> b \<le> 64 \<and>
                                      (b \<le> (shift_amount b vy + shift_amount b vz))"
  using exp_left_shift_becomes_zero numeral_1_eq_Suc_0 by fastforce

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