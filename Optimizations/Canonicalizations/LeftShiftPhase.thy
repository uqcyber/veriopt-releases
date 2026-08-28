subsection \<open>LeftShiftNode Phase\<close>

theory LeftShiftPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase LeftShiftNode
  terminating size
begin

(* Value level proofs *)
lemma val_eliminate_RHS:
  assumes "x = new_int bx vx"
  assumes "shift_amount bx vy = 0"
  shows "val[x << (IntVal by vy)] = x"
  using take_bit_shift_zero [of bx vx] assms by force

lemma val_left_shift_becomes_zero:
  assumes "x = new_int bx vx"
  assumes "y = IntVal by vy"
  assumes "z = IntVal bz vz"
  assumes "bx \<le> (shift_amount bx vy) + (shift_amount bx vz)"
  shows "val[(x << y) << z] = new_int bx 0"
proof -
  obtain xv where x: "x = IntVal bx xv"
    using assms(1) by simp
  have "val[x << y] = new_int bx (xv << shift_amount bx vy)"
    using assms(2) x by auto
  then show ?thesis
    by (metis (no_types, lifting) successive_shift_to_sum take_bit_shift_leq_width_0 new_int_zero
        intval_left_shift.simps(1) new_int.simps assms(3,4) take_bit_merge_shift)
qed

(* Exp level proofs *)
lemma exp_eliminate_RHS:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  assumes "shift_amount b vy = 0"
  shows "exp[x << const (IntVal c vy)] \<ge> x"
  using assms apply auto
  by (metis assms(3) stamp_eval_same_bits wf_integerstamp_eval_is_new_int val_eliminate_RHS)

lemma exp_left_shift_becomes_zero:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "wf_stamp x"
  assumes "b \<le> (shift_amount b vy + shift_amount b vz)"
  shows "exp[(x << const (IntVal by vy)) << const (IntVal bz vz)] \<ge> exp[const (IntVal b 0)]"
  using assms apply auto
  by (metis assms(3) new_int_zero val_left_shift_becomes_zero wf_integerstamp_implies_zero_evals
      stamp_eval_same_bits wf_integerstamp_eval_is_new_int)

text \<open>Optimisations\<close>

optimization EliminateRHS: "(x << const (IntVal by vy)) \<longmapsto> x
                             when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and>
                                   shift_amount b vy = 0)"
  using exp_eliminate_RHS by fastforce

optimization LeftShiftBecomesZero: "((x << const (IntVal by vy)) << const (IntVal bz vz)) \<longmapsto>
                                    const (IntVal b 0)
                                    when (wf_stamp x \<and> stamp_expr x = IntegerStamp b lo hi \<and>
                                          b \<le> (shift_amount b vy + shift_amount b vz))"
  using exp_left_shift_becomes_zero by fastforce

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