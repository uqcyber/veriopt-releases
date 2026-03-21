subsection \<open>RightShiftNode Phase\<close>

theory RightShiftPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase RightShiftNode
  terminating size
begin

(* Value level proofs *)
lemma val_ReturnXOnZeroShift:
  assumes "x = new_int 32 xv"
  shows "val[x >> (IntVal 32 0)] = x"
proof -
  have TB: "take_bit 32 (take_bit 32 xv >>> 0) = take_bit 32 xv"
    unfolding shiftr_def
    by simp
  show ?thesis
    using assms TB
    unfolding new_int.simps intval_right_shift.simps(1)
    by simp
qed

(* Exp level proofs *)
lemma exp_ReturnXOnZeroShift:
  assumes "stamp_expr x = IntegerStamp 32 lo hi"
  and     "wf_stamp x"
  shows "exp[x >> const(IntVal 32 0)] \<ge> exp[x]"
  apply auto
  subgoal premises p for m p xa
  proof -
    obtain bx vx where xa_new: "xa = new_int bx vx"
      using assms p(1)
      by (metis eval_unused_bits_zero valid_int wf_stamp_def)

    then obtain ivX where xa_int: "xa = IntVal bx ivX"
      by simp

    have bx32: "bx = 32"
      using assms p(1) xa_int
      by (metis valid_int_same_bits wf_stamp_def)

    have eq: "val[xa >> (IntVal 32 0)] = xa"
      using xa_new bx32 val_ReturnXOnZeroShift
      by simp

    then show ?thesis
      using p(1) p(2)
      by (metis evalDet)
  qed
  done

text \<open>Optimisations\<close>

optimization ReturnXOnZeroShift:
  "(x >> const(new_int 32 0)) \<longmapsto> x when
    ((stamp_expr x = IntegerStamp 32 lo hi) \<and> wf_stamp x)"
  using exp_ReturnXOnZeroShift
  by fastforce

end

end (* End of file *)
