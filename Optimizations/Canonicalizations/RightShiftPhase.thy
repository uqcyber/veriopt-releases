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
lemma val_ReturnXOnZeroShift_anyWidth:
  assumes "val[x >> (new_int b 0)] \<noteq> UndefVal"
  and     "x = new_int b xv"
  shows "val[x >> (new_int b 0)] = x"
  using assms apply auto unfolding shiftr_def by auto

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

lemma exp_ReturnXOnZeroShift_anyWidth:
  assumes "stamp_expr x = IntegerStamp b lo hi"
  and     "wf_stamp x"
  shows "exp[x >> const(new_int b 0)] \<ge> exp[x]"
  apply auto
  subgoal premises p for m p xa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(1) by auto
    then have vx: "\<exists>vx. xa = new_int b vx"
      apply auto by (metis eval_unused_bits_zero wf_stamp_def assms valid_int)
    have shiftZeroNotUndef: "val[xa >> (new_int b 0)] \<noteq> UndefVal"
      by (metis evalDet new_int_zero_is_intval p(1,2) xa)
    have "xa = val[xa >> (new_int b 0)]"
      by (metis shiftZeroNotUndef val_ReturnXOnZeroShift_anyWidth vx)
    then show ?thesis
      using evalDet p(1) xa by fastforce
  qed
  done

lemma exp_ReturnXOnZeroShift:
  assumes "stamp_expr x = IntegerStamp 32 lo hi"
  and     "wf_stamp x"
  shows "exp[x >> const(IntVal 32 0)] \<ge> exp[x]"
  apply auto
  subgoal premises p for m p xa
  proof -
    obtain bx vx where xa_new: "xa = new_int bx vx"
      using assms p(1)
      by (meson wf_integerstamp_eval_is_new_int)

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

optimization ReturnXOnZeroShift_anyWidth: "(x >> const (new_int b 0)) \<longmapsto> x
                                  when ((stamp_expr x = IntegerStamp b lo hi) \<and> (wf_stamp x))"
  using exp_ReturnXOnZeroShift_anyWidth by fastforce

optimization ReturnXOnZeroShift:
  "(x >> const(new_int 32 0)) \<longmapsto> x when
    ((stamp_expr x = IntegerStamp 32 lo hi) \<and> wf_stamp x)"
  using exp_ReturnXOnZeroShift
  by fastforce

end (* End of RightShiftPhase *)

end (* End of file *)
