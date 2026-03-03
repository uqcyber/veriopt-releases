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
  assumes "val[x >> (new_int b 0)] \<noteq> UndefVal"
  and     "x = new_int b xv"
  shows "val[x >> (new_int b 0)] = x"
  using assms apply auto unfolding shiftr_def by auto

(* Exp level proofs *)

lemma exp_ReturnXOnZeroShift:
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
      by (metis shiftZeroNotUndef val_ReturnXOnZeroShift vx)
    then show ?thesis
      using evalDet p(1) xa by fastforce
  qed
  done

text \<open>Optimisations\<close>

optimization ReturnXOnZeroShift: "(x >> const (new_int b 0)) \<longmapsto> x
                                  when ((stamp_expr x = IntegerStamp b lo hi) \<and> (wf_stamp x))"
  using exp_ReturnXOnZeroShift by fastforce

end (* End of RightShiftNode *)

end (* End of file *)