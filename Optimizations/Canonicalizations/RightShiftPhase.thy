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
(* Has counter-example if x not 32-bit *)
lemma val_ReturnXOnZeroShift:
  assumes "val[x >> (new_int 32 0)] \<noteq> UndefVal"
  and     "x = new_int 32 xv"
  shows "val[x >> (new_int 32 0)] = x"
  using assms apply auto unfolding shiftr_def by auto

(* Exp level proofs *)
lemma exp_ReturnXOnZeroShift:
  assumes "stamp_expr x = IntegerStamp 32 lo hi"
  and     "wf_stamp x"
  shows "exp[x >> const(new_int 32 0)] \<ge> exp[x]"
  apply auto
  subgoal premises p for m p xa
  proof - 
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(1) by auto
    then have vx: "\<exists>vx. xa = new_int 32 vx"
      apply auto by (metis eval_unused_bits_zero wf_stamp_def assms valid_int)
    then have shiftZeroNotUndef: "val[xa >> (new_int 32 0)] \<noteq> UndefVal"
      using evalDet p(1,2) xa by (metis IntVal0)
    then have equals: "xa = val[xa >> (new_int 32 0)]"
      by (metis shiftZeroNotUndef val_ReturnXOnZeroShift vx)
    then show ?thesis
      using evalDet p(1) xa by fastforce
  qed
  done

text \<open>Optimisations\<close>
(* Need to prove exp_ReturnXOnZeroShift *)
optimization ReturnXOnZeroShift: "(x >> const(new_int 32 0)) \<longmapsto> x when 
                                  ((stamp_expr x = IntegerStamp 32 lo hi) \<and> (wf_stamp x))"
   using exp_ReturnXOnZeroShift by fastforce

end (* End of RightShiftNode *)

end (* End of file *)