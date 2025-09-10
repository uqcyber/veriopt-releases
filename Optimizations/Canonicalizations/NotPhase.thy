subsection \<open>NotNode Phase\<close>

theory NotPhase
  imports
    Common
begin

phase NotNode
  terminating size
begin

(* Word level proofs *)
lemma bin_not_cancel:
 "bin[\<not>(\<not>(e))] = bin[e]"
  by auto

(* Value level proofs *)
lemma val_not_cancel:
  assumes "val[~(new_int b v)] \<noteq> UndefVal"
  shows   "val[~(~(new_int b v))] = (new_int b v)"
  by (simp add: take_bit_not_take_bit)

(* Exp level proofs *)
lemma exp_not_cancel:
   "exp[~(~a)] \<ge> exp[a]" 
  unfolding le_expr_def
  apply auto
  subgoal premises prems for m p x
  proof -
    obtain av where av: "[m,p] \<turnstile> a \<mapsto> av"
      using prems(2) by auto
    obtain bv avv where avv: "av = IntVal bv avv"
      by (metis Value.exhaust av evalDet evaltree_not_undef intval_not.simps(3,4,5) prems(2,3))
    then have valEval: "val[~(~av)] = val[av]"
      by (metis av avv evalDet eval_unused_bits_zero new_int.elims prems(2,3) val_not_cancel)
    then show ?thesis
      by (metis av evalDet prems(2))
  qed
  done
  
text \<open>Optimisations\<close>

optimization NotCancel: "exp[~(~a)] \<longmapsto> a"
  by (metis exp_not_cancel)

optimization NotOrToYOnMaskXY: "\<not>(x | y) \<longmapsto> y
                        when (IRExpr_up y = 0 \<and> IRExpr_down x = -1 \<and>
                             (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y))"
  by (simp add: IRExpr_down_def)+

end (* End of NotPhase *)

end (* End of file *)
