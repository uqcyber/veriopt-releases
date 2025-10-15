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
  unfolding le_expr_def apply auto
  subgoal premises prems for m p x
  proof -
    obtain bv avv where av: "[m,p] \<turnstile> a \<mapsto> IntVal bv avv"
      by (metis intval_not.elims prems(2,3))
    then show ?thesis
      by (metis evalDet eval_unused_bits_zero new_int.elims prems(2,3) val_not_cancel)
  qed
  done
  
text \<open>Optimisations\<close>

optimization NotCancel: "exp[~(~a)] \<longmapsto> a"
  by (metis exp_not_cancel)

end (* End of NotPhase *)

end (* End of file *)