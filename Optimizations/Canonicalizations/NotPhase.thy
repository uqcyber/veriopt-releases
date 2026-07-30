subsection \<open>NotNode Phase\<close>

theory NotPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase NotNode
  terminating size
begin

text \<open> All optimisations complete as at 02/07/26 \<close>

(* Word level proofs *)
lemma bin_not_cancel:
 "bin[\<not>(\<not>(e))] = bin[e]"
  by auto

(* Value level proofs *)
lemma val_not_cancel:
  assumes "val[~(new_int b v)] \<noteq> UndefVal"
  shows   "val[~(~(new_int b v))] = (new_int b v)"
  by (simp add: take_bit_not_take_bit)

lemma val_not_sub_to_neg:
  assumes "val[\<not>(x - (new_int b 1))] \<noteq> UndefVal"
  assumes "val[-x] \<noteq> UndefVal"
  shows "val[\<not>(x - (new_int b 1))] = val[-x]"
  using assms apply (cases x; auto) apply (simp add: minus_diff_commute not_eq_complement)
  using intval_not.simps(2) by presburger+

lemma val_not_negate:
  assumes "val[~(-x)] \<noteq> UndefVal"
  assumes "val[x - (new_int b 1)] \<noteq> UndefVal"
  shows "val[~(-x)] = val[x - (new_int b 1)]"
  using assms apply (cases x; auto) apply (simp add: decr_eq_not_minus take_bit_not_take_bit)
  by meson+

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

optimization NotCancel: "~(~a) \<longmapsto> a"
  by (metis exp_not_cancel)

optimization NotNegate: "~(-x) \<longmapsto> (x - const (new_int b 1))
                         when (stamp_expr x = IntegerStamp b lo hi \<and> wf_stamp x)"
  apply auto subgoal premises p for m p xa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(5) by auto
    obtain xvv where xvv: "xa = new_int b xvv"
      by (metis p(2,3) stamp_eval_same_bits wf_integerstamp_eval_is_new_int xa)
    have constEval: "[m,p] \<turnstile> exp[const (new_int b 1)] \<mapsto> val[new_int b 1]"
      using wf_integerstamp_eval_is_new_int p(2,3) stamp_eval_int xa by blast
    have rhsDefined: "val[xa - (new_int b 1)] \<noteq> UndefVal"
      unfolding xvv by simp
    have "val[~(-xa)] = val[xa - (new_int b 1)]"
      using evalDet p(4,5) rhsDefined val_not_negate xa by blast
    then show ?thesis
      by (metis (no_types, lifting) bin_eval.simps(2) constEval evalDet new_int_one_intval p(1,4,5)
          unfold_binary xa)
  qed
  subgoal premises p for m p xa
  proof -
    have "b \<noteq> 0"
      using wf_integerstamp_implies_nonzero_bits p(2,3,5) by blast
    then show ?thesis
      by (simp add: p(1))
  qed
  done

optimization NotSubToNeg: "~(x - (const (new_int b 1))) \<longmapsto> -x
                           when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x)"
  apply auto subgoal premises p for m p xa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(5) by auto
    obtain xb xvv where xvv: "xa = IntVal xb xvv"
      by (metis p(2,3) valid_int wf_stamp_def xa)
    have rhsNewInt: "val[-xa] = new_int xb (-xvv)"
      unfolding xvv by simp
    have "[m,p] \<turnstile> exp[\<not>(x - (const (new_int b 1)))] \<mapsto> val[\<not>(xa - (new_int b 1))]"
      by (metis (no_types, opaque_lifting) BinaryExpr ConstantExpr UnaryExpr bin_eval.simps(2) xa
          evalDet new_int_one_intval p(1,4,5,6,7) unary_eval.simps(3))
    then show ?thesis
      by (metis Value.distinct(1) evalDet new_int.simps new_int_one_intval p(1,5) xa unfold_unary
          unary_eval.simps(2) rhsNewInt val_not_sub_to_neg)
  qed
  subgoal premises p for m p xa
  proof -
    have "b \<noteq> 0"
      using wf_integerstamp_implies_nonzero_bits p(2,3,5) by blast
    then show ?thesis
      by (simp add: p(1))
  qed
  done

end (* End of NotPhase *)

end (* End of file *)