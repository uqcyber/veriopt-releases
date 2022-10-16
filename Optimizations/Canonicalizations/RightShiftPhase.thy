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
  assumes "val[x >> (IntVal 32 0)] \<noteq> UndefVal"
  and     "x = IntVal 32 xv"
  shows "val[x >> (IntVal 32 0)] = x"  
  using assms apply (cases x; auto)
  sorry

(* Exp level proofs *)
lemma exp_ReturnXOnZeroShift:
  assumes "stamp_expr x = IntegerStamp 32 lo hi"
  and     "wf_stamp x"
shows "exp[x >> const(IntVal 32 0)] \<ge> exp[x]" 
  apply auto
  subgoal premises p for m p xa
  proof - 
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(1) by auto
    then have 1: "intval_right_shift xa (IntVal 32 0) \<noteq> UndefVal"
      using evalDet p(1) p(2) by blast
    then have 2: "wf_value (IntVal 32 0)"
      using p(3) by auto
    then have equals: "xa = val[xa >> (IntVal 32 0)]"
      using val_ReturnXOnZeroShift apply (cases xa; auto) 
      sorry
    then have 3: "[m,p] \<turnstile> x \<mapsto> intval_right_shift xa (IntVal (32::nat) (0::64 word))"
      by (simp add: xa)
    then show ?thesis
      using evalDet p(1) xa by blast
  qed
  done

text \<open>Optimisations\<close>
(* Need to prove exp_ReturnXOnZeroShift *)
optimization ReturnXOnZeroShift: "(x >> const(new_int 32 0)) \<longmapsto> x when 
                                  ((stamp_expr x = IntegerStamp 32 lo hi) \<and> (wf_stamp x))"
   using exp_ReturnXOnZeroShift by fastforce

end (* End of RightShiftNode *)

end (* End of file *)