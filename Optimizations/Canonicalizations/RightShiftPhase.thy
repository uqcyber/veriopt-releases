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
  shows "val[x >> (IntVal 32 0)] = val[x]"  
  using assms apply (cases x; auto)
  sorry

(* Exp level proofs *)
lemma exp_ReturnXOnZeroShift:
  assumes "stamp_expr x = IntegerStamp 32 lo hi"
  and     "wf_stamp x"
  shows "exp[x >> const(IntVal 32 0)] \<ge> exp[x]" 
   sorry

text \<open>Optimisations\<close>
(* Need to prove exp_ReturnXOnZeroShift *)
optimization ReturnXOnZeroShift: "(x >> const(new_int 32 0)) \<longmapsto> x when 
                                  ((stamp_expr x = IntegerStamp 32 lo hi) \<and> (wf_stamp x))"
   using exp_ReturnXOnZeroShift by fastforce

end (* End of RightShiftNode *)

end (* End of file *)