subsection \<open>NegateNode Phase\<close>

theory NegatePhase
  imports
    Common
begin

phase NegateNode
  terminating size
begin

(* Word level proofs *)
lemma bin_negative_cancel:
 "-1 * (-1 * ((x::('a::len) word))) = x"
  by auto

value "(2 :: 32 word) >>> (31 :: nat)"
value "-((2 :: 32 word) >> (31 :: nat))"

lemma bin_negative_shift32:
  shows "-((x :: 32 word) >> (31 :: nat)) = x >>> (31 :: nat)"
  unfolding sshiftr_def shiftr_def sorry

(* Value level proofs *)
lemma val_negative_cancel:
  assumes "intval_negate (new_int b v) \<noteq> UndefVal"
  shows "val[-(-(new_int b v))] = val[new_int b v]"
  using assms by simp

lemma val_distribute_sub:
  assumes "x \<noteq> UndefVal \<and> y \<noteq> UndefVal"
  shows "val[-(x-y)] = val[y-x]"
  using assms by (cases x; cases y; auto)

(* Exp level proofs *)
lemma exp_distribute_sub:
  shows "exp[-(x-y)] \<ge> exp[y-x]"
  using val_distribute_sub apply auto
  using evaltree_not_undef by auto

thm_oracles exp_distribute_sub

lemma exp_negative_cancel:
  shows "exp[-(-x)] \<ge> exp[x]"
  using val_negative_cancel apply auto
  by (metis (no_types, opaque_lifting) eval_unused_bits_zero intval_negate.elims intval_negate.simps(1) minus_equation_iff new_int.simps take_bit_dist_neg) 

(* Optimisations *)
optimization NegateCancel: "-(-(x)) \<longmapsto> x"
  using val_negative_cancel exp_negative_cancel  by blast 


(* FloatStamp condition is omitted. Not 100% sure. *)
optimization DistributeSubtraction: "-(x - y) \<longmapsto> (y - x)" 
   apply simp_all 
   apply auto
  by (simp add: BinaryExpr evaltree_not_undef val_distribute_sub)


optimization NegativeShift: "-(x >> (const (IntVal b y))) \<longmapsto> x >>> (const (IntVal b y))
                                   when (stamp_expr x = IntegerStamp b' lo hi \<and> unat y = (b' - 1))"
   apply simp_all apply auto 
  sorry


end (* End of NegatePhase *)

end (* End of file *)
