theory NegatePhase
  imports
    Common
begin

section \<open>Optimizations for Negate Nodes\<close>

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
  sorry

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

lemma exp_negative_cancel:
  shows "exp[-(-x)] \<ge> exp[x]"
  using val_negative_cancel apply (cases x; simp) 
  using unary_eval_new_int apply force 
  sorry

(* Optimisations *)
optimization NegateCancel: "-(-(x)) \<longmapsto> x"
  using val_negative_cancel exp_negative_cancel  by blast 


(* FloatStamp condition is omitted. Not 100% sure. *)
optimization DistributeSubtraction: "-(x - y) \<longmapsto> (y - x)" 
   apply simp_all 
   apply auto
  by (simp add: BinaryExpr evaltree_not_undef val_distribute_sub)


(* Bits: 64, 32, 16, 8, 1 *)
(* 32-bit proof *)
optimization NegativeShift: "-(x >> (const (IntVal b y))) \<longmapsto> 
                                   x >>> (const (IntVal b y))
                                   when (stamp_expr x = IntegerStamp b' lo hi \<and> unat y = (b' - 1))"
   apply simp_all apply auto 
  sorry


end (* End of NegatePhase *)

end (* End of file *)
