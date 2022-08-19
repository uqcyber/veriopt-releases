theory NegatePhase
  imports
    Common
begin

section \<open>Optimizations for Negate Nodes\<close>

phase NegatePhase
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
  assumes "intval_negate e \<noteq> UndefVal"
  shows "val[-(-(e))] = val[e]"
  by (metis (no_types, lifting) assms intval_negate.elims intval_negate.simps(1) 
      intval_negate.simps(2) verit_minus_simplify(4))

lemma val_distribute_sub:
  assumes "x \<noteq> UndefVal \<and> y \<noteq> UndefVal"
  shows "val[-(x-y)] = val[y-x]"
  using assms by (cases x; cases y; auto)

(* Exp level proofs *)
lemma exp_distribute_sub:
  shows "exp[-(x-y)] \<ge> exp[y-x]"
   apply (cases x; cases y; auto) using unfold_binary val_distribute_sub 
   apply auto[1]
   apply (metis BinaryExpr UnaryExpr bin_eval.simps(3) val_distribute_sub) 
          using bin_eval.simps(3) val_distribute_sub apply auto[1]
   apply (metis BinaryExpr ParameterExpr UnaryExpr bin_eval.simps(3) intval_sub.simps(10) 
          val_distribute_sub)
   apply (metis BinaryExpr LeafExpr UnaryExpr bin_eval.simps(3) intval_sub.simps(10) 
          val_distribute_sub)
   apply (metis BinaryExpr ConstantExpr UnaryExpr bin_eval.simps(3) evaltree_not_undef 
          val_distribute_sub)
   apply (metis BinaryExpr UnaryExpr bin_eval.simps(3) val_distribute_sub)
   apply (metis BinaryExpr bin_eval.simps(3) val_distribute_sub) using val_distribute_sub 
   apply auto[1]
   apply (metis BinaryExpr ParameterExpr bin_eval.simps(3) evaltree_not_undef val_distribute_sub)
   apply (metis BinaryExpr LeafExpr bin_eval.simps(3) val_distribute_sub valid_value.simps(4))
   apply (metis BinaryExpr ConstantExpr bin_eval.simps(3) evaltree_not_undef val_distribute_sub)
          using unfold_binary val_distribute_sub apply auto[1]
          using val_distribute_sub apply auto[1]
          using unfold_binary val_distribute_sub apply auto[1]
   apply (smt (verit, best) ConditionalExpr ParameterExpr bin_eval.simps(3) intval_sub.simps(10) 
          unfold_binary val_distribute_sub)
   apply (smt (verit, ccfv_SIG) BinaryExpr ConditionalExpr LeafExpr bin_eval.simps(3) 
          intval_sub.simps(10) val_distribute_sub)
   apply (smt (verit, ccfv_SIG) ConditionalExpr ConstantExpr bin_eval.simps(3) intval_sub.simps(10) 
          unfold_binary val_distribute_sub)
   apply (metis BinaryExpr ParameterExpr UnaryExpr bin_eval.simps(3) intval_sub.simps(3) 
          val_distribute_sub)
   apply (metis BinaryExpr ParameterExpr bin_eval.simps(3) evaltree_not_undef val_distribute_sub)
   apply (smt (verit, ccfv_SIG) BinaryExpr ConditionalExpr ParameterExpr bin_eval.simps(3) 
          evaltree_not_undef val_distribute_sub)
   apply (metis BinaryExpr ParameterExpr bin_eval.simps(3) evaltree_not_undef val_distribute_sub)
   apply (metis LeafExpr ParameterExpr bin_eval.simps(3) evaltree_not_undef unfold_binary 
          val_distribute_sub)
   apply (metis ConstantExpr ParameterExpr bin_eval.simps(3) unfold_binary val_distribute_sub 
          valid_value.simps(4))
   apply (metis BinaryExpr LeafExpr UnaryExpr bin_eval.simps(3) intval_sub.simps(3) 
          val_distribute_sub)
   apply (metis BinaryExpr LeafExpr bin_eval.simps(3) val_distribute_sub valid_value.simps(4))
   apply (smt (verit, ccfv_SIG) ConditionalExpr LeafExpr bin_eval.simps(3) intval_sub.simps(3) 
          unfold_binary val_distribute_sub)
   apply (metis LeafExpr ParameterExpr bin_eval.simps(3) evaltree_not_undef unfold_binary 
          val_distribute_sub)
   apply (metis LeafExpr bin_eval.simps(3) intval_sub.simps(10) intval_sub.simps(3) unfold_binary 
          val_distribute_sub)
   apply (metis BinaryExpr ConstantExpr LeafExpr bin_eval.simps(3) evaltree_not_undef 
          val_distribute_sub)
   apply (metis BinaryExpr ConstantExpr UnaryExpr bin_eval.simps(3) evaltree_not_undef 
          val_distribute_sub)
   apply (metis BinaryExpr ConstantExpr bin_eval.simps(3) evaltree_not_undef val_distribute_sub)
   apply (smt (verit, ccfv_SIG) BinaryExpr ConditionalExpr ConstantExpr bin_eval.simps(3) 
          evaltree_not_undef val_distribute_sub)
   apply (metis BinaryExpr ConstantExpr ParameterExpr bin_eval.simps(3) intval_sub.simps(10) 
          intval_sub.simps(3) val_distribute_sub)
   apply (metis BinaryExpr ConstantExpr LeafExpr bin_eval.simps(3) evaltree_not_undef 
          val_distribute_sub)
   apply (metis BinaryExpr ConstantExpr bin_eval.simps(3) evaltree_not_undef val_distribute_sub) 
  done

(* Optimisations *)
optimization negate_cancel: "-(-(e)) \<longmapsto> e"
   apply simp_all
  by (metis  unary_eval.simps(2) unfold_unary val_negative_cancel)


(* FloatStamp condition is omitted. Not 100% sure. *)
optimization distribute_sub: "-(x - y) \<longmapsto> (y - x)" 
   apply simp_all 
   apply auto
  by (simp add: BinaryExpr evaltree_not_undef val_distribute_sub)


(* Bits: 64, 32, 16, 8, 1 *)
(* 32-bit proof *)
optimization negative_shift_32: "-(BinaryExpr BinRightShift x (const (IntVal32 31))) \<longmapsto> 
                                   BinaryExpr BinURightShift x (const (IntVal32 31))
                                   when (stamp_expr x = default_stamp)"
   apply simp_all apply auto 
  sorry


end (* End of NegatePhase *)

end (* End of file *)
