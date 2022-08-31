theory SignedDivPhase
  imports
    Common
begin

section \<open>Optimizations for SignedDiv Nodes\<close>

phase SignedDivNode
  terminating size
begin

(* Value level proofs *)
lemma val_division_by_one_is_self_32:
  assumes "x = new_int 32 v"
  shows "intval_div x (IntVal 32 1) = x"
  using assms apply (cases x; auto)
  by (simp add: take_bit_signed_take_bit)

(* Optimizations*)
(*
optimization opt_DivisionByOneIsSelf32: "x / ConstantExpr (IntVal32 1) \<longmapsto> x"
   apply unfold_optimization unfolding le_expr_def
  sorry*)

end (* end of phase *)

end (* end of file *)
