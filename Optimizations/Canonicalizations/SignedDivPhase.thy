theory SignedDivPhase
  imports
    Common
begin

section \<open>Optimizations for SignedDiv Nodes\<close>

phase SignedDivPhase
  terminating size
begin

(* Value level proofs *)
lemma val_division_by_one_is_self_32:
  assumes "is_IntVal32 x"
  shows "intval_div x (IntVal32 1) = x"
  using assms apply (cases x; auto) done

(* Optimizations*)
(*
optimization opt_DivisionByOneIsSelf32: "x / ConstantExpr (IntVal32 1) \<longmapsto> x"
   apply unfold_optimization unfolding le_expr_def
  sorry*)

end (* end of phase *)

end (* end of file *)
