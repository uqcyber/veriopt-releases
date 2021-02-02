theory ConditionalElimination
  imports
    IREval
begin

fun wff_stamps :: "IRGraph \<Rightarrow> bool" where
  "wff_stamps g = (\<forall> n \<in> ids g . 
    (\<forall> v m . (g m \<turnstile> (kind g n) \<mapsto> v) \<longrightarrow> valid_value (stamp g n) v))"

lemma join_unequal:
  assumes "joined = (join x_stamp y_stamp)"
  assumes "is_stamp_empty joined"
  shows "\<nexists> x y . x = y \<and> valid_value x_stamp x \<and> valid_value y_stamp y"
  using assms disjoint_empty by auto

lemma foldBinaryOpLogicJoin:
  assumes "wff_stamps g"
  assumes "kind g nid = (IntegerEqualsNode x y)"
  assumes "g m \<turnstile> (kind g nid) \<mapsto> v"
  assumes "is_stamp_empty (join (stamp g x) (stamp g y))"
  shows "v = IntVal 1 0"
  using assms eval.IntegerEqualsNode join_unequal
  by (smt IntegerEqualsNodeE NoNodeE bool_to_val.simps(2) ids_some wff_stamps.simps)

(*
lemma rewriteBinaryOpLogicJoin:
  assumes "wff_stamps g"
  assumes "kind g1 if = (IfNode cond t f)"
  assumes "kind g1 cond = (IntegerEqualsNode x y)"
  assumes "is_stamp_empty (join (stamp g x) (stamp g y))"
  shows "?"
*)

end