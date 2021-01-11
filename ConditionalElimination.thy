theory ConditionalElimination
  imports
    IREval
    Stamp
begin

fun stamp :: "IRGraph \<Rightarrow> ID \<Rightarrow> Stamp" where
  "stamp g nid = unrestricted (IntegerStamp 8 0 0)"

fun wff_stamps :: "IRGraph \<Rightarrow> bool" where
  "wff_stamps g = (\<forall> n \<in> ids g . 
    (\<forall> v m . (g m \<turnstile> n (the (kind g n)) \<mapsto> v) \<and> valid_value (stamp g n) v))"

lemma
  assumes "joined = (join (stamp g x) (stamp g y))"
  assumes "stamp_empty joined"
  shows "\<nexists> v . valid_value joined v" 
  using assms unfolding stamp_empty.simps
  sorry

lemma foldBinaryOpLogicJoin:
  assumes "wff_stamps g"
  assumes "is_IntegerStamp (stamp g x)"
  assumes "is_IntegerStamp (stamp g y)"
  assumes "kind g nid = (Some (IntegerEqualsNode x y))"
  assumes "g m \<turnstile> nid (the (kind g nid)) \<mapsto> v"
  assumes "stamp_empty (join (stamp g x) (stamp g y))"
  shows "v = IntVal 0"
  using eval.IntegerEqualsNode


end