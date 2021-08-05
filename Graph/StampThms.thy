section \<open>Stamp Typing\<close>

theory StampThms
  imports Stamp
begin

(* Theories/Lemmas *)
(* TODO: should we have separate 32 and 64 versions of this? *)
lemma int_valid_range:
  assumes "stamp = IntegerStamp 32 lower upper"
  shows "{x . valid_value stamp x} = {(IntVal32 (word_of val)) | val . val \<in> {lower..upper}}"
  using assms valid_value.simps apply auto
  (* TODO: here we need to prove: sint (word_of val) = val
    To do that, we need to know that the stamp is well-formed,
    so its lower and upper bounds fit within 32 bits.

  using valid_value.elims(2) by blast
*)
  sorry

(*
lemma float_valid_range:
  assumes "stamp = FloatStamp bits lower upper"
  shows "{x . valid_value stamp x} = {(FloatVal bits val) | val . val \<in> {lower..upper}}"
  using assms valid_value.simps apply auto
  using valid_value.simps
  by (metis less_eq_float.rep_eq valid_value.elims(2))
*)

lemma disjoint_empty:
  assumes "joined = (join x_stamp y_stamp)"
  assumes "is_stamp_empty joined"
  shows "{x . valid_value x_stamp x} \<inter> {y . valid_value y_stamp y} = {}"
  using assms int_valid_range (*float_valid_range*)
  apply (induction "x_stamp"; induction "y_stamp"; auto)
  sorry

lemma join_unequal:
  assumes "joined = (join x_stamp y_stamp)"
  assumes "is_stamp_empty joined"
  shows "\<nexists> x y . x = y \<and> valid_value x_stamp x \<and> valid_value y_stamp y"
  using assms disjoint_empty by auto

lemma neverDistinctEqual:
  assumes "neverDistinct x_stamp y_stamp"
  shows "\<nexists> x y . x \<noteq> y \<and> valid_value x_stamp x \<and> valid_value y_stamp y"
  using assms
  by (smt (verit, best) asConstant.simps(1) asConstant.simps(2) asConstant.simps(3) neverDistinct.elims(2) valid_value.elims(2))

lemma boundsNoOverlapNoEqual:
  assumes "stpi_upper x_stamp < stpi_lower y_stamp"
  assumes "is_IntegerStamp x_stamp \<and> is_IntegerStamp y_stamp"
  shows "\<nexists> x y . x = y \<and> valid_value x_stamp x \<and> valid_value y_stamp y"
  using assms apply (cases "x_stamp"; auto)
  using int_valid_range
  by (smt (verit, ccfv_threshold) Stamp.collapse(1) mem_Collect_eq valid_value.simps(1))

lemma boundsNoOverlap:
  assumes "stpi_upper x_stamp < stpi_lower y_stamp"
  assumes "x = IntVal b1 xval"
  assumes "y = IntVal b2 yval"
  assumes "is_IntegerStamp x_stamp \<and> is_IntegerStamp y_stamp"
  assumes "valid_value x_stamp x \<and> valid_value y_stamp y"
  shows "xval < yval"
  using assms is_IntegerStamp_def by force

lemma boundsAlwaysOverlap:
  assumes "stpi_lower x_stamp \<ge> stpi_upper y_stamp"
  assumes "x = IntVal b1 xval"
  assumes "y = IntVal b2 yval"
  assumes "is_IntegerStamp x_stamp \<and> is_IntegerStamp y_stamp"
  assumes "valid_value x_stamp x \<and> valid_value y_stamp y"
  shows "\<not>(xval < yval)"
  using assms is_IntegerStamp_def
  by fastforce

lemma intstamp_bits_eq_meet:
  assumes "(meet (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2)) = (IntegerStamp b3 l3 u3)"
  shows "b1 = b3 \<and> b2 = b3"
  by (metis Stamp.distinct(25) assms meet.simps(2))

lemma intstamp_bits_eq_join:
  assumes "(join (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2)) = (IntegerStamp b3 l3 u3)"
  shows "b1 = b3 \<and> b2 = b3"
  by (metis Stamp.distinct(25) assms join.simps(2))

lemma intstamp_bites_eq_unrestricted:
  assumes "(unrestricted_stamp (IntegerStamp b1 l1 u1)) = (IntegerStamp b2 l2 u2)"
  shows "b1 = b2"
  using assms by auto

lemma intstamp_bits_eq_empty:
  assumes "(empty_stamp (IntegerStamp b1 l1 u1)) = (IntegerStamp b2 l2 u2)"
  shows "b1 = b2"
  using assms by auto

(*
lemma floatstamp_bits_eq_meet:
  assumes "(meet (FloatStamp b1 l1 u1) (FloatStamp b2 l2 u2)) = (FloatStamp b3 l3 u3)"
  shows "b1 = b3 \<and> b2 = b3"
  by (metis Stamp.distinct(42) assms meet.simps(3))

lemma floatstamp_bits_eq_join:
  assumes "(join (FloatStamp b1 l1 u1) (FloatStamp b2 l2 u2)) = (FloatStamp b3 l3 u3)"
  shows "b1 = b3 \<and> b2 = b3"
  by (metis Stamp.distinct(42) assms join.simps(3))

lemma floatstamp_bites_eq_unrestricted:
  assumes "(unrestricted_stamp (FloatStamp b1 l1 u1)) = (FloatStamp b2 l2 u2)"
  shows "b1 = b2"
  using assms by auto

lemma floatstamp_bits_eq_empty:
  assumes "(empty_stamp (FloatStamp b1 l1 u1)) = (FloatStamp b2 l2 u2)"
  shows "b1 = b2"
  using assms by auto
*)

(* Manual sanity checks *)
notepad
begin
  have "unrestricted_stamp (IntegerStamp 8 0 10) = (IntegerStamp 8 (- 128) 127)"
    by auto
  have "unrestricted_stamp (IntegerStamp 16 0 10) = (IntegerStamp 16 (- 32768) 32767)"
    by auto
  have "unrestricted_stamp (IntegerStamp 32 0 10) = (IntegerStamp 32 (- 2147483648) 2147483647)"
    by auto
  have "empty_stamp (IntegerStamp 8 0 10) = (IntegerStamp 8 127 (- 128))"
    by auto
  have "empty_stamp (IntegerStamp 16 0 10) = (IntegerStamp 16 32767 (- 32768))"
    by auto
  have "empty_stamp (IntegerStamp 32 0 10) = (IntegerStamp 32 2147483647 (- 2147483648))"
    by auto
  have "join (IntegerStamp 32 0 20) (IntegerStamp 32 (-100) 10) = (IntegerStamp 32 0 10)"
    by auto
  have "meet (IntegerStamp 32 0 20) (IntegerStamp 32 (-100) 10) = (IntegerStamp 32 (- 100) 20)"
    by auto
end

(*
notepad
begin
  have "unrestricted_stamp (FloatStamp 8 0 10) = (FloatStamp 8 neg_infinity pos_infinity)"
    by auto
  have "unrestricted_stamp (FloatStamp 16 0 10) = (FloatStamp 16 neg_infinity pos_infinity)"
    by auto
  have "unrestricted_stamp (FloatStamp 32 0 10) = (FloatStamp 32 neg_infinity pos_infinity)"
    by auto
  have "empty_stamp (FloatStamp 8 0 10) = (FloatStamp 8 pos_infinity neg_infinity)"
    by auto
  have "empty_stamp (FloatStamp 16 0 10) = (FloatStamp 16 pos_infinity neg_infinity)"
    by auto
  have "empty_stamp (FloatStamp 32 0 10) = (FloatStamp 32 pos_infinity neg_infinity)"
    by auto
  have "join (FloatStamp 32 0 20) (FloatStamp 32 (-100) 10) = (FloatStamp 32 0 10)"
    by auto
  have "meet (FloatStamp 32 0 20) (FloatStamp 32 (-100) 10) = (FloatStamp 32 (- 100) 20)"
    by auto
end
*)

end