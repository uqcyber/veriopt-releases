section \<open>Stamp Typing\<close>

theory Stamp
  imports Values
begin

fun bit_bounds :: "nat \<Rightarrow> (int \<times> int)" where
  "bit_bounds bits = (((2 ^ bits) div 2) * -1, ((2 ^ bits) div 2) - 1)"

definition pos_infinity :: "float" where
  "pos_infinity = float_of (0 * 2 powr 255)"

definition neg_infinity :: "float" where
  "neg_infinity = -pos_infinity"

text_raw \<open>\Snip{Stamp}%\<close>
datatype Stamp = 
  VoidStamp
  | IntegerStamp (stp_bits: nat) (stpi_lower: int) (stpi_upper: int)
  | FloatStamp (stp_bits: nat) (stpf_lower: float) (stpf_upper: float)
  | KlassPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodCountersPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodPointersStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | ObjectStamp (stp_type: string) (stp_exactType: bool) (stp_nonNull: bool) (stp_alwaysNull: bool)
  | RawPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | IllegalStamp
text_raw \<open>\EndSnip\<close>

fun unrestricted_stamp :: "Stamp \<Rightarrow> Stamp" where
  "unrestricted_stamp VoidStamp = VoidStamp" |
  "unrestricted_stamp (IntegerStamp bits lower upper) = (IntegerStamp bits (fst (bit_bounds bits)) (snd (bit_bounds bits)))" | 
  "unrestricted_stamp (FloatStamp bits lower upper) = (FloatStamp bits neg_infinity pos_infinity)" | 
  "unrestricted_stamp (KlassPointerStamp nonNull alwaysNull) = (KlassPointerStamp False False)" |
  "unrestricted_stamp (MethodCountersPointerStamp nonNull alwaysNull) = (MethodCountersPointerStamp False False)" |
  "unrestricted_stamp (MethodPointersStamp nonNull alwaysNull) = (MethodPointersStamp False False)" |
  "unrestricted_stamp (ObjectStamp type exactType nonNull alwaysNull) = (ObjectStamp '''' False False False)" |
  "unrestricted_stamp _ = IllegalStamp"

fun is_stamp_unrestricted :: "Stamp \<Rightarrow> bool" where
  "is_stamp_unrestricted s = (s = unrestricted_stamp s)"

fun empty_stamp :: "Stamp \<Rightarrow> Stamp" where
  "empty_stamp VoidStamp = VoidStamp" |
  "empty_stamp (IntegerStamp bits lower upper) = (IntegerStamp bits (snd (bit_bounds bits)) (fst (bit_bounds bits)))" |
  "empty_stamp (FloatStamp bits lower upper) = (FloatStamp bits pos_infinity neg_infinity)" |
  "empty_stamp (KlassPointerStamp nonNull alwaysNull) = (KlassPointerStamp nonNull alwaysNull)" |
  "empty_stamp (MethodCountersPointerStamp nonNull alwaysNull) = (MethodCountersPointerStamp nonNull alwaysNull)" |
  "empty_stamp (MethodPointersStamp nonNull alwaysNull) = (MethodPointersStamp nonNull alwaysNull)" |
  "empty_stamp (ObjectStamp type exactType nonNull alwaysNull) = (ObjectStamp '''' True True False)" |
  "empty_stamp stamp = IllegalStamp"

fun is_stamp_empty :: "Stamp \<Rightarrow> bool" where
  "is_stamp_empty (IntegerStamp b lower upper) = (upper < lower)" |
  "is_stamp_empty (FloatStamp b lower upper) = (upper < lower)" |
  "is_stamp_empty x = False"

fun meet :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "meet VoidStamp VoidStamp = VoidStamp" |
  "meet (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (IntegerStamp b1 (min l1 l2) (max u1 u2))
  )" |
  "meet (FloatStamp b1 l1 u1) (FloatStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (FloatStamp b1 (min l1 l2) (max u1 u2))
  )" |
  "meet (KlassPointerStamp nn1 an1) (KlassPointerStamp nn2 an2) = (
    KlassPointerStamp (nn1 \<and> nn2) (an1 \<and> an2)
  )" |
  "meet (MethodCountersPointerStamp nn1 an1) (MethodCountersPointerStamp nn2 an2) = (
    MethodCountersPointerStamp (nn1 \<and> nn2) (an1 \<and> an2)
  )" |
  "meet (MethodPointersStamp nn1 an1) (MethodPointersStamp nn2 an2) = (
    MethodPointersStamp (nn1 \<and> nn2) (an1 \<and> an2)
  )" |
  "meet s1 s2 = IllegalStamp"

fun join :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "join VoidStamp VoidStamp = VoidStamp" |
  "join (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (IntegerStamp b1 (max l1 l2) (min u1 u2))
  )" |
  "join (FloatStamp b1 l1 u1) (FloatStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (FloatStamp b1 (max l1 l2) (min u1 u2))
  )" |
  "join (KlassPointerStamp nn1 an1) (KlassPointerStamp nn2 an2) = (
    if ((nn1 \<or> nn2) \<and> (an1 \<or> an2)) 
    then (empty_stamp (KlassPointerStamp nn1 an1))
    else (KlassPointerStamp (nn1 \<or> nn2) (an1 \<or> an2))
  )" |
  "join (MethodCountersPointerStamp nn1 an1) (MethodCountersPointerStamp nn2 an2) = (
    if ((nn1 \<or> nn2) \<and> (an1 \<or> an2)) 
    then (empty_stamp (MethodCountersPointerStamp nn1 an1))
    else (MethodCountersPointerStamp (nn1 \<or> nn2) (an1 \<or> an2))
  )" |
  "join (MethodPointersStamp nn1 an1) (MethodPointersStamp nn2 an2) = (
    if ((nn1 \<or> nn2) \<and> (an1 \<or> an2)) 
    then (empty_stamp (MethodPointersStamp nn1 an1))
    else (MethodPointersStamp (nn1 \<or> nn2) (an1 \<or> an2))
  )" |
  "join s1 s2 = IllegalStamp"


fun asConstant :: "Stamp \<Rightarrow> Value" where
  "asConstant (IntegerStamp b l h) = (if l = h then IntVal b l else UndefVal)" |
  "asConstant _ = UndefVal"

fun alwaysDistinct :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "alwaysDistinct stamp1 stamp2 = is_stamp_empty (join stamp1 stamp2)"

fun neverDistinct :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "neverDistinct stamp1 stamp2 = (asConstant stamp1 = asConstant stamp2 \<and> asConstant stamp1 \<noteq> UndefVal)"

fun constantAsStamp :: "Value \<Rightarrow> Stamp" where
  "constantAsStamp (IntVal b v) = (IntegerStamp (nat b) v v)" |
  (* TODO *)
  "constantAsStamp _ = IllegalStamp"

fun valid_value :: "Stamp \<Rightarrow> Value \<Rightarrow> bool" where
  "valid_value (IntegerStamp b1 l h) (IntVal b2 v) = ((b1 = b2) \<and> (v \<ge> l) \<and> (v \<le> h))" |
  "valid_value (FloatStamp b1 l h) (FloatVal b2 v) = ((b1 = b2) \<and> (v \<ge> l) \<and> (v \<le> h))" |
  "valid_value (VoidStamp) (UndefVal) = True" |
  "valid_value stamp val = False"

definition default_stamp :: "Stamp" where
  "default_stamp = (unrestricted_stamp (IntegerStamp 32 0 0))"

(* Theories/Lemmas *)
lemma int_valid_range:
  assumes "stamp = IntegerStamp bits lower upper"
  shows "{x . valid_value stamp x} = {(IntVal bits val) | val . val \<in> {lower..upper}}"
  using assms valid_value.simps apply auto
  using valid_value.elims(2) by blast

lemma float_valid_range:
  assumes "stamp = FloatStamp bits lower upper"
  shows "{x . valid_value stamp x} = {(FloatVal bits val) | val . val \<in> {lower..upper}}"
  using assms valid_value.simps apply auto
  using valid_value.simps
  by (metis less_eq_float.rep_eq valid_value.elims(2))

lemma disjoint_empty:
  assumes "joined = (join x_stamp y_stamp)"
  assumes "is_stamp_empty joined"
  shows "{x . valid_value x_stamp x} \<inter> {y . valid_value y_stamp y} = {}"
  using assms int_valid_range float_valid_range
  by (induction "x_stamp"; induction "y_stamp"; auto)

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
  by (metis Stamp.distinct(29) assms meet.simps(2))

lemma intstamp_bits_eq_join:
  assumes "(join (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2)) = (IntegerStamp b3 l3 u3)"
  shows "b1 = b3 \<and> b2 = b3"
  by (metis Stamp.distinct(29) assms join.simps(2))

lemma intstamp_bites_eq_unrestricted:
  assumes "(unrestricted_stamp (IntegerStamp b1 l1 u1)) = (IntegerStamp b2 l2 u2)"
  shows "b1 = b2"
  using assms by auto

lemma intstamp_bits_eq_empty:
  assumes "(empty_stamp (IntegerStamp b1 l1 u1)) = (IntegerStamp b2 l2 u2)"
  shows "b1 = b2"
  using assms by auto

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

end