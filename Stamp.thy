theory Stamp
  imports
    IREval
    "HOL-Word.Word"
    "HOL-Library.Float"
begin            

fun bit_bounds :: "nat \<Rightarrow> (int \<times> int)" where
  "bit_bounds bits = (((2 ^ bits) div 2) * -1, ((2 ^ bits) div 2) - 1)"

definition pos_infinity :: "float" where
  "pos_infinity = float_of (0 * 2 powr 255)"

definition neg_infinity :: "float" where
  "neg_infinity = -pos_infinity"

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

fun unrestricted :: "Stamp \<Rightarrow> Stamp" where
  "unrestricted VoidStamp = VoidStamp" |
  "unrestricted (IntegerStamp bits lower upper) = (IntegerStamp bits (fst (bit_bounds bits)) (snd (bit_bounds bits)))" | 
  "unrestricted (FloatStamp bits lower upper) = (FloatStamp bits neg_infinity pos_infinity)" | 
  "unrestricted (KlassPointerStamp nonNull alwaysNull) = (KlassPointerStamp False False)" |
  "unrestricted (MethodCountersPointerStamp nonNull alwaysNull) = (MethodCountersPointerStamp False False)" |
  "unrestricted (MethodPointersStamp nonNull alwaysNull) = (MethodPointersStamp False False)" |
  "unrestricted (ObjectStamp type exactType nonNull alwaysNull) = (ObjectStamp '''' False False False)" |
  "unrestricted _ = IllegalStamp"

fun stamp_unrestricted :: "Stamp \<Rightarrow> bool" where
  "stamp_unrestricted s = (s = unrestricted s)"

fun empty :: "Stamp \<Rightarrow> Stamp" where
  "empty VoidStamp = VoidStamp" |
  "empty (IntegerStamp bits lower upper) = (IntegerStamp bits (snd (bit_bounds bits)) (fst (bit_bounds bits)))" |
  "empty (FloatStamp bits lower upper) = (FloatStamp bits pos_infinity neg_infinity)" |
  "empty (KlassPointerStamp nonNull alwaysNull) = (KlassPointerStamp nonNull alwaysNull)" |
  "empty (MethodCountersPointerStamp nonNull alwaysNull) = (MethodCountersPointerStamp nonNull alwaysNull)" |
  "empty (MethodPointersStamp nonNull alwaysNull) = (MethodPointersStamp nonNull alwaysNull)" |
  "empty (ObjectStamp type exactType nonNull alwaysNull) = (ObjectStamp '''' True True False)" |
  "empty stamp = IllegalStamp"

fun stamp_empty :: "Stamp \<Rightarrow> bool" where
  "stamp_empty (IntegerStamp b lower upper) = (upper < lower)" |
  "stamp_empty x = False"

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
    then (empty (KlassPointerStamp nn1 an1))
    else (KlassPointerStamp (nn1 \<or> nn2) (an1 \<or> an2))
  )" |
  "join (MethodCountersPointerStamp nn1 an1) (MethodCountersPointerStamp nn2 an2) = (
    if ((nn1 \<or> nn2) \<and> (an1 \<or> an2)) 
    then (empty (MethodCountersPointerStamp nn1 an1))
    else (MethodCountersPointerStamp (nn1 \<or> nn2) (an1 \<or> an2))
  )" |
  "join (MethodPointersStamp nn1 an1) (MethodPointersStamp nn2 an2) = (
    if ((nn1 \<or> nn2) \<and> (an1 \<or> an2)) 
    then (empty (MethodPointersStamp nn1 an1))
    else (MethodPointersStamp (nn1 \<or> nn2) (an1 \<or> an2))
  )" |
  "join s1 s2 = IllegalStamp"


fun valid_value :: "Stamp \<Rightarrow> Value \<Rightarrow> bool" where
  "valid_value (IntegerStamp b l h) (IntVal x) = (x \<ge> l \<and> x \<le> h)" |
  "valid_value x y = True"

(* Theories/Lemmas *)
lemma intstamp_bits_eq_meet:
  assumes "(meet (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2)) = (IntegerStamp b3 l3 u3)"
  shows "b1 = b3 \<and> b2 = b3"
  by (metis Stamp.distinct(29) assms meet.simps(2))

lemma intstamp_bits_eq_join:
  assumes "(join (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2)) = (IntegerStamp b3 l3 u3)"
  shows "b1 = b3 \<and> b2 = b3"
  by (metis Stamp.distinct(29) assms join.simps(2))

lemma intstamp_bites_eq_unrestricted:
  assumes "(unrestricted (IntegerStamp b1 l1 u1)) = (IntegerStamp b2 l2 u2)"
  shows "b1 = b2"
  using assms by auto

lemma intstamp_bits_eq_empty:
  assumes "(empty (IntegerStamp b1 l1 u1)) = (IntegerStamp b2 l2 u2)"
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
  assumes "(unrestricted (FloatStamp b1 l1 u1)) = (FloatStamp b2 l2 u2)"
  shows "b1 = b2"
  using assms by auto

lemma floatstamp_bits_eq_empty:
  assumes "(empty (FloatStamp b1 l1 u1)) = (FloatStamp b2 l2 u2)"
  shows "b1 = b2"
  using assms by auto

(* Manual sanity checks *)
notepad
begin
  have "unrestricted (IntegerStamp 8 0 10) = (IntegerStamp 8 (- 128) 127)"
    by auto
  have "unrestricted (IntegerStamp 16 0 10) = (IntegerStamp 16 (- 32768) 32767)"
    by auto
  have "unrestricted (IntegerStamp 32 0 10) = (IntegerStamp 32 (- 2147483648) 2147483647)"
    by auto
  have "empty (IntegerStamp 8 0 10) = (IntegerStamp 8 127 (- 128))"
    by auto
  have "empty (IntegerStamp 16 0 10) = (IntegerStamp 16 32767 (- 32768))"
    by auto
  have "empty (IntegerStamp 32 0 10) = (IntegerStamp 32 2147483647 (- 2147483648))"
    by auto
  have "join (IntegerStamp 32 0 20) (IntegerStamp 32 (-100) 10) = (IntegerStamp 32 0 10)"
    by auto
  have "meet (IntegerStamp 32 0 20) (IntegerStamp 32 (-100) 10) = (IntegerStamp 32 (- 100) 20)"
    by auto
end

notepad
begin
  have "unrestricted (FloatStamp 8 0 10) = (FloatStamp 8 neg_infinity pos_infinity)"
    by auto
  have "unrestricted (FloatStamp 16 0 10) = (FloatStamp 16 neg_infinity pos_infinity)"
    by auto
  have "unrestricted (FloatStamp 32 0 10) = (FloatStamp 32 neg_infinity pos_infinity)"
    by auto
  have "empty (FloatStamp 8 0 10) = (FloatStamp 8 pos_infinity neg_infinity)"
    by auto
  have "empty (FloatStamp 16 0 10) = (FloatStamp 16 pos_infinity neg_infinity)"
    by auto
  have "empty (FloatStamp 32 0 10) = (FloatStamp 32 pos_infinity neg_infinity)"
    by auto
  have "join (FloatStamp 32 0 20) (FloatStamp 32 (-100) 10) = (FloatStamp 32 0 10)"
    by auto
  have "meet (FloatStamp 32 0 20) (FloatStamp 32 (-100) 10) = (FloatStamp 32 (- 100) 20)"
    by auto
end

end