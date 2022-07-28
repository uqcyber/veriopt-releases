section \<open>Stamp Typing\<close>

theory Stamp
  imports Values
begin

text \<open>
The GraalVM compiler uses the Stamp class to store range and type information
for a given node in the IR graph.
We model the Stamp class as a datatype, Stamp, and provide a number of functions
on the datatype which correspond to the class methods within the compiler.

Stamp information is used in a variety of ways in optimizations, and so, we
additionally provide a number of lemmas which help to prove future optimizations.
\<close>

datatype Stamp = 
  VoidStamp
  | IntegerStamp (stp_bits: nat) (stpi_lower: int) (stpi_upper: int)
  (* | FloatStamp (stp_bits: nat) (stpf_lower: float) (stpf_upper: float) *)
  | KlassPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodCountersPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodPointersStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | ObjectStamp (stp_type: string) (stp_exactType: bool) (stp_nonNull: bool) (stp_alwaysNull: bool)
  | RawPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | IllegalStamp

fun bit_bounds :: "nat \<Rightarrow> (int \<times> int)" where
  "bit_bounds bits = (((2 ^ bits) div 2) * -1, ((2 ^ bits) div 2) - 1)"


experiment begin
corollary "bit_bounds 1 = (-1, 0)" by simp  (* this matches the compiler stamps. *)
end



(* NOTE: the FloatStamp has been commented out to allow use of code generation facilities *)
(*
definition pos_infinity :: "float" where
  "pos_infinity = float_of (0 * 2 powr 255)"

definition neg_infinity :: "float" where
  "neg_infinity = -pos_infinity"
*)

\<comment> \<open>A stamp which includes the full range of the type\<close>
fun unrestricted_stamp :: "Stamp \<Rightarrow> Stamp" where
  "unrestricted_stamp VoidStamp = VoidStamp" |
  "unrestricted_stamp (IntegerStamp bits lower upper) = (IntegerStamp bits (fst (bit_bounds bits)) (snd (bit_bounds bits)))" | 
  (* "unrestricted_stamp (FloatStamp bits lower upper) = (FloatStamp bits neg_infinity pos_infinity)" |  *)
  "unrestricted_stamp (KlassPointerStamp nonNull alwaysNull) = (KlassPointerStamp False False)" |
  "unrestricted_stamp (MethodCountersPointerStamp nonNull alwaysNull) = (MethodCountersPointerStamp False False)" |
  "unrestricted_stamp (MethodPointersStamp nonNull alwaysNull) = (MethodPointersStamp False False)" |
  "unrestricted_stamp (ObjectStamp type exactType nonNull alwaysNull) = (ObjectStamp '''' False False False)" |
  "unrestricted_stamp _ = IllegalStamp"

fun is_stamp_unrestricted :: "Stamp \<Rightarrow> bool" where
  "is_stamp_unrestricted s = (s = unrestricted_stamp s)"

\<comment> \<open>A stamp which provides type information but has an empty range of values\<close>
fun empty_stamp :: "Stamp \<Rightarrow> Stamp" where
  "empty_stamp VoidStamp = VoidStamp" |
  "empty_stamp (IntegerStamp bits lower upper) = (IntegerStamp bits (snd (bit_bounds bits)) (fst (bit_bounds bits)))" |
  (* "empty_stamp (FloatStamp bits lower upper) = (FloatStamp bits pos_infinity neg_infinity)" | *)
  "empty_stamp (KlassPointerStamp nonNull alwaysNull) = (KlassPointerStamp nonNull alwaysNull)" |
  "empty_stamp (MethodCountersPointerStamp nonNull alwaysNull) = (MethodCountersPointerStamp nonNull alwaysNull)" |
  "empty_stamp (MethodPointersStamp nonNull alwaysNull) = (MethodPointersStamp nonNull alwaysNull)" |
  "empty_stamp (ObjectStamp type exactType nonNull alwaysNull) = (ObjectStamp '''' True True False)" |
  "empty_stamp stamp = IllegalStamp"

fun is_stamp_empty :: "Stamp \<Rightarrow> bool" where
  "is_stamp_empty (IntegerStamp b lower upper) = (upper < lower)" |
  (* "is_stamp_empty (FloatStamp b lower upper) = (upper < lower)" | *)
  "is_stamp_empty x = False"

\<comment> \<open>Calculate the meet stamp of two stamps\<close>
fun meet :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "meet VoidStamp VoidStamp = VoidStamp" |
  "meet (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (IntegerStamp b1 (min l1 l2) (max u1 u2))
  )" |
  (* "meet (FloatStamp b1 l1 u1) (FloatStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (FloatStamp b1 (min l1 l2) (max u1 u2))
  )" | *)
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

\<comment> \<open>Calculate the join stamp of two stamps\<close>
fun join :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "join VoidStamp VoidStamp = VoidStamp" |
  "join (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (IntegerStamp b1 (max l1 l2) (min u1 u2))
  )" |
  (* "join (FloatStamp b1 l1 u1) (FloatStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (FloatStamp b1 (max l1 l2) (min u1 u2))
  )" | *)
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

\<comment> \<open>
In certain circumstances a stamp provides enough information to evaluate a value as a stamp,
the asConstant function converts the stamp to a value where one can be inferred.
\<close>
(* NOTE: we could also add a 32-bit version of this if needed. *)
fun asConstant :: "Stamp \<Rightarrow> Value" where
  "asConstant (IntegerStamp b l h) = (if l = h then IntVal b (word_of_int l) else UndefVal)" |
  "asConstant _ = UndefVal"

\<comment> \<open>Determine if two stamps never have value overlaps i.e. their join is empty\<close>
fun alwaysDistinct :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "alwaysDistinct stamp1 stamp2 = is_stamp_empty (join stamp1 stamp2)"

\<comment> \<open>Determine if two stamps must always be the same value i.e. two equal constants\<close>
fun neverDistinct :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "neverDistinct stamp1 stamp2 = (asConstant stamp1 = asConstant stamp2 \<and> asConstant stamp1 \<noteq> UndefVal)"

fun constantAsStamp :: "Value \<Rightarrow> Stamp" where
  "constantAsStamp (IntVal b v) = (IntegerStamp b (sint v) (sint v))" |
  (* TODO: float *)
  "constantAsStamp _ = IllegalStamp"

\<comment> \<open>Define when a runtime value is valid for a stamp\<close>
fun valid_value :: "Value \<Rightarrow> Stamp \<Rightarrow> bool" where
  "valid_value (IntVal b1 v1) (IntegerStamp b l h) =
     (if b1 = b then
       (if l < 0 
        then (l \<le> int_signed_value b1 v1 \<and> int_signed_value b1 v1 \<le> h)
        else (l \<le> int_unsigned_value b1 v1 \<and> int_unsigned_value b1 v1 \<le> h))
      else False)" |
  (* "valid_value (FloatStamp b1 l h) (FloatVal b2 v) = ((b1 = b2) \<and> (v \<ge> l) \<and> (v \<le> h))" | *)
  "valid_value (ObjRef ref) (ObjectStamp klass exact nonNull alwaysNull) = 
     ((alwaysNull \<longrightarrow> ref = None) \<and> (ref=None \<longrightarrow> \<not> nonNull))" |
  "valid_value stamp val = False"
(* TODO: add the other stamps:
  | KlassPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodCountersPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodPointersStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | RawPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
*)

(* Once all other constantAsStamp alternatives have been implemented,
   this should be proved and constant semantics should be updated.
lemma constants_valid:
  assumes "v \<noteq> UndefVal"
  shows "valid_value v (constantAsStamp v)"
  using assms apply (induction v; auto)
*)

fun compatible :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "compatible (IntegerStamp b1 _ _) (IntegerStamp b2 _ _) = (b1 = b2)" |
  "compatible (VoidStamp) (VoidStamp) = True" |
  "compatible _ _ = False"

fun stamp_under :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "stamp_under x y = ((stpi_upper x) < (stpi_lower y))"

\<comment> \<open>
The most common type of stamp within the compiler (apart from the VoidStamp) is a 32 bit
integer stamp with an unrestricted range. We use @{text default_stamp} as it is a frequently used stamp.
\<close>
definition default_stamp :: "Stamp" where
  "default_stamp = (unrestricted_stamp (IntegerStamp 32 0 0))"

(* TODO: should we check that the upper bits are zero? *)
value "valid_value (IntVal 32 (-2)) default_stamp"
end