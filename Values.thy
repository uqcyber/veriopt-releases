theory Values
  imports
    "HOL-Library.Word"
    "HOL-Library.Float"
    "HOL-Library.LaTeXsugar"
begin

type_synonym objref = "nat option"

(* Java supports 64, 32, 16, 8 signed ints, plus 1 bit (boolean) ints.
   Our Value type models this by keeping the value as an infinite precision signed int,
   but also carrying along the number of bits allowed.
   So each (IntVal b v) should satisfy the invariants:
      b in {1,8,16,32,64} and
      (b > 1 \<Longrightarrow> v == signed (signed_take_bit b v))
*)
type_synonym int64 = "64 word"   (* long *)
type_synonym int32 = "32 word"   (* int *)
type_synonym int16 = "16 word"   (* short *)
type_synonym int8 = "8 word"   (* char *)
type_synonym int1 = "1 word"   (* boolean *)

datatype Value  =
  UndefVal |
  IntVal (v_bits: nat) (v_int: int) |
  FloatVal (v_bits: nat) (v_float: float) |
  ObjRef objref


fun no_overflow_n :: "nat \<Rightarrow> int \<Rightarrow> bool" where
  "no_overflow_n b val = ((-(2^(b-1)) \<le> val) \<and> (val < (2^(b-1))))"

fun wff_value :: "Value \<Rightarrow> bool" where
  "wff_value (IntVal b v) = 
    (b \<in> {1,8,16,32,64} \<and>
    (b = 1 \<longrightarrow> (v = 0 \<or> v = 1)) \<and>
    (b > 1 \<longrightarrow> no_overflow_n b v))" |
  "wff_value _ = True"

(* boolean values *)
lemma "\<not> (wff_value (IntVal 1 (-1)))" by simp
lemma wff_false: "wff_value (IntVal 1 0)" by simp
lemma wff_true: "wff_value (IntVal 1 1)" by simp
lemma "\<not> (wff_value (IntVal 1 2))" by simp

value "(-7::int) div (4::int)"   (* gives -2.  Truncates towards negative infinity, unlike Java. *)
value "(-7::int) mod (4::int)"   (* gives 1.  Whereas Java gives -3. *)

(* byte values *)
lemma wff_byte__neg129: "i < -128 \<longrightarrow> \<not> (wff_value (IntVal 8 i))" by simp
lemma wff_byte__neg: "-128 \<le> i \<and> i < 0 \<longrightarrow> wff_value (IntVal 8 i)" by simp
lemma wff_byte_0: "wff_value (IntVal 8 0)" by simp
lemma wff_byte_127: "0 < i \<and> i < 128 \<longrightarrow> wff_value (IntVal 8 i)" by simp
lemma wff_byte_128: "i \<ge> 128 \<longrightarrow> \<not> (wff_value (IntVal 8 i))" by simp

value "sint(word_of_int (1) :: int1)"
end