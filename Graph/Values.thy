section \<open>Runtime Values and Arithmetic\<close>

theory Values
  imports
    "HOL-Library.Word"
    "HOL-Library.Signed_Division"
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
  IntVal (v_bits: int) (v_int: int) |
  FloatVal (v_bits: int) (v_float: float) |
  ObjRef objref |
  ObjStr string

(* Check that a signed int value does not overflow b bits. *)
fun fits_into_n :: "nat \<Rightarrow> int \<Rightarrow> bool" where
  "fits_into_n b val = ((-(2^(b-1)) \<le> val) \<and> (val < (2^(b-1))))"

fun wff_value :: "Value \<Rightarrow> bool" where
  "wff_value (IntVal b v) = 
    (nat b \<in> {1,8,16,32,64} \<and>
    (nat b = 1 \<longrightarrow> (v = 0 \<or> v = 1)) \<and>
    (nat b > 1 \<longrightarrow> fits_into_n (nat b) v))" |
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
lemma wff_byte_pos: "0 < i \<and> i < 128 \<longrightarrow> wff_value (IntVal 8 i)" by simp
lemma wff_byte_128: "i \<ge> 128 \<longrightarrow> \<not> (wff_value (IntVal 8 i))" by simp

value "sint(word_of_int (1) :: int1)"

(* Corresponds to JVM iadd and ladd instructions. *)
fun intval_add :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_add (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32 
       then (IntVal 32 (sint((word_of_int v1 :: int32) + (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) + (word_of_int v2 :: int64)))))" |
  "intval_add _ _ = UndefVal"

code_deps intval_add  (* view dependency graph of code definitions *)
code_thms intval_add  (* print all code definitions used by intval_add *)

value "intval_add (IntVal 32 (2^31-1)) (IntVal 32 (2^31-1))"  (* gives: IntVal 32 (-2) *)
value "intval_add (IntVal 64 (2^31-1)) (IntVal 32 (2^31-1))"  (* gives: IntVal 64 4294967294 *)

(* Corresponds to JVM isub and lsub instructions. *)
fun intval_sub :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_sub (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32 
       then (IntVal 32 (sint((word_of_int v1 :: int32) - (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) - (word_of_int v2 :: int64)))))" |
  "intval_sub _ _ = UndefVal"


(* Corresponds to JVM imul and lmul instructions. *)
fun intval_mul :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_mul (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int v1 :: int32) * (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) * (word_of_int v2 :: int64)))))" |
  "intval_mul _ _ = UndefVal"

(* Java division rounds towards 0. *)
fun intval_div :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_div (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int(v1 sdiv v2) :: int32))))
       else (IntVal 64 (sint((word_of_int(v1 sdiv v2) :: int64)))))" |
  "intval_div _ _ = UndefVal"

(* Java % is a modulo operator that can give negative results, since div rounds towards 0. *)
fun intval_mod :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_mod (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int(v1 smod v2) :: int32))))
       else (IntVal 64 (sint((word_of_int(v1 smod v2) :: int64)))))" |
  "intval_mod _ _ = UndefVal"


(* unsuccessful try at a bitwise generic binary operator:
fun intval_binary :: "('a word \<Rightarrow> 'a word \<Rightarrow> 'a word) \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_binary op (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint(op (word_of_int v1 :: 32 word) (word_of_int v2 :: 32 word))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) + (word_of_int v2 :: int64)))))" |
  "intval_binary _ _ _ = UndefVal"
*)

fun intval_and :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_and (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int v1 :: int32) AND (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) AND (word_of_int v2 :: int64)))))" |
  "intval_and _ _ = UndefVal"

fun intval_or :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_or (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int v1 :: int32) OR (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) OR (word_of_int v2 :: int64)))))" |
  "intval_or _ _ = UndefVal"

fun intval_xor :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_xor (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int v1 :: int32) XOR (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) XOR (word_of_int v2 :: int64)))))" |
  "intval_xor _ _ = UndefVal"

end