section \<open>Runtime Values and Arithmetic\<close>

theory Values
  imports
    "HOL-Library.Word"
    "HOL-Library.Signed_Division"
    "HOL-Library.Float"
    "HOL-Library.LaTeXsugar"
begin

text \<open>
In order to properly implement the IR semantics we first introduce
a new type of runtime values. Our evaluation semantics are defined
in terms of these runtime values.
These runtime values represent the full range of primitive types
currently allowed by our semantics, ranging from basic integer types
to object references and eventually arrays.

An object reference is an option type where the None object reference
points to the static fields. This is examined more closely in our
definition of the heap.
\<close>

type_synonym objref = "nat option"

datatype Value  =
  UndefVal | (* TODO: still required? *)
  IntVal (v_bits: int) (v_int: int) |
  FloatVal (v_bits: int) (v_float: float) |
  ObjRef objref |
  ObjStr string

text \<open>
Java supports 64, 32, 16, 8 signed ints, plus 1 bit (boolean) ints.
Our Value type models this by keeping the value as an infinite precision signed int,
but also carrying along the number of bits allowed.

So each (IntVal b v) should satisfy the invariants:

@{term "b \<in> {1,8,16,32,64}"}

@{term "b > 1 \<Longrightarrow> v == signed (signed_take_bit b v)"}
\<close>

type_synonym int64 = "64 word" \<comment> \<open>long\<close>
type_synonym int32 = "32 word" \<comment> \<open>int\<close>
type_synonym int16 = "16 word" \<comment> \<open>short\<close>
type_synonym int8 = "8 word" \<comment> \<open>char\<close>
type_synonym int1 = "1 word" \<comment> \<open>boolean\<close>


text \<open>
We define integer values to be well-formed when their bit size is valid
and their integer value is able to fit within the bit size.
This is defined using the @{text wf_value} function.
\<close>

\<comment> \<open>Check that a signed int value does not overflow b bits.\<close>
fun fits_into_n :: "nat \<Rightarrow> int \<Rightarrow> bool" where
  "fits_into_n b val = ((-(2^(b-1)) \<le> val) \<and> (val < (2^(b-1))))"

definition int_bits_allowed :: "int set" where
  "int_bits_allowed = {32}"

(* was:   (nat b \<in> {1,8,16,32,64} \<and> ...
   But we temporarily reduce this to 32/64 until we use stamps more statically.
*)
fun wf_value :: "Value \<Rightarrow> bool" where
  "wf_value (IntVal b v) = 
    (b \<in> int_bits_allowed \<and>
    (nat b = 1 \<longrightarrow> (v = 0 \<or> v = 1)) \<and>
    (nat b > 1 \<longrightarrow> fits_into_n (nat b) v))" |
  "wf_value _ = True"

fun wf_bool :: "Value \<Rightarrow> bool" where
  "wf_bool (IntVal b v) = (b = 1 \<and> (v = 0 \<or> v = 1))" |
  "wf_bool _ = False" 

(* boolean values  TODO
lemma "\<not> (wf_value (IntVal 1 (-1)))" by simp
lemma wf_false: "wf_value (IntVal 1 0)" by simp
lemma wf_true: "wf_value (IntVal 1 1)" by simp
lemma "\<not> (wf_value (IntVal 1 2))" by simp

value "(-7::int) div (4::int)"   (* gives -2.  Truncates towards negative infinity, unlike Java. *)
value "(-7::int) mod (4::int)"   (* gives 1.  Whereas Java gives -3. *)
*)

(* byte values TODO
lemma wf_byte__neg129: "i < -128 \<longrightarrow> \<not> (wf_value (IntVal 8 i))" by simp
lemma wf_byte__neg: "-128 \<le> i \<and> i < 0 \<longrightarrow> wf_value (IntVal 8 i)" by simp
lemma wf_byte_0: "wf_value (IntVal 8 0)" by simp
lemma wf_byte_pos: "0 < i \<and> i < 128 \<longrightarrow> wf_value (IntVal 8 i)" by simp
lemma wf_byte_128: "i \<ge> 128 \<longrightarrow> \<not> (wf_value (IntVal 8 i))" by simp
*)

value "sint(word_of_int (1) :: int1)"

text \<open>
We need to introduce arithmetic operations which agree with the JVM.

Within the JVM, bytecode arithmetic operations are performed on 32
or 64 bit integers, unboxing where appropriate.

The following collection of intval functions correspond to the JVM
arithmetic operations.
\<close>

(* Corresponds to JVM iadd and ladd instructions. *)
fun intval_add :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_add (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32 
       then (IntVal 32 (sint((word_of_int v1 :: int32) + (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) + (word_of_int v2 :: int64)))))" |
  "intval_add _ _ = UndefVal"

instantiation Value :: plus
begin

definition plus_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "plus_Value = intval_add"

instance proof qed
end

(* Corresponds to JVM isub and lsub instructions. *)
fun intval_sub :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_sub (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32 
       then (IntVal 32 (sint((word_of_int v1 :: int32) - (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) - (word_of_int v2 :: int64)))))" |
  "intval_sub _ _ = UndefVal"

instantiation Value :: minus
begin

definition minus_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "minus_Value = intval_sub"

instance proof qed
end

(* Corresponds to JVM imul and lmul instructions. *)
fun intval_mul :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_mul (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int v1 :: int32) * (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) * (word_of_int v2 :: int64)))))" |
  "intval_mul _ _ = UndefVal"

instantiation Value :: times
begin

definition times_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "times_Value = intval_mul"

instance proof qed
end

(* Java division rounds towards 0. *)
fun intval_div :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_div (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int(v1 sdiv v2) :: int32))))
       else (IntVal 64 (sint((word_of_int(v1 sdiv v2) :: int64)))))" |
  "intval_div _ _ = UndefVal"

instantiation Value :: divide
begin

definition divide_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "divide_Value = intval_div"

instance proof qed
end

(* Java % is a modulo operator that can give negative results, since div rounds towards 0. *)
fun intval_mod :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_mod (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int(v1 smod v2) :: int32))))
       else (IntVal 64 (sint((word_of_int(v1 smod v2) :: int64)))))" |
  "intval_mod _ _ = UndefVal"

instantiation Value :: modulo
begin

definition modulo_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "modulo_Value = intval_mod"

instance proof qed
end

(* unsuccessful try at a bitwise generic binary operator:
fun intval_binary :: "('a word \<Rightarrow> 'a word \<Rightarrow> 'a word) \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_binary op (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint(op (word_of_int v1 :: 32 word) (word_of_int v2 :: 32 word))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) + (word_of_int v2 :: int64)))))" |
  "intval_binary _ _ _ = UndefVal"
*)

fun intval_and :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "&&*" 64) where
  "intval_and (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int v1 :: int32) AND (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) AND (word_of_int v2 :: int64)))))" |
  "intval_and _ _ = UndefVal"

fun intval_or :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "||*" 59) where
  "intval_or (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int v1 :: int32) OR (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) OR (word_of_int v2 :: int64)))))" |
  "intval_or _ _ = UndefVal"

fun intval_xor :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "^*" 59) where
  "intval_xor (IntVal b1 v1) (IntVal b2 v2) = 
     (if b1 \<le> 32 \<and> b2 \<le> 32
       then (IntVal 32 (sint((word_of_int v1 :: int32) XOR (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) XOR (word_of_int v2 :: int64)))))" |
  "intval_xor _ _ = UndefVal"

fun intval_not :: "Value \<Rightarrow> Value" where
  "intval_not (IntVal b v) = 
     (if b \<le> 32
       then (IntVal 32 (sint(NOT (word_of_int v :: int32))))
       else (IntVal 64 (sint(NOT (word_of_int v :: int64)))))" |
  "intval_not _ = UndefVal"

(* Other possibly-helpful lemmas from WORD and its ancestors:

lemma signed_take_bit_add:
  \<open>signed_take_bit n (signed_take_bit n k + signed_take_bit n l) = signed_take_bit n (k + l)\<close>

lemma plus_dist:
  \<open>Word.the_int (v + w) = take_bit LENGTH('a) (Word.the_int v + Word.the_int w)\<close>
  for v w :: \<open>'a::len word\<close>
*)

(* this follows from the definition of intval_add. *)
lemma intval_add_bits:
  assumes b: "IntVal b res = intval_add x y"
  shows "b = 32 \<or> b = 64"
proof -
  have def: "intval_add x y \<noteq> UndefVal"
    using b by auto
  obtain b1 v1 where x: "x = IntVal b1 v1"
    by (metis Value.exhaust_sel def intval_add.simps(2,3,4,5))
  obtain b2 v2 where y: "y = IntVal b2 v2"
    by (metis Value.exhaust_sel def intval_add.simps(6,7,8,9))
  have
     ax: "intval_add (IntVal b1 v1) (IntVal b2 v2) = 
       (if b1 \<le> 32 \<and> b2 \<le> 32 
       then (IntVal 32 (sint((word_of_int v1 :: int32) + (word_of_int v2 :: int32))))
       else (IntVal 64 (sint((word_of_int v1 :: int64) + (word_of_int v2 :: int64)))))"
      (is "?L = (if ?C then (IntVal 32 ?A) else (IntVal 64 ?B))")
    by simp
  then have l: "IntVal b res = ?L" using b x y by simp 
  have "(b1 \<le> 32 \<and> b2 \<le> 32) \<or> \<not>(b1 \<le> 32 \<and> b2 \<le> 32)" by auto
  then show ?thesis
  proof
    assume "(b1 \<le> 32 \<and> b2 \<le> 32)"
    then have r32: "?L = (IntVal 32 ?A)" using ax by auto
    then have "b = 32" using r32 l b by auto
    then show ?thesis by simp 
  next
    assume "\<not>(b1 \<le> 32 \<and> b2 \<le> 32)"
    then have r64: "?L = (IntVal 64 ?B)" using ax by auto
    then have "b = 64" using r64 l b by auto
    then show ?thesis by simp 
  qed
qed


(* ========================================================================
   Commutative and Associative results.  (Not used yet).
   ======================================================================== *)
lemma word_add_sym: 
  shows "word_of_int v1 + word_of_int v2 = word_of_int v2 + word_of_int v1"
  by simp

(* commutative rules to be used when needed. *)
lemma intval_add_sym1:
  shows "intval_add (IntVal b1 v1) (IntVal b2 v2) = intval_add (IntVal b2 v2) (IntVal b1 v1)"
  by (simp add: word_add_sym)

lemma intval_add_sym:
  shows "intval_add x y = intval_add y x"
  using intval_add_sym1 apply simp
  apply (induction "x")
      apply auto
  apply (induction "y")
      apply auto
  done


lemma word_add_assoc: 
  shows "(word_of_int v1 + word_of_int v2) + word_of_int v3 
       = word_of_int v1 + (word_of_int v2 + word_of_int v3)"
  by simp
(* =========================== end ========================*)


lemma wf_int32:
  assumes wf: "wf_value (IntVal b v)"
  shows "b = 32"
proof -
  have "b \<in> int_bits_allowed"
    using wf wf_value.simps(1) by blast 
  then show ?thesis
    by (simp add: int_bits_allowed_def)
qed

(*
lemma int32_mod [simp]:
  assumes wf: "wf_value (IntVal w b)"
  assumes notbool: "w > 1"
  shows "((b + 2^(w-1)) mod 2^w) = (b + 2^(w-1))"
  using wf notbool by auto
*)

(* Any well-formed IntVal is equal to its underlying integer value. *)
lemma wf_int [simp]:
  assumes wf: "wf_value (IntVal w n)"
  assumes notbool: "w = 32"
  shows "sint((word_of_int n) :: int32) = n"
  apply (simp only: int_word_sint)
  using wf notbool apply simp
  done


(* Adding 0 is the identity, if (IntVal 32 b) is well-formed. *)
lemma add32_0: 
  assumes z:"wf_value (IntVal 32 0)"
  assumes b:"wf_value (IntVal 32 b)"
  shows "intval_add (IntVal 32 0) (IntVal 32 b) = (IntVal 32 (b))"
  apply (simp only: intval_add.simps word_of_int_0)
  apply (simp only: order_class.order.refl conj_absorb if_True)
  apply (simp only: word_add_def uint_0_eq add_0)
  apply (simp only: word_of_int_uint int_word_sint)
  using b apply simp
  done

code_deps intval_add  (* view dependency graph of code definitions *)
code_thms intval_add  (* print all code definitions used by intval_add *)

lemma "intval_add (IntVal 32 (2^31-1)) (IntVal 32 (2^31-1)) = IntVal 32 (-2)"
  by eval
lemma "intval_add (IntVal 64 (2^31-1)) (IntVal 32 (2^31-1)) = IntVal 64 4294967294"
  by eval

end