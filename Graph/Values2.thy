section \<open>Runtime Values and Arithmetic\<close>

theory Values2
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

type_synonym objref = "nat option"

datatype Value  =
  UndefVal |
  IntVal32 int32 |  (* includes boolean *)
  IntVal64 int64 |
  FloatVal float |
  ObjRef objref |
  ObjStr string


text \<open>
We define integer values to be well-formed when their bit size is valid
and their integer value is able to fit within the bit size.
This is defined using the @{text wf_value} function.
\<close>

\<comment> \<open>Check that a signed int value does not overflow b bits.\<close>
fun fits_into_n :: "nat \<Rightarrow> int \<Rightarrow> bool" where
  "fits_into_n b val = ((-(2^(b-1)) \<le> val) \<and> (val < (2^(b-1))))"


fun wf_bool :: "Value \<Rightarrow> bool" where
  "wf_bool (IntVal32 v) = (v = 0 \<or> v = 1)" |
  "wf_bool _ = False" 

fun val_to_bool :: "Value \<Rightarrow> bool" where
  "val_to_bool (IntVal32 v) = (v = 1)" |
  "val_to_bool _ = False"

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal32 1)" |
  "bool_to_val False = (IntVal32 0)"

value "sint(word_of_int (1) :: int1)"

text \<open>
We need to introduce arithmetic operations which agree with the JVM.

Within the JVM, bytecode arithmetic operations are performed on 32
or 64 bit integers, unboxing where appropriate.

The following collection of intval functions correspond to the JVM
arithmetic operations.
\<close>

(* Corresponds to JVM iadd instruction. *)
fun intval_add32 :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_add32 (IntVal32 v1) (IntVal32 v2) = (IntVal32 (v1+v2))" |
  "intval_add32 _ _ = UndefVal"

(* NOTE: this should not need to do widening, since an explicit node does that. *) 
(* Corresponds to JVM ladd instruction. *)
fun intval_add64 :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_add64 (IntVal64 v1) (IntVal64 v2) = (IntVal64 (v1+v2))" |
  "intval_add64 _ _ = UndefVal"


(* OR: We could define a general add function for 32 AND 64 bit ints?
  This makes it easier to do the instantiation of Value as 'plus'.
  But might be worse for reasoning, because it causes more case analysis.
 *)
fun intval_add :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_add (IntVal32 v1) (IntVal32 v2) = (IntVal32 (v1+v2))" |
  "intval_add (IntVal64 v1) (IntVal64 v2) = (IntVal64 (v1+v2))" |
  "intval_add _ _ = UndefVal"

instantiation Value :: plus
begin

definition plus_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "plus_Value = intval_add"

instance proof qed
end

(* Corresponds to JVM isub and lsub instructions. *)
fun intval_sub :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_sub (IntVal32 v1) (IntVal32 v2) = (IntVal32 (v1-v2))" |
  "intval_sub (IntVal64 v1) (IntVal64 v2) = (IntVal64 (v1-v2))" |
  "intval_sub _ _ = UndefVal"

instantiation Value :: minus
begin

definition minus_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "minus_Value = intval_sub"

instance proof qed
end

(* Corresponds to JVM imul and lmul instructions. *)
fun intval_mul :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_mul (IntVal32 v1) (IntVal32 v2) = (IntVal32 (v1*v2))" |
  "intval_mul (IntVal64 v1) (IntVal64 v2) = (IntVal64 (v1*v2))" |
  "intval_mul _ _ = UndefVal"

instantiation Value :: times
begin

definition times_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "times_Value = intval_mul"

instance proof qed
end

(* Java division rounds towards 0, so we use sdiv, not div. *)
(* TODO: find a signed division operator in the Word library? *)
fun intval_div :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_div (IntVal32 v1) (IntVal32 v2) = (IntVal32 (word_of_int((sint v1) sdiv (sint v2))))" |
  "intval_div (IntVal64 v1) (IntVal64 v2) = (IntVal64 (word_of_int((sint v1) sdiv (sint v2))))" |
  "intval_div _ _ = UndefVal"

instantiation Value :: divide
begin

definition divide_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "divide_Value = intval_div"

instance proof qed
end

(* Java % is a modulo operator that can give negative results, since div rounds towards 0. *)
fun intval_mod :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_mod (IntVal32 v1) (IntVal32 v2) = (IntVal32 (word_of_int((sint v1) smod (sint v2))))" |
  "intval_mod (IntVal64 v1) (IntVal64 v2) = (IntVal64 (word_of_int((sint v1) smod (sint v2))))" |
  "intval_mod _ _ = UndefVal"
  (* WAS: (IntVal 32 (sint((word_of_int(v1 smod v2) :: int32))))  *)
  (*      (IntVal 64 (sint((word_of_int(v1 smod v2) :: int64)))))  *)

instantiation Value :: modulo
begin

definition modulo_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "modulo_Value = intval_mod"

instance proof qed
end


fun intval_and :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "&&*" 64) where
  "intval_and (IntVal32 v1) (IntVal32 v2) = (IntVal32 (v1 AND v2))" |
  "intval_and (IntVal64 v1) (IntVal64 v2) = (IntVal64 (v1 AND v2))" |
  "intval_and _ _ = UndefVal"

fun intval_or :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "||*" 59) where
  "intval_or (IntVal32 v1) (IntVal32 v2) = (IntVal32 (v1 OR v2))" |
  "intval_or (IntVal64 v1) (IntVal64 v2) = (IntVal64 (v1 OR v2))" |
  "intval_or _ _ = UndefVal"

fun intval_xor :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "^*" 59) where
  "intval_xor (IntVal32 v1) (IntVal32 v2) = (IntVal32 (v1 XOR v2))" |
  "intval_xor (IntVal64 v1) (IntVal64 v2) = (IntVal64 (v1 XOR v2))" |
  "intval_xor _ _ = UndefVal"

fun intval_not :: "Value \<Rightarrow> Value" where
  "intval_not (IntVal32 v) = (IntVal32 (NOT v))" |
  "intval_not (IntVal64 v) = (IntVal64 (NOT v))" |
  "intval_not _ = UndefVal"

fun intval_equals :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_equals (IntVal32 v1) (IntVal32 v2) = bool_to_val (v1 = v2)" |
  "intval_equals (IntVal64 v1) (IntVal64 v2) = bool_to_val (v1 = v2)" |
  "intval_equals _ _ = UndefVal"

fun intval_less_than :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_less_than (IntVal32 v1) (IntVal32 v2) = bool_to_val (v1 < v2)" |
  "intval_less_than (IntVal64 v1) (IntVal64 v2) = bool_to_val (v1 < v2)" |
  "intval_less_than _ _ = UndefVal"

(* Other possibly-helpful lemmas from WORD and its ancestors:

lemma signed_take_bit_add:
  \<open>signed_take_bit n (signed_take_bit n k + signed_take_bit n l) = signed_take_bit n (k + l)\<close>

lemma plus_dist:
  \<open>Word.the_int (v + w) = take_bit LENGTH('a) (Word.the_int v + Word.the_int w)\<close>
  for v w :: \<open>'a::len word\<close>
*)



(* ========================================================================
   Commutative and Associative results.  (Not used yet).
   ======================================================================== *)
lemma word_add_sym: 
  shows "word_of_int v1 + word_of_int v2 = word_of_int v2 + word_of_int v1"
  by simp

(* commutative rules to be used when needed. *)
lemma intval_add_sym:
  shows "intval_add a b = intval_add b a"
  by (induction a; induction b; auto)


lemma word_add_assoc: 
  shows "(word_of_int v1 + word_of_int v2) + word_of_int v3 
       = word_of_int v1 + (word_of_int v2 + word_of_int v3)"
  by simp

lemma intval_bad1 [simp]: "intval_add (IntVal32 x) (IntVal64 y) = UndefVal"
  by auto
lemma intval_bad2 [simp]: "intval_add (IntVal64 x) (IntVal32 y) = UndefVal"
  by auto

(* this should be provable, but is not trivial. 
lemma intval_assoc: "intval_add (intval_add x y) z = intval_add x (intval_add y z)"
  apply (induction x)
       apply auto
   apply (induction y)
        apply auto
    apply (induction z)
  apply auto
*)

(* Whereas the individual 32-bit version is easier to prove. *)
lemma intval_assoc: "intval_add32 (intval_add32 x y) z = intval_add32 x (intval_add32 y z)"
  apply (induction x)
       apply auto
   apply (induction y)
       apply auto
    apply (induction z)
  by auto
(* =========================== end ========================*)


code_deps intval_add  (* view dependency graph of code definitions *)
code_thms intval_add  (* print all code definitions used by intval_add *)


(* Some example tests. *)
lemma "intval_add (IntVal32 (2^31-1)) (IntVal32 (2^31-1)) = IntVal32 (-2)"
  by eval
lemma "intval_add (IntVal64 (2^31-1)) (IntVal64 (2^31-1)) = IntVal64 4294967294"
  by eval

end