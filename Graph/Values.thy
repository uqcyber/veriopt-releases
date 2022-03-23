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
a type that represents runtime values.
These runtime values represent the full range of primitive types
currently allowed by our semantics, ranging from basic integer types
to object references and arrays.

Note that Java supports 64, 32, 16, 8 signed ints, plus 1 bit (boolean)
ints, but during calculations the smaller sizes are expanded to 32 bits,
so here we model just 32 and 64 bit values.

An object reference is an option type where the @{term None} object reference
points to the static fields. This is examined more closely in our
definition of the heap.
\<close>

type_synonym int64 = "64 word" \<comment> \<open>long\<close>
type_synonym int32 = "32 word" \<comment> \<open>int\<close>
type_synonym int16 = "16 word" \<comment> \<open>short\<close>
type_synonym int8 = "8 word" \<comment> \<open>char\<close>
type_synonym int1 = "1 word" \<comment> \<open>boolean\<close>

type_synonym objref = "nat option"

datatype (discs_sels) Value  =
  UndefVal |
  IntVal32 "32 word" |  (* includes boolean *)
  IntVal64 "64 word" |
  (* FloatVal float | not supported *)
  ObjRef objref |
  ObjStr string


fun wf_bool :: "Value \<Rightarrow> bool" where
  "wf_bool (IntVal32 v) = (v = 0 \<or> v = 1)" |
  "wf_bool _ = False" 

fun val_to_bool :: "Value \<Rightarrow> bool" where
  "val_to_bool (IntVal32 val) = (if val = 0 then False else True)" |
  "val_to_bool (IntVal64 val) = (if val = 0 then False else True)" |
  "val_to_bool v = False"

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal32 1)" |
  "bool_to_val False = (IntVal32 0)"

value "sint(word_of_int (1) :: int1)"

fun is_int_val :: "Value \<Rightarrow> bool" where
  "is_int_val (IntVal32 v) = True" |
  "is_int_val (IntVal64 v) = True" |
  "is_int_val _ = False"

text \<open>
We need to introduce arithmetic operations which agree with the JVM.

Within the JVM, bytecode arithmetic operations are performed on 32
or 64 bit integers, unboxing where appropriate.

The following collection of intval functions correspond to the JVM
arithmetic operations.  We merge the 32 and 64 bit operations into
a single function, even though the stamp of each IRNode tells us
exactly what the bit widths will be.  These merged functions 
know to make it easier to do the instantiation of Value as 'plus', etc.
It might be worse for reasoning, because it could cause more case analysis,
but this does not seem to be a problem in practice.
\<close>

(* Corresponds to JVM iadd and ladd instructions. *)
fun intval_add :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_add (IntVal32 v1) (IntVal32 v2) = (IntVal32 (v1+v2))" |
  "intval_add (IntVal64 v1) (IntVal64 v2) = (IntVal64 (v1+v2))" |
  "intval_add _ _ = UndefVal"

instantiation Value :: ab_semigroup_add
begin

definition plus_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "plus_Value = intval_add"

print_locale! ab_semigroup_add

instance proof
  fix a b c :: Value
  show "a + b + c = a + (b + c)"
    apply (simp add: plus_Value_def)
    apply (induction a; induction b; induction c; auto)
    done
  show "a + b = b + a"
    apply (simp add: plus_Value_def)
    apply (induction a; induction b; auto)
    done
qed
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

(* NOTE: this bitwise syntax bundle is added for Isabelle 2021-1. *)
context
  includes bit_operations_syntax
begin


fun intval_and :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_and (IntVal32 v1) (IntVal32 v2) = (IntVal32 (v1 AND v2))" |
  "intval_and (IntVal64 v1) (IntVal64 v2) = (IntVal64 (v1 AND v2))" |
  "intval_and _ _ = UndefVal"

fun intval_or :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_or (IntVal32 v1) (IntVal32 v2) = (IntVal32 (v1 OR v2))" |
  "intval_or (IntVal64 v1) (IntVal64 v2) = (IntVal64 (v1 OR v2))" |
  "intval_or _ _ = UndefVal"

fun intval_xor :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_xor (IntVal32 v1) (IntVal32 v2) = (IntVal32 (v1 XOR v2))" |
  "intval_xor (IntVal64 v1) (IntVal64 v2) = (IntVal64 (v1 XOR v2))" |
  "intval_xor _ _ = UndefVal"

fun intval_equals :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_equals (IntVal32 v1) (IntVal32 v2) = bool_to_val (v1 = v2)" |
  "intval_equals (IntVal64 v1) (IntVal64 v2) = bool_to_val (v1 = v2)" |
  "intval_equals _ _ = UndefVal"

fun intval_less_than :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_less_than (IntVal32 v1) (IntVal32 v2) = bool_to_val (v1 <s v2)" |
  "intval_less_than (IntVal64 v1) (IntVal64 v2) = bool_to_val (v1 <s v2)" |
  "intval_less_than _ _ = UndefVal"

fun intval_below :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_below (IntVal32 v1) (IntVal32 v2) = bool_to_val (v1 < v2)" |
  "intval_below (IntVal64 v1) (IntVal64 v2) = bool_to_val (v1 < v2)" |
  "intval_below _ _ = UndefVal"

fun intval_not :: "Value \<Rightarrow> Value" where
  "intval_not (IntVal32 v) = (IntVal32 (NOT v))" |
  "intval_not (IntVal64 v) = (IntVal64 (NOT v))" |
  "intval_not _ = UndefVal"

fun intval_negate :: "Value \<Rightarrow> Value" where
  "intval_negate (IntVal32 v) = IntVal32 (- v)" |
  "intval_negate (IntVal64 v) = IntVal64 (- v)" |
  "intval_negate _ = UndefVal"

fun intval_abs :: "Value \<Rightarrow> Value" where
  "intval_abs (IntVal32 v) = (if (v) <s 0 then (IntVal32 (- v)) else (IntVal32 v))" |
  "intval_abs (IntVal64 v) = (if (v) <s 0 then (IntVal64 (- v)) else (IntVal64 v))" |
  "intval_abs _ = UndefVal"

fun intval_conditional :: "Value \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_conditional cond tv fv = (if (val_to_bool cond) then tv else fv)"

fun intval_logic_negation :: "Value \<Rightarrow> Value" where
  "intval_logic_negation (IntVal32 v) = (if v = 0 then (IntVal32 1) else (IntVal32 0))" |
  "intval_logic_negation (IntVal64 v) = (if v = 0 then (IntVal64 1) else (IntVal64 0))" |
  "intval_logic_negation _ = UndefVal"


fun narrow_helper :: "nat \<Rightarrow> nat \<Rightarrow> int32 \<Rightarrow> Value" where
  "narrow_helper inBits outBits v =
    (if inBits < outBits then UndefVal
     else if outBits = 32 then (IntVal32 v)
     else if outBits = 16 then (IntVal32 (v AND 0xFFFF))
     else if outBits = 8 then (IntVal32 (v AND 0xFF))
     else UndefVal)"

fun intval_narrow :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_narrow inBits outBits (IntVal32 v) = narrow_helper inBits outBits v" |
  "intval_narrow inBits outBits (IntVal64 v) = narrow_helper inBits outBits (ucast v)" |
  "intval_narrow _ _ _ = UndefVal"

value "intval_narrow 16 8 (IntVal64 (-2))"  (* gives 254 *)


fun choose_32_64 :: "nat \<Rightarrow> int64 \<Rightarrow> Value" where
  "choose_32_64 outBits v = (if outBits = 64 then (IntVal64 v) else (IntVal32 (scast v)))"

fun sign_extend_helper :: "nat \<Rightarrow> nat \<Rightarrow> int64 \<Rightarrow> Value" where
  "sign_extend_helper inBits outBits v =
    (if outBits < inBits then UndefVal
     else if inBits = 32 then choose_32_64 outBits v
     else if inBits = 16 then choose_32_64 outBits (scast ((ucast v) :: int16))
     else if inBits = 8 then choose_32_64 outBits (scast ((ucast v) :: int16))
     else UndefVal)"

fun intval_sign_extend :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_sign_extend inBits outBits (IntVal32 v) = sign_extend_helper inBits outBits (scast v)" |
  "intval_sign_extend inBits outBits (IntVal64 v) = sign_extend_helper inBits outBits v" |
  "intval_sign_extend _ _ _ = UndefVal"

value "intval_sign_extend 8 32 (IntVal64 (-2))"


fun zero_extend_helper :: "nat \<Rightarrow> nat \<Rightarrow> int64 \<Rightarrow> Value" where
  "zero_extend_helper inBits outBits v =
    (if outBits < inBits then UndefVal
     else if inBits = 32 then choose_32_64 outBits v
     else if inBits = 16 then choose_32_64 outBits (ucast ((ucast v) :: int16))
     else if inBits = 8 then choose_32_64 outBits (ucast ((ucast v) :: int16))
     else UndefVal)"

fun intval_zero_extend :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_zero_extend inBits outBits (IntVal32 v) = zero_extend_helper inBits outBits (ucast v)" |
  "intval_zero_extend inBits outBits (IntVal64 v) = zero_extend_helper inBits outBits v" |
  "intval_zero_extend _ _ _ = UndefVal"

value "intval_zero_extend 8 32 (IntVal64 (-2))"

(*
lemma [code]: "shiftl1 n = n * 2"
  by (simp add: shiftl1_eq_mult_2)

lemma [code]: "shiftr1 n = n div 2"
  by (simp add: shiftr1_eq_div_2)
*)

definition shiftl (infix "<<" 75) where 
  "shiftl w n = (push_bit n) w"

lemma shiftl_power[simp]: "(x::('a::len) word) * (2 ^ j) = x << j"
  unfolding shiftl_def apply (induction j)
   apply simp unfolding funpow_Suc_right
  by (metis (no_types, opaque_lifting) push_bit_eq_mult)

lemma "(x::('a::len) word) * ((2 ^ j) + 1) = x << j + x"
  by (simp add: distrib_left)

lemma "(x::('a::len) word) * ((2 ^ j) - 1) = x << j - x"
  by (simp add: right_diff_distrib)

lemma "(x::('a::len) word) * ((2^j) + (2^k)) = x << j + x << k"
  by (simp add: distrib_left)

lemma "(x::('a::len) word) * ((2^j) - (2^k)) = x << j - x << k"
  by (simp add: right_diff_distrib)


definition shiftr (infix ">>>" 75) where 
  "shiftr w n = (drop_bit n) w"

value "(255 :: 8 word) >>> (2 :: nat)"


definition signed_shiftr :: "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix ">>" 75) where 
  "signed_shiftr w n = word_of_int ((sint w) div (2 ^ n))"

value "(128 :: 8 word) >> 2"


fun intval_left_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_left_shift (IntVal32 v1) (IntVal32 v2) = IntVal32 (v1 << unat (v2 AND 0x1f))" |
  "intval_left_shift (IntVal64 v1) (IntVal64 v2) = IntVal64 (v1 << unat (v2 AND 0x3f))" |
  "intval_left_shift _ _ = UndefVal"

fun intval_right_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_right_shift (IntVal32 v1) (IntVal32 v2) = IntVal32 (v1 >> unat (v2 AND 0x1f))" |
  "intval_right_shift (IntVal64 v1) (IntVal64 v2) = IntVal64 (v1 >> unat (v2 AND 0x3f))" |
  "intval_right_shift _ _ = UndefVal"

fun intval_uright_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_uright_shift (IntVal32 v1) (IntVal32 v2) = IntVal32 (v1 >>> unat (v2 AND 0x1f))" |
  "intval_uright_shift (IntVal64 v1) (IntVal64 v2) = IntVal64 (v1 >>> unat (v2 AND 0x3f))" |
  "intval_uright_shift _ _ = UndefVal"

end


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

(* commutative rules to be used when needed. *)
lemma intval_add_sym:
  shows "intval_add a b = intval_add b a"
  by (induction a; induction b; auto)


code_deps intval_add  (* view dependency graph of code definitions *)
code_thms intval_add  (* print all code definitions used by intval_add *)


(* Some example tests. *)
lemma "intval_add (IntVal32 (2^31-1)) (IntVal32 (2^31-1)) = IntVal32 (-2)"
  by eval
lemma "intval_add (IntVal64 (2^31-1)) (IntVal64 (2^31-1)) = IntVal64 4294967294"
  by eval

end