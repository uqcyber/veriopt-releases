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
ints, but during calculations the smaller sizes are sign-extended to 32 bits,
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

abbreviation valid_int_widths :: "nat set" where
  "valid_int_widths \<equiv> {1, 8, 16, 32, 64}"


type_synonym objref = "nat option"

datatype (discs_sels) Value  =
  UndefVal |
  IntVal32 "32 word" |  (* also used for 16, 8, and 1-bit (boolean) values *)
  IntVal64 "64 word" |
  (* FloatVal float | not supported *)
  ObjRef objref |
  ObjStr string

text \<open>Characterise integer values, covering both 32 and 64 bit.
  If a node has a stamp smaller than 32 bits (16, 8, or 1 bit),
  then the value will be sign-extended to 32 bits.
  This is necessary to match what the stamps specify 
  E.g. an 8-bit stamp has a default range of -128..+127.
  And a 1-bit stamp has a default range of -1..0, surprisingly.
\<close>

definition is_IntVal :: "Value \<Rightarrow> bool" where
  "is_IntVal v = (is_IntVal32 v \<or> is_IntVal64 v)"

text \<open>Extract signed integer values from both 32 and 64 bit.\<close>

fun intval :: "Value \<Rightarrow> int" where
  "intval (IntVal32 v) = sint v" |
  "intval (IntVal64 v) = sint v"


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



subsection \<open>Arithmetic Operators\<close>

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



subsection \<open>Bitwise Operators and Comparisons\<close>


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

lemma intval_eq32:
  assumes "intval_equals (IntVal32 v1) v2 \<noteq> UndefVal"
  shows "is_IntVal32 v2"
  by (metis Value.exhaust_disc assms intval_equals.simps(10) intval_equals.simps(12) intval_equals.simps(15) intval_equals.simps(16) is_IntVal64_def is_ObjRef_def is_ObjStr_def)

lemma intval_eq32_simp:
  assumes "intval_equals (IntVal32 v1) v2 \<noteq> UndefVal"
  shows "intval_equals (IntVal32 v1) v2 = bool_to_val (v1 = un_IntVal32 v2)"
  by (metis Value.collapse(1) assms intval_eq32 intval_equals.simps(1))



subsection \<open>Narrowing and Widening Operators\<close>

text \<open>Note: we allow these operators to have inBits=outBits, because the Graal compiler
  also seems to allow that case, even though it should rarely / never arise in practice.\<close>

text \<open>When narrowing to less than 32 bits, we sign extend back to 32 bits,
  because we always represent integer values as either 32 or 64 bits.\<close>

fun narrow_helper :: "nat \<Rightarrow> nat \<Rightarrow> int32 \<Rightarrow> Value" where
  "narrow_helper inBits outBits val =
    (if outBits \<le> inBits \<and> outBits \<le> 32 \<and>
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths
     then IntVal32 (signed_take_bit (outBits - 1) val)
     else UndefVal)"

value "sint(signed_take_bit 0 (1 :: int32))" (* gives -1, which matches compiler *)

fun intval_narrow :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_narrow inBits outBits (IntVal32 v) =
     (if inBits = 64 
      then UndefVal
      else narrow_helper inBits outBits v)" |
  "intval_narrow inBits outBits (IntVal64 v) = 
     (if inBits = 64 
      then (if outBits = 64 
            then IntVal64 v 
            else narrow_helper inBits outBits (scast v))
      else UndefVal)" |
  "intval_narrow _ _ _ = UndefVal"

value "intval(intval_narrow 16 8 (IntVal32 (512 - 2)))"  (* gives -2 (IntVal32 4294967294) *)


fun choose_32_64 :: "nat \<Rightarrow> int64 \<Rightarrow> Value" where
  "choose_32_64 outBits v = (if outBits = 64 then (IntVal64 v) else (IntVal32 (scast v)))"

value "sint (signed_take_bit 7 ((256 + 128) :: int64))"

fun sign_extend_helper :: "nat \<Rightarrow> nat \<Rightarrow> int32 \<Rightarrow> Value" where
  "sign_extend_helper inBits outBits val =
    (if inBits \<le> outBits \<and> inBits \<le> 32 \<and>
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths
     then
       (if outBits = 64 
        then IntVal64 (scast (signed_take_bit (inBits - 1) val))
        else IntVal32 (signed_take_bit (inBits - 1) val))
     else UndefVal)"


fun intval_sign_extend :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_sign_extend inBits outBits (IntVal32 v) =
     sign_extend_helper inBits outBits v" |
  "intval_sign_extend inBits outBits (IntVal64 v) = 
     (if inBits=64 \<and> outBits=64 then IntVal64 v else UndefVal)" |
  "intval_sign_extend _ _ _ = UndefVal"


fun zero_extend_helper :: "nat \<Rightarrow> nat \<Rightarrow> int32 \<Rightarrow> Value" where
  "zero_extend_helper inBits outBits val =
    (if inBits \<le> outBits \<and> inBits \<le> 32 \<and>
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths
     then
       (if outBits = 64
        then IntVal64 (ucast (take_bit inBits val))
        else IntVal32 (take_bit inBits val))
     else UndefVal)"

fun intval_zero_extend :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_zero_extend inBits outBits (IntVal32 v) =
     zero_extend_helper inBits outBits v" |
  "intval_zero_extend inBits outBits (IntVal64 v) = 
     (if inBits=64 \<and> outBits=64 then IntVal64 v else UndefVal)" |
  "intval_zero_extend _ _ _ = UndefVal"


text \<open>Some well-formedness results to help reasoning about narrowing and widening operators\<close>

lemma narrow_helper_ok:
  assumes "narrow_helper inBits outBits val \<noteq> UndefVal"
  shows "0 < outBits \<and> outBits \<le> 32 \<and>
        outBits \<le> inBits \<and>
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths"
  using assms narrow_helper.simps neq0_conv by fastforce

lemma intval_narrow_ok:
  assumes "intval_narrow inBits outBits val \<noteq> UndefVal"
  shows "0 < outBits \<and>
        outBits \<le> inBits \<and> 
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths"
  using assms narrow_helper_ok intval_narrow.simps neq0_conv
  by (smt (verit, best) insertCI intval_sign_extend.elims order_le_less zero_neq_numeral) 

lemma narrow_takes_64:
  assumes "result = intval_narrow inBits outBits value"
  assumes "result \<noteq> UndefVal"
  shows "is_IntVal64 value = (inBits = 64)"
  using assms by (cases "value"; simp; presburger)

lemma narrow_gives_64:
  assumes "result = intval_narrow inBits outBits value"
  assumes "result \<noteq> UndefVal"
  shows "is_IntVal64 result = (outBits = 64)"
  using assms
  by (smt (verit, best) Value.case_eq_if Value.discI(1) Value.discI(2) Value.disc_eq_case(3) add_diff_cancel_left' diff_is_0_eq intval_narrow.elims narrow_helper.simps numeral_Bit0 zero_neq_numeral) 


lemma sign_extend_helper_ok:
  assumes "sign_extend_helper inBits outBits val \<noteq> UndefVal"
  shows "0 < inBits \<and> inBits \<le> 32 \<and>
        inBits \<le> outBits \<and> 
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths"
  using assms sign_extend_helper.simps neq0_conv by fastforce

lemma intval_sign_extend_ok:
  assumes "intval_sign_extend inBits outBits val \<noteq> UndefVal"
  shows "0 < inBits \<and>
        inBits \<le> outBits \<and> 
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths"
  using assms sign_extend_helper_ok intval_sign_extend.simps neq0_conv
  by (smt (verit, best) insertCI intval_sign_extend.elims order_le_less zero_neq_numeral) 

lemma zero_extend_helper_ok:
  assumes "zero_extend_helper inBits outBits val \<noteq> UndefVal"
  shows "0 < inBits \<and> inBits \<le> 32 \<and>
        inBits \<le> outBits \<and> 
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths"
  using assms zero_extend_helper.simps neq0_conv by fastforce

lemma intval_zero_extend_ok:
  assumes "intval_zero_extend inBits outBits val \<noteq> UndefVal"
  shows "0 < inBits \<and>
        inBits \<le> outBits \<and> 
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths"
  using assms zero_extend_helper_ok intval_zero_extend.simps neq0_conv
  by (smt (verit, best) insertCI intval_zero_extend.elims order_le_less zero_neq_numeral) 



subsection \<open>Bit-Shifting Operators\<close>

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


text \<open>Note that Java shift operators use unary numeric promotion, unlike other binary 
  operators, which use binary numeric promotion (see the Java language reference manual).
  This means that the left-hand input determines the output size, while the 
  right-hand input can be any size.\<close>

fun intval_left_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_left_shift (IntVal32 v1) (IntVal32 v2) = IntVal32 (v1 << unat (v2 AND 0x1f))" |
  "intval_left_shift (IntVal32 v1) (IntVal64 v2) = IntVal32 (v1 << unat (v2 AND 0x1f))" |
  "intval_left_shift (IntVal64 v1) (IntVal32 v2) = IntVal64 (v1 << unat (v2 AND 0x3f))" |
  "intval_left_shift (IntVal64 v1) (IntVal64 v2) = IntVal64 (v1 << unat (v2 AND 0x3f))" |
  "intval_left_shift _ _ = UndefVal"

fun intval_right_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_right_shift (IntVal32 v1) (IntVal32 v2) = IntVal32 (v1 >> unat (v2 AND 0x1f))" |
  "intval_right_shift (IntVal32 v1) (IntVal64 v2) = IntVal32 (v1 >> unat (v2 AND 0x1f))" |
  "intval_right_shift (IntVal64 v1) (IntVal32 v2) = IntVal64 (v1 >> unat (v2 AND 0x3f))" |
  "intval_right_shift (IntVal64 v1) (IntVal64 v2) = IntVal64 (v1 >> unat (v2 AND 0x3f))" |
  "intval_right_shift _ _ = UndefVal"

fun intval_uright_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_uright_shift (IntVal32 v1) (IntVal32 v2) = IntVal32 (v1 >>> unat (v2 AND 0x1f))" |
  "intval_uright_shift (IntVal32 v1) (IntVal64 v2) = IntVal32 (v1 >>> unat (v2 AND 0x1f))" |
  "intval_uright_shift (IntVal64 v1) (IntVal32 v2) = IntVal64 (v1 >>> unat (v2 AND 0x3f))" |
  "intval_uright_shift (IntVal64 v1) (IntVal64 v2) = IntVal64 (v1 >>> unat (v2 AND 0x3f))" |
  "intval_uright_shift _ _ = UndefVal"

end


section \<open>Examples of Narrowing / Widening Functions\<close>

experiment begin
corollary "intval_narrow 32 8 (IntVal32 (256 + 128)) = IntVal32 (-128)" by simp
corollary "intval_narrow 32 8 (IntVal32 (-2)) = IntVal32 (-2)" by simp
corollary "intval_narrow 32 1 (IntVal32 (-2)) = IntVal32 0"    by simp
corollary "intval_narrow 32 1 (IntVal32 (-3)) = IntVal32 (-1)" by simp

(* now test some 64 bit inputs and outputs *)
corollary "intval_narrow 32 8 (IntVal64 (-2)) = UndefVal" by simp
corollary "intval_narrow 64 8 (IntVal32 (-2)) = UndefVal" by simp
corollary "intval_narrow 64 8 (IntVal64 (-2)) = IntVal32 (-2)" by simp
corollary "intval_narrow 64 8 (IntVal64 (256+127)) = IntVal32 127" by simp
corollary "intval_narrow 64 32 (IntVal64 (-2)) = IntVal32 (-2)" by simp
corollary "intval_narrow 64 64 (IntVal64 (-2)) = IntVal64 (-2)" by simp
end

experiment begin
corollary "intval_sign_extend 8 32 (IntVal32 (256 + 128)) = IntVal32 (-128)" by simp
corollary "intval_sign_extend 8 32 (IntVal32 (-2)) = IntVal32 (-2)" by simp
corollary "intval_sign_extend 1 32 (IntVal32 (-2)) = IntVal32 0"    by simp
corollary "intval_sign_extend 1 32 (IntVal32 (-3)) = IntVal32 (-1)" by simp

(* now test some 64 bit inputs and outputs *)
corollary "intval_sign_extend 8 32 (IntVal64 (-2)) = UndefVal" by simp
corollary "intval_sign_extend 8 64 (IntVal64 (-2)) = UndefVal" by simp
corollary "intval_sign_extend 8 64 (IntVal32 (-2)) = IntVal64 (-2)" by simp
corollary "intval_sign_extend 32 64 (IntVal32 (-2)) = IntVal64 (-2)" by simp
corollary "intval_sign_extend 64 64 (IntVal64 (-2)) = IntVal64 (-2)" by simp
end


experiment begin
corollary "intval_zero_extend 8 32 (IntVal32 (256 + 128)) = IntVal32 128" by simp
corollary "intval_zero_extend 8 32 (IntVal32 (-2)) = IntVal32 254" by simp
corollary "intval_zero_extend 1 32 (IntVal32 (-1)) = IntVal32 1"   by simp
corollary "intval_zero_extend 1 32 (IntVal32 (-2)) = IntVal32 0"   by simp

(* now test some 64 bit inputs and outputs *)
corollary "intval_zero_extend 8 32 (IntVal64 (-2)) = UndefVal" by simp
corollary "intval_zero_extend 8 64 (IntVal64 (-2)) = UndefVal" by simp
corollary "intval_zero_extend 8 64 (IntVal32 (-2)) = IntVal64 254" by simp
corollary "intval_zero_extend 32 64 (IntVal32 (-2)) = IntVal64 4294967294" by simp
end


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