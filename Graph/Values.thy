section \<open>Runtime Values and Arithmetic\<close>

theory Values
  imports
    "HOL-Library.Word"
    "HOL-Library.Signed_Division"
    "HOL-Library.Float"
    "HOL-Library.LaTeXsugar"
begin

lemma "-((x::float)-y) = (y-x)"
  by simp

text \<open>
In order to properly implement the IR semantics we first introduce
a type that represents runtime values.
These runtime values represent the full range of primitive types
currently allowed by our semantics, ranging from basic integer types
to object references and arrays.

Note that Java supports 64, 32, 16, 8 signed ints, plus 1 bit (boolean)
ints, and char is 16-bit unsigned.
E.g. an 8-bit stamp has a default range of -128..+127.
And a 1-bit stamp has a default range of -1..0, surprisingly.

During calculations the smaller sizes are sign-extended to 32 bits, but explicit 
widening nodes will do that, so most binary calculations should see equal input sizes.

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


text \<open>Option 2: explicit width stored with each integer value.
      However, this does not help us to distinguish between short (signed) and char (unsigned).\<close>

typedef IntWidth = "{ w :: nat . w=1 \<or> w=8 \<or> w=16 \<or> w=32 \<or> w=64 }"
  by blast

setup_lifting type_definition_IntWidth

lift_definition IntWidthBits :: "IntWidth \<Rightarrow> nat"
  is "\<lambda>w. w" .


text \<open>Option 3: explicit type stored with each integer value.\<close>

datatype IntType = ILong | IInt | IShort | IChar | IByte | IBoolean

fun int_bits :: "IntType \<Rightarrow> nat" where
  "int_bits ILong  = 64" |
  "int_bits IInt   = 32" |
  "int_bits IShort = 16" |
  "int_bits IChar  = 16" |
  "int_bits IByte  =  8" |
  "int_bits IBoolean = 1"

fun int_signed :: "IntType \<Rightarrow> bool" where
  "int_signed ILong  = True" |
  "int_signed IInt   = True" |
  "int_signed IShort = True" |
  "int_signed IChar  = False" |
  "int_signed IByte  =  True" |
  "int_signed IBoolean = True"


text \<open>Option 4: int64 with the number of significant bits.\<close>


type_synonym iwidth = "nat"  (* TODO: 1..64 *)
type_synonym objref = "nat option"

datatype (discs_sels) Value  =
  UndefVal |
  (* IntVal32 "32 word" | *)  (* also used for 16, 8, and 1-bit (boolean) values *)
  (* IntVal64 "64 word" | *)
  (* IntVal IntType int64 |  -- all types smaller than 64 bits are zero-extended *)
  (* or widths: IntVal (ibits:IntWidth) (ival:int64) | *)
  (* or just:   IntVal (ibits:nat) (ival:int64) ? *)
  (* or         IntVal IntWord where IntWord = (nat,int64)? *)
  (* IntValv2 nat bool int64 |   bits, signed, word *)
  IntVal iwidth int64 | (* bits and word because we cannot know sign until do compare! *)
  (* FloatVal float | not supported *)
  ObjRef objref |
  ObjStr string

fun intval_bits :: "Value \<Rightarrow> nat" where
  "intval_bits (IntVal b v) = b"

fun bit_bounds :: "nat \<Rightarrow> (int \<times> int)" where
  "bit_bounds bits = (((2 ^ bits) div 2) * -1, ((2 ^ bits) div 2) - 1)"

definition logic_negate :: "('a::len) word \<Rightarrow> 'a word" where
  "logic_negate x = (if x = 0 then 1 else 0)"

fun int_signed_value :: "iwidth \<Rightarrow> int64 \<Rightarrow> int" where
  "int_signed_value b v = sint (signed_take_bit (b - 1) v)"

fun int_unsigned_value :: "iwidth \<Rightarrow> int64 \<Rightarrow> int" where
  "int_unsigned_value b v = uint v"  (* NB. we could drop take_bit? *)


text \<open>Converts an integer word into a Java value.\<close>
fun new_int :: "iwidth \<Rightarrow> int64 \<Rightarrow> Value" where
  "new_int b w = IntVal b (take_bit b w)"

text \<open>Converts an integer word into a Java value, iff the two types are equal.\<close>
fun new_int_bin :: "iwidth \<Rightarrow> iwidth \<Rightarrow> int64 \<Rightarrow> Value" where
  "new_int_bin b1 b2 w = (if b1=b2 then new_int b1 w else UndefVal)"


fun wf_bool :: "Value \<Rightarrow> bool" where
  "wf_bool (IntVal b w) = (b = 1)" |
  "wf_bool _ = False" 

fun val_to_bool :: "Value \<Rightarrow> bool" where
  "val_to_bool (IntVal b val) = (if val = 0 then False else True)" |
  "val_to_bool val = False"

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal 1 1)" |
  "bool_to_val False = (IntVal 1 0)"


text \<open>Converts an Isabelle bool into a Java value, iff the two types are equal.\<close>
fun bool_to_val_bin :: "iwidth \<Rightarrow> iwidth \<Rightarrow> bool \<Rightarrow> Value" where
  "bool_to_val_bin t1 t2 b = (if t1 = t2 then bool_to_val b else UndefVal)"


(* Deprecated - just for backwards compatibility. *)
fun is_int_val :: "Value \<Rightarrow> bool" where
  "is_int_val v = is_IntVal v"



subsection \<open>Arithmetic Operators\<close>

text \<open>
We need to introduce arithmetic operations which agree with the JVM.

Within the JVM, bytecode arithmetic operations are performed on 32
or 64 bit integers, unboxing where appropriate.

The following collection of intval functions correspond to the JVM
arithmetic operations.  We merge the 32 and 64 bit operations into
a single function, even though the stamp of each IRNode tells us
exactly what the bit widths will be.  These merged functions 
make it easier to do the instantiation of Value as 'plus', etc.
It might be worse for reasoning, because it could cause more case analysis,
but this does not seem to be a problem in practice.
\<close>

(* Corresponds to JVM iadd and ladd instructions. *)
fun intval_add :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_add (IntVal b1 v1) (IntVal b2 v2) = 
    (if b1 = b2 then IntVal b1 (take_bit b1 (v1+v2)) else UndefVal)" |
  "intval_add _ _ = UndefVal"

(* TODO if needed:
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
    
  show "a + b = b + a"
    apply (simp add: plus_Value_def)
    apply (induction a; induction b; auto)
    done
qed
end
*)

(* Corresponds to JVM isub and lsub instructions. *)
fun intval_sub :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_sub (IntVal b1 v1) (IntVal b2 v2) = new_int_bin b1 b2 (v1-v2)" |
  "intval_sub _ _ = UndefVal"


instantiation Value :: minus
begin

definition minus_Value :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "minus_Value = intval_sub"

instance proof qed
end


(* Corresponds to JVM imul and lmul instructions. *)
fun intval_mul :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_mul (IntVal b1 v1) (IntVal b2 v2) = new_int_bin b1 b2 (v1*v2)" |
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
  "intval_div (IntVal b1 v1) (IntVal b2 v2) = 
        new_int_bin b1 b2 (word_of_int
           ((int_signed_value b1 v1) sdiv (int_signed_value b2 v2)))" |
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
        new_int_bin b1 b2 (word_of_int
           ((int_signed_value b1 v1) smod (int_signed_value b2 v2)))" |
  "intval_mod _ _ = UndefVal"

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
  "intval_and (IntVal b1 v1) (IntVal b2 v2) = new_int_bin b1 b2 (v1 AND v2)" |
  "intval_and _ _ = UndefVal"

fun intval_or :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_or (IntVal b1 v1) (IntVal b2 v2) = new_int_bin b1 b2 (v1 OR v2)" |
  "intval_or _ _ = UndefVal"

fun intval_xor :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_xor (IntVal b1 v1) (IntVal b2 v2) = new_int_bin b1 b2 (v1 XOR v2)" |
  "intval_xor _ _ = UndefVal"

(* TODO: temp guess at semantics *)
fun intval_short_circuit_or :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_short_circuit_or (IntVal b1 v1) (IntVal b2 v2) = new_int_bin b1 b2 (v1 OR v2)" |
  "intval_short_circuit_or _ _ = UndefVal"

fun intval_equals :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_equals (IntVal b1 v1) (IntVal b2 v2) = bool_to_val_bin b1 b2 (v1 = v2)" |
  "intval_equals _ _ = UndefVal"

fun intval_less_than :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_less_than (IntVal b1 v1) (IntVal b2 v2) = 
    bool_to_val_bin b1 b2 (int_signed_value b1 v1 < int_signed_value b2 v2)" |
  "intval_less_than _ _ = UndefVal"

fun intval_below :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_below (IntVal b1 v1) (IntVal b2 v2) = bool_to_val_bin b1 b2 (v1 < v2)" |
  "intval_below _ _ = UndefVal"

fun intval_not :: "Value \<Rightarrow> Value" where
  "intval_not (IntVal t v) = new_int t (NOT v)" |
  "intval_not _ = UndefVal"

fun intval_negate :: "Value \<Rightarrow> Value" where
  "intval_negate (IntVal t v) = new_int t (- v)" |
  "intval_negate _ = UndefVal"

fun intval_abs :: "Value \<Rightarrow> Value" where
  "intval_abs (IntVal t v) = new_int t (if int_signed_value t v < 0 then - v else v)" |
  "intval_abs _ = UndefVal"

fun intval_conditional :: "Value \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_conditional cond tv fv = (if (val_to_bool cond) then tv else fv)"

text \<open>TODO: clarify which widths this should work on: just 1-bit or all?\<close>
fun intval_logic_negation :: "Value \<Rightarrow> Value" where
  "intval_logic_negation (IntVal b v) = (IntVal b (logic_negate v))" |
  "intval_logic_negation _ = UndefVal"



subsection \<open>Narrowing and Widening Operators\<close>

text \<open>Note: we allow these operators to have inBits=outBits, because the Graal compiler
  also seems to allow that case, even though it should rarely / never arise in practice.\<close>

(* Not needed now:
fun narrow_helper :: "nat \<Rightarrow> nat \<Rightarrow> int32 \<Rightarrow> Value" where
  "narrow_helper inBits outBits val =
    (if outBits \<le> inBits \<and> outBits \<le> 32 \<and>
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths
     then IntVal32 (signed_take_bit (outBits - 1) val)
     else UndefVal)"
*)

value "sint(signed_take_bit 0 (1 :: int32))" (* gives -1, which matches compiler *)

fun intval_narrow :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_narrow inBits outBits (IntVal b v) =
     (if inBits = b \<and> outBits \<le> inBits  
      then new_int outBits v
      else UndefVal)" |
  "intval_narrow _ _ _ = UndefVal"

value "intval(intval_narrow 16 8 (IntVal32 (512 - 2)))"  (* gives -2 (IntVal32 4294967294) *)

(* Not needed now:
fun choose_32_64 :: "nat \<Rightarrow> int64 \<Rightarrow> Value" where
  "choose_32_64 outBits v = (if outBits = 64 then (IntVal64 v) else (IntVal32 (scast v)))"
*)

value "sint (signed_take_bit 7 ((256 + 128) :: int64))"

(*
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
*)

fun intval_sign_extend :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_sign_extend inBits outBits (IntVal b v) =
     (if inBits = b \<and> outBits \<ge> inBits  
      then new_int outBits (signed_take_bit (inBits - 1) v)
      else UndefVal)" |
  "intval_sign_extend _ _ _ = UndefVal"

(* Not needed now:
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
*)

fun intval_zero_extend :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_zero_extend inBits outBits (IntVal b v) =
     (if inBits = b \<and> outBits \<ge> inBits  
      then new_int outBits (take_bit inBits v)
      else UndefVal)" |
  "intval_zero_extend _ _ _ = UndefVal"


text \<open>Some well-formedness results to help reasoning about narrowing and widening operators\<close>

lemma intval_narrow_ok:
  assumes "intval_narrow inBits outBits val \<noteq> UndefVal"
  shows "0 \<le> outBits \<and>
        outBits \<le> inBits \<and> 
        is_IntVal val \<and>
        intval_bits val = inBits"
  using assms intval_narrow.simps neq0_conv intval_bits.simps
  by (metis intval_narrow.elims is_IntVal_def less_eq_nat.simps(1))

(* Not needed now:
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
*)

lemma intval_sign_extend_ok:
  assumes "intval_sign_extend inBits outBits val \<noteq> UndefVal"
  shows "0 \<le> inBits \<and>
        inBits \<le> outBits \<and> 
        is_IntVal val \<and>
        intval_bits val = inBits"
  using assms intval_sign_extend.simps neq0_conv
  by (metis intval_bits.simps intval_sign_extend.elims is_IntVal_def less_eq_nat.simps(1))

(*
lemma zero_extend_helper_ok:
  assumes "zero_extend_helper inBits outBits val \<noteq> UndefVal"
  shows "0 < inBits \<and> inBits \<le> 32 \<and>
        inBits \<le> outBits \<and> 
        outBits \<in> valid_int_widths \<and>
        inBits \<in> valid_int_widths"
  using assms zero_extend_helper.simps neq0_conv by fastforce
*)

lemma intval_zero_extend_ok:
  assumes "intval_zero_extend inBits outBits val \<noteq> UndefVal"
  shows "0 \<le> inBits \<and>
        inBits \<le> outBits \<and> 
        is_IntVal val \<and>
        intval_bits val = inBits"
  using assms intval_sign_extend.simps neq0_conv
  by (metis intval_bits.simps intval_zero_extend.elims is_IntVal_def less_eq_nat.simps(1))


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

fun shift_amount :: "iwidth \<Rightarrow> int64 \<Rightarrow> nat" where
  "shift_amount b val = unat (val AND (if b = 64 then 0x3F else 0x1f))"

fun intval_left_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_left_shift (IntVal b1 v1) (IntVal b2 v2) = new_int b1 (v1 << shift_amount b1 v2)" |
  "intval_left_shift _ _ = UndefVal"

text \<open>Signed shift is more complex, because we sometimes have to insert 1 bits
  at the correct point, which is at b1 bits.\<close>
fun intval_right_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_right_shift (IntVal b1 v1) (IntVal b2 v2) = 
     (let shift = shift_amount b1 v2 in
      let ones = mask b1 AND (NOT (mask (b1 - shift) :: int64)) in
      (if int_signed_value b1 v1 < 0
       then new_int b1 (ones OR (v1 >>> shift))
       else new_int b1 (v1 >>> shift)))" |
  "intval_right_shift _ _ = UndefVal"

fun intval_uright_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_uright_shift (IntVal b1 v1) (IntVal b2 v2) = new_int b1 (v1 >>> shift_amount b1 v2)" |
  "intval_uright_shift _ _ = UndefVal"

end


section \<open>Examples of Narrowing / Widening Functions\<close>

experiment begin
corollary "intval_narrow 32 8 (IntVal 32 (256 + 128)) = IntVal 8 128" by simp
corollary "intval_narrow 32 8 (IntVal 32 (-2)) = IntVal 8 254" by simp
corollary "intval_narrow 32 1 (IntVal 32 (-2)) = IntVal 1 0"    by simp
corollary "intval_narrow 32 1 (IntVal 32 (-3)) = IntVal 1 1" by simp

(* now test some 64 bit inputs and outputs *)
corollary "intval_narrow 32 8 (IntVal 64 (-2)) = UndefVal" by simp
corollary "intval_narrow 64 8 (IntVal 32 (-2)) = UndefVal" by simp
corollary "intval_narrow 64 8 (IntVal 64 254) = IntVal 8 254" by simp
corollary "intval_narrow 64 8 (IntVal 64 (256+127)) = IntVal 8 127" by simp
corollary "intval_narrow 64 64 (IntVal 64 (-2)) = IntVal 64 (-2)" by simp
end

experiment begin
corollary "intval_sign_extend 8 32 (IntVal 8 (256 + 128)) = IntVal 32 (2^32 - 128)" by simp
corollary "intval_sign_extend 8 32 (IntVal 8 (-2)) = IntVal 32 (2^32 - 2)" by simp
corollary "intval_sign_extend 1 32 (IntVal 1 (-2)) = IntVal 32 0"    by simp
corollary "intval_sign_extend 1 32 (IntVal 1 (-3)) = IntVal 32 (mask 32)" by simp

(* now test some 64 bit inputs and outputs *)
corollary "intval_sign_extend 8 32 (IntVal 64 254) = UndefVal" by simp
corollary "intval_sign_extend 8 64 (IntVal 32 254) = UndefVal" by simp
corollary "intval_sign_extend 8 64 (IntVal 8 254) = IntVal 64 (-2)" by simp
corollary "intval_sign_extend 32 64 (IntVal 32 (2^32 - 2)) = IntVal 64 (-2)" by simp
corollary "intval_sign_extend 64 64 (IntVal 64 (-2)) = IntVal 64 (-2)" by simp
end


experiment begin
corollary "intval_zero_extend 8 32 (IntVal 8 (256 + 128)) = IntVal 32 128" by simp
corollary "intval_zero_extend 8 32 (IntVal 8 (-2)) = IntVal 32 254" by simp
corollary "intval_zero_extend 1 32 (IntVal 1 (-1)) = IntVal 32 1"   by simp
corollary "intval_zero_extend 1 32 (IntVal 1 (-2)) = IntVal 32 0"   by simp

(* now test some 64 bit inputs and outputs *)
corollary "intval_zero_extend 8 32 (IntVal 64 (-2)) = UndefVal" by simp
corollary "intval_zero_extend 8 64 (IntVal 64 (-2)) = UndefVal" by simp
corollary "intval_zero_extend 8 64 (IntVal 8 254) = IntVal 64 254" by simp
corollary "intval_zero_extend 32 64 (IntVal 32 (2^32 - 2)) = IntVal 64 (2^32 - 2)" by simp
corollary "intval_zero_extend 64 64 (IntVal 64 (-2)) = IntVal 64 (-2)" by simp
end

experiment begin
corollary "intval_right_shift (IntVal 8 128) (IntVal 8 0) = IntVal 8 128" by eval
corollary "intval_right_shift (IntVal 8 128) (IntVal 8 1) = IntVal 8 192" by eval
corollary "intval_right_shift (IntVal 8 128) (IntVal 8 2) = IntVal 8 224" by eval
corollary "intval_right_shift (IntVal 8 128) (IntVal 8 8) = IntVal 8 255" by eval
corollary "intval_right_shift (IntVal 8 128) (IntVal 8 31) = IntVal 8 255" by eval
end

(* ========================================================================
   Commutative and Associative results.  (Not used yet).
   ======================================================================== *)

(* commutative rules to be used when needed. *)
lemma intval_add_sym:
  shows "intval_add a b = intval_add b a"
  by (induction a; induction b; auto simp: add.commute)


code_deps intval_add  (* view dependency graph of code definitions *)
code_thms intval_add  (* print all code definitions used by intval_add *)


(* Some example tests. *)
lemma "intval_add (IntVal 32 (2^31-1)) (IntVal 32 (2^31-1)) = IntVal 32 (2^32 - 2)"
  by eval
lemma "intval_add (IntVal 64 (2^31-1)) (IntVal 64 (2^31-1)) = IntVal 64 4294967294"
  by eval

end