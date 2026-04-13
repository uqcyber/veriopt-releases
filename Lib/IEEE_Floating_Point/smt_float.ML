(*  Title:      IEEE_Floating_Point/smt_float.ML
    Author:     Olle Torstensson, Uppsala University
    Author:     Tjark Weber, Uppsala University

SMT setup for floating-points.

This file provides an interpretation of floating-point related types and constants found in
IEEE_Floating_Point/IEEE_Single_NaN.thy into SMT-LIB. The interpretation encompasses
  - fixed format floating-point types,
  - the rounding mode type,
  - floating-point value construction from bit vector triples,
  - special floating-point values (+/- 0, +/- infinity, and NaN),
  - rounding modes,
  - classification operations,
  - arithmetic operations,
  - comparison operations,
  - type conversions to and from the reals, and
  - type conversions to and from bit-vector representations.

The interpretation does NOT cover polymorphic floating-point types. Variables and constants with a
floating-point type will in general need to be attached with explicit type constraints in order to
trigger the interpretation.
*)

structure SMT_Float: sig end =
struct

(*Determine whether a type is a word type of a fixed format supported by SMT-LIB.*)
fun is_word (Type (\<^type_name>\<open>Word.word\<close>, [a])) =
      can Word_Lib.dest_binT a andalso Word_Lib.dest_binT a > 0
  | is_word _ = false

(*Determine whether a type is a floating-point type of a fixed format supported by SMT-LIB.*)
fun is_float (Type (\<^type_name>\<open>IEEE_Single_NaN.floatSingleNaN\<close>, [e,f])) =
      can (apply2 Word_Lib.dest_binT) (e,f) andalso
      Word_Lib.dest_binT e > 1 andalso
      Word_Lib.dest_binT f > 0  \<comment> \<open>SMT-LIB requires e>1 and f>1 but counts the significand's hidden bit in f\<close>
  | is_float _ = false

(*Extract type argument from word types of fixed formats.*)
fun word_Targ (T as (Type (\<^type_name>\<open>Word.word\<close>, [a]))) =
      if is_word T then
        SOME (Word_Lib.dest_binT a)
      else
        NONE
  | word_Targ _ = NONE

(*Extract type arguments from floating-point types of fixed formats.*)
fun float_Targs (T as (Type (\<^type_name>\<open>IEEE_Single_NaN.floatSingleNaN\<close>, [e,f]))) =
      if is_float T then
        SOME (Word_Lib.dest_binT e, Word_Lib.dest_binT f)
      else
        NONE
  | float_Targs _ = NONE

(*True except for floating-point and word types of unsupported formats.*)
fun is_valid_type (T as (Type (\<^type_name>\<open>IEEE_Single_NaN.floatSingleNaN\<close>, _))) = is_float T
  | is_valid_type (T as (Type (\<^type_name>\<open>Word.word\<close>, _))) = is_word T
  | is_valid_type _ = true


(* SMT-LIB logic *)

(*
  SMT-LIB logics are generally too restrictive for Isabelle's problems. "ALL" denotes the most
  general logic supported by the SMT solver, and is chosen if a rounding mode or supported
  floating-point type is encountered among the terms. Isabelle's SMTLIB_Interface unfortunately
  does not provide a modular way to indicate that a problem requires the floating-point (FP) theory.
*)
fun smtlib_logic _ ts =
  let
    fun is_float_or_rm (Type (\<^type_name>\<open>IEEE.roundmode\<close>, _)) = true
      | is_float_or_rm T = is_float T
  in
    if exists (Term.exists_type (Term.exists_subtype is_float_or_rm)) ts then
      SOME "ALL" (*FIXME: There are currently three SMT solvers available in Isabelle: cvc4, verit,
                          and z3. verit currently does not support the FP theory at all. z3
                          currently does not support the "ALL" logic but ignores it gracefully.*)
    else
      NONE
  end


(* SMT-LIB built-ins *)

(*Interpret floating-point related types and constants supported by the SMT-LIB floating-point theory.*)
local

  (*SMT-LIB syntax template for parameterized sorts and functions.*)
  fun param_template1 s a =
  	"(_ " ^ s ^ " " ^ string_of_int a ^ ")"

  fun param_template2 s (e,f) =
  	"(_ " ^ s ^ " " ^ string_of_int e ^ " " ^ string_of_int (f + 1) ^ ")"

  fun word_typ T = Option.map (rpair [] o param_template1 "BitVec") (word_Targ T)

  fun float_typ T = Option.map (rpair [] o param_template2 "FloatingPoint") (float_Targs T)

  (*
    Generic function for interpreting floating-point constants.
    f can be used to customize the interpretation.
  *)
  fun add_float_fun f (t, s) =
    let
      val (n, _) = Term.dest_Const t
    in
      (*FIXME: It would be preferable to add the floating-point types and functions only for those
               SMT solvers that support them (currently, cvc4 and z3). However, doing this in a
               modular way would require a change to the solver interface specifications (in
               isabelle/src/HOL/Tools/SMT/). *)
      SMT_Builtin.add_builtin_fun SMTLIB_Interface.smtlibC (Term.dest_Const t, f n s)
    end

  (*Customized interpretation. Check whether the type is supported and add two type arguments
    extracted from the result type.*)
  fun add_with_Targs n s _ T ts =
    let
      val (Us, U) = Term.strip_type T
      val all_valid = forall is_valid_type (U::Us)
    in
      case (all_valid, float_Targs U) of
        (true, SOME args) =>
          SOME (param_template2 s args, length Us, ts, Term.list_comb o pair (Const (n, T)))
      | _ => NONE
    end

  (*Customized interpretation. Check whether the type is supported and add one type argument
    extracted from the result type.*)
  fun add_with_Targ n s _ T ts =
    let
      val (Us, U) = Term.strip_type T
      val all_valid = forall is_valid_type (U::Us)
    in
      case (all_valid, word_Targ U) of
        (true, SOME arg) =>
          SOME (param_template1 s arg, length Us, ts, Term.list_comb o pair (Const (n, T)))
      | _ => NONE
    end

  (*Customized interpretation. Check whether the type is supported.*)
  fun add_if_fixed n s _ T ts =
    let
      val (Us, U) = Term.strip_type T
      val all_valid = forall is_valid_type (U::Us)
    in
      if all_valid then
        SOME (s, length Us, ts, Term.list_comb o pair (Const (n, T)))
      else
        NONE
    end

in

val setup_builtins =

  (*Types*)
  fold (SMT_Builtin.add_builtin_typ SMTLIB_Interface.smtlibC) [
    (\<^typ>\<open>('a::len) Word.word\<close>, word_typ, K (K NONE)),
    (\<^typ>\<open>('e::len,'f::len) IEEE_Single_NaN.floatSingleNaN\<close>, float_typ, K (K NONE)),
    (\<^typ>\<open>IEEE.roundmode\<close>, K (SOME ("RoundingMode", [])), K (K NONE))] #>

  (*Rounding modes*)
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (@{const IEEE.roundNearestTiesToEven}, "RNE"),
    (@{const IEEE.roundTowardPositive}, "RTP"),
    (@{const IEEE.roundTowardNegative}, "RTN"),
    (@{const IEEE.roundTowardZero}, "RTZ"),
    (@{const IEEE.roundNearestTiesToAway}, "RNA")] #>

  (*Value constructors*)
  add_float_fun add_if_fixed
    (@{const IEEE_Single_NaN.fp (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp") #>
  fold (add_float_fun add_with_Targs) [
    (@{const IEEE_Single_NaN.plus_infinity (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "+oo"),
    (@{const IEEE_Single_NaN.minus_infinity (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "-oo"),
    (@{const zero_class.zero (\<open>('e::len,'f::len) IEEE_Single_NaN.floatSingleNaN\<close>)}, "+zero"),
    (@{const IEEE_Single_NaN.minus_zero (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "-zero"),
    (@{const IEEE_Single_NaN.NaN (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "NaN")] #>

  (*Operators*)
  fold (add_float_fun add_if_fixed) [
  (*arithmetic operators*)
    (@{const abs_class.abs (\<open>('e::len,'f::len) IEEE_Single_NaN.floatSingleNaN\<close>)}, "fp.abs"),
    (@{const uminus_class.uminus (\<open>('e::len,'f::len) IEEE_Single_NaN.floatSingleNaN\<close>)}, "fp.neg"),
    (@{const IEEE_Single_NaN.fadd (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.add"),
    (@{const IEEE_Single_NaN.fsub (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.sub"),
    (@{const IEEE_Single_NaN.fmul (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.mul"),
    (@{const IEEE_Single_NaN.fdiv (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.div"),
    (@{const IEEE_Single_NaN.fmul_add (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.fma"),
    (@{const IEEE_Single_NaN.fsqrt (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.sqrt"),
    (@{const IEEE_Single_NaN.float_rem (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.rem"),
    (@{const IEEE_Single_NaN.fintrnd (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.roundToIntegral"),
  (*comparison operators, IEEE 754 equality*)
    (@{const IEEE_Single_NaN.fle (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.leq"),
    (@{const IEEE_Single_NaN.flt (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.lt"),
    (@{const IEEE_Single_NaN.fge (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.geq"),
    (@{const IEEE_Single_NaN.fgt (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.gt"),
    (@{const IEEE_Single_NaN.feq (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.eq"),
  (*classification of numbers*)
    (@{const IEEE_Single_NaN.is_normal (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isNormal"),
    (@{const IEEE_Single_NaN.is_subnormal (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isSubnormal"),
    (@{const IEEE_Single_NaN.is_zero (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isZero"),
    (@{const IEEE_Single_NaN.is_infinity (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isInfinite"),
    (@{const IEEE_Single_NaN.is_nan (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isNaN"),
    (@{const IEEE_Single_NaN.is_negative (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isNegative"),
    (@{const IEEE_Single_NaN.is_positive (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.isPositive"),
  (*conversions to other types*)
    (@{const IEEE_Single_NaN.valof (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "fp.to_real")] #>
  fold (add_float_fun add_with_Targ) [
    (@{const IEEE_Single_NaN.unsigned_word_of_floatSingleNaN (\<open>'e::len\<close>,\<open>'f::len\<close>,\<open>'a::len\<close>)}, "fp.to_ubv"),
    (@{const IEEE_Single_NaN.signed_word_of_floatSingleNaN (\<open>'e::len\<close>,\<open>'f::len\<close>,\<open>'a::len\<close>)}, "fp.to_sbv")] #>
  (*conversions from other types*)
  fold (add_float_fun add_with_Targs) [
    (@{const IEEE_Single_NaN.floatSingleNaN_of_IEEE754_word (\<open>'a::len\<close>,\<open>'e::len\<close>,\<open>'f::len\<close>)}, "to_fp"),  (*FIXME: interpret only if a=e+f+1*)
    (@{const IEEE_Single_NaN.round (\<open>'e::len\<close>,\<open>'f::len\<close>)}, "to_fp"),
    (@{const IEEE_Single_NaN.floatSingleNaN_of_floatSingleNaN (\<open>'a::len\<close>,\<open>'b::len\<close>,\<open>'a::len\<close>,\<open>'b::len\<close>)}, "to_fp"),
    (@{const IEEE_Single_NaN.floatSingleNaN_of_signed_word (\<open>'a::len\<close>,\<open>'e::len\<close>,\<open>'f::len\<close>)}, "to_fp"),
    (@{const IEEE_Single_NaN.floatSingleNaN_of_unsigned_word (\<open>'a::len\<close>,\<open>'e::len\<close>,\<open>'f::len\<close>)}, "to_fp_unsigned")]

end


(* Setup *)

(*Override any other logic.*)
val _ = Theory.setup (Context.theory_map (
    SMTLIB_Interface.add_logic (0, smtlib_logic) #>
    setup_builtins
  ))

end;
