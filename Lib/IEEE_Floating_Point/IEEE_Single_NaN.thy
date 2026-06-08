(* Author: Tjark Weber, Uppsala University
*)

section \<open>Specification of the IEEE standard with a single NaN value\<close>

theory IEEE_Single_NaN
  imports
    IEEE_Properties
begin

text \<open>This theory defines a type of floating-point numbers that contains a single NaN value, much
  like specification level~2 of IEEE-754 (which does not distinguish between a quiet and a
  signaling NaN, nor between different bit representations of NaN).

  In contrast, the type @{typ \<open>('e, 'f) float\<close>} defined in {\tt IEEE.thy} may contain several
  distinct (bit) representations of NaN, much like specification level~4 of IEEE-754.

  One aim of this theory is to define a floating-point type (along with arithmetic operations) whose
  semantics agrees with the semantics of the SMT-LIB floating-point theory at
  \url{https://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml}. The following development
  therefore deviates from {\tt IEEE.thy} in some places to ensure alignment with the SMT-LIB
  theory.\<close>

text \<open>Note that we are using HOL equality (rather than IEEE-754 floating-point equality) in the
  following definition. This is because we do not want to identify~$+0$ and~$-0$.\<close>
definition is_nan_equivalent :: "('e, 'f) float \<Rightarrow> ('e, 'f) float \<Rightarrow> bool"
  where "is_nan_equivalent a b \<equiv> a = b \<or> (is_nan a \<and> is_nan b)"

quotient_type (overloaded) ('e, 'f) floatSingleNaN = "('e, 'f) float" / is_nan_equivalent
  by (metis equivpI is_nan_equivalent_def reflpI sympI transpI)

text \<open>Note that @{typ "('e, 'f) floatSingleNaN"} does not count the hidden bit in the significand.
  For instance, IEEE-754's double-precision binary floating point format {\tt binary64} corresponds
  to @{typ "(11,52) floatSingleNaN"}. The corresponding SMT-LIB sort is {\tt (\_ FloatingPoint 11 53)},
  where the hidden bit is counted.  Since the bit size is encoded as a type argument, and Isabelle/HOL
  does not permit arithmetic on type expressions, it would be difficult to resolve this difference
  without completely separating the definition of @{typ "('e, 'f) floatSingleNaN"} in this theory
  from the definition of @{typ "('e, 'f) float"} in IEEE.thy.\<close>

syntax "_floatSingleNaN" :: "type \<Rightarrow> type \<Rightarrow> type" ("'(_, _') floatSingleNaN")
text \<open>Parse \<open>('a, 'b) floatSingleNaN\<close> as \<open>('a::len, 'b::len) floatSingleNaN\<close>.\<close>

parse_translation \<open>
  let
    fun float t u = Syntax.const @{type_syntax floatSingleNaN} $ t $ u;
    fun len_tr u =
      (case Term_Position.strip_positions u of
        v as Free (x, _) =>
          if Lexicon.is_tid x then
            (Syntax.const @{syntax_const "_ofsort"} $ v $
              Syntax.const @{class_syntax len})
          else u
      | _ => u)
    fun len_float_tr [t, u] =
      float (len_tr t) (len_tr u)
  in
    [(@{syntax_const "_floatSingleNaN"}, K len_float_tr)]
  end
\<close>


subsection \<open>Value constructors\<close>

subsubsection \<open>FP literals as bit string triples, with the leading bit for the significand not
  represented (hidden bit)\<close>

lift_definition fp :: "1 word \<Rightarrow> 'e word \<Rightarrow> 'f word \<Rightarrow> ('e, 'f) floatSingleNaN"
  is "\<lambda>s e f. IEEE.Abs_float (s, e, f)" .

subsubsection \<open>Plus and minus infinity\<close>

lift_definition plus_infinity :: "('e, 'f) floatSingleNaN" ("\<infinity>") is IEEE.plus_infinity .

lift_definition minus_infinity :: "('e, 'f) floatSingleNaN" is IEEE.minus_infinity .

subsubsection \<open>Plus and minus zero\<close>

instantiation floatSingleNaN :: (len, len) zero begin

  lift_definition zero_floatSingleNaN :: "('a, 'b) floatSingleNaN" is 0 .

  instance ..

end

lift_definition minus_zero :: "('e, 'f) floatSingleNaN" is IEEE.minus_zero .

subsubsection \<open>Non-numbers (NaN)\<close>

lift_definition NaN :: "('e, 'f) floatSingleNaN" is some_nan .


subsection \<open>Operators\<close>

subsubsection \<open>Absolute value\<close>

setup \<open>Sign.mandatory_path "abs_floatSingleNaN_inst"\<close>  \<comment> \<open>workaround to avoid a duplicate fact declaration {\tt abs\_floatSingleNaN\_def} in lift\_definition below\<close>

instantiation floatSingleNaN :: (len, len) abs
begin

  lift_definition abs_floatSingleNaN :: "('a, 'b) floatSingleNaN \<Rightarrow> ('a, 'b) floatSingleNaN" is abs
    unfolding is_nan_equivalent_def by (metis IEEE.abs_float_def is_nan_uminus)

  instance ..

end

setup \<open>Sign.parent_path\<close>

subsubsection \<open>Negation (no rounding needed)\<close>

instantiation floatSingleNaN :: (len, len) uminus
begin

  lift_definition uminus_floatSingleNaN :: "('a, 'b) floatSingleNaN \<Rightarrow> ('a, 'b) floatSingleNaN" is uminus
    unfolding is_nan_equivalent_def by (metis is_nan_uminus)

  instance ..

end

subsubsection \<open>Addition\<close>

lift_definition fadd :: "roundmode \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN" is IEEE.fadd
  unfolding is_nan_equivalent_def by (metis IEEE.fadd_def)

subsubsection \<open>Subtraction\<close>

lift_definition fsub :: "roundmode \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN" is IEEE.fsub
  unfolding is_nan_equivalent_def by (metis IEEE.fsub_def)

subsubsection \<open>Multiplication\<close>

lift_definition fmul :: "roundmode \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN" is IEEE.fmul
  unfolding is_nan_equivalent_def by (metis IEEE.fmul_def)

subsubsection \<open>Division\<close>

lift_definition fdiv :: "roundmode \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN" is IEEE.fdiv
  unfolding is_nan_equivalent_def by (metis IEEE.fdiv_def)

subsubsection \<open>Fused multiplication and addition; $(x \cdot y) + z$\<close>

lift_definition fmul_add :: "roundmode \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN" is IEEE.fmul_add
  unfolding is_nan_equivalent_def by (smt (verit) IEEE.fmul_add_def)

subsubsection \<open>Square root\<close>

lift_definition fsqrt :: "roundmode \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN" is IEEE.fsqrt
  unfolding is_nan_equivalent_def by (metis IEEE.fsqrt_def)

subsubsection \<open>Remainder: $x - y \cdot n$, where $n \in \mathrm{Z}$ is nearest to $x/y$\<close>

lift_definition frem :: "roundmode \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN" is IEEE.frem
  unfolding is_nan_equivalent_def by (metis IEEE.frem_def)

lift_definition float_rem :: "('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN" is IEEE.float_rem
  unfolding is_nan_equivalent_def by (metis IEEE.frem_def IEEE.float_rem_def)

subsubsection \<open>Rounding to integral\<close>

lift_definition fintrnd :: "roundmode \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN" is IEEE.fintrnd
  unfolding is_nan_equivalent_def by (metis IEEE.fintrnd_def)

subsubsection \<open>Minimum and maximum\<close>

text \<open>In IEEE 754-2019, the minNum and maxNum operations of the 2008 version of the standard have
been replaced by minimum, minimumNumber, maximum, maximumNumber (see Section~9.6 of the 2019
standard). These are not (yet) available in SMT-LIB. We currently do not implement any of these
operations.\<close>

subsubsection \<open>Comparison operators\<close>

lift_definition fle :: "('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> bool" is IEEE.fle
  unfolding is_nan_equivalent_def by (smt (verit) IEEE.fcompare_def IEEE.fle_def)

lift_definition flt :: "('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> bool" is IEEE.flt
  unfolding is_nan_equivalent_def by (smt (verit) IEEE.fcompare_def IEEE.flt_def)

lift_definition fge :: "('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> bool" is IEEE.fge
  unfolding is_nan_equivalent_def by (smt (verit) IEEE.fcompare_def IEEE.fge_def)

lift_definition fgt :: "('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> bool" is IEEE.fgt
  unfolding is_nan_equivalent_def by (smt (verit) IEEE.fcompare_def IEEE.fgt_def)

subsubsection \<open>IEEE 754 equality\<close>

lift_definition feq :: "('e ,'f) floatSingleNaN \<Rightarrow> ('e ,'f) floatSingleNaN \<Rightarrow> bool" is IEEE.feq
  unfolding is_nan_equivalent_def by (smt (verit) IEEE.fcompare_def IEEE.feq_def)

subsubsection \<open>Classification of numbers\<close>

lift_definition is_normal :: "('e, 'f) floatSingleNaN \<Rightarrow> bool" is IEEE.is_normal
  unfolding is_nan_equivalent_def using float_distinct by blast

lift_definition is_subnormal :: "('e, 'f) floatSingleNaN \<Rightarrow> bool" is IEEE.is_denormal
  unfolding is_nan_equivalent_def using float_distinct by blast

lift_definition is_zero :: "('e, 'f) floatSingleNaN \<Rightarrow> bool" is IEEE.is_zero
  unfolding is_nan_equivalent_def using float_distinct by blast

lift_definition is_infinity :: "('e, 'f) floatSingleNaN \<Rightarrow> bool" is IEEE.is_infinity
  unfolding is_nan_equivalent_def using float_distinct by blast

lift_definition is_nan :: "('e, 'f) floatSingleNaN \<Rightarrow> bool" is IEEE.is_nan
  unfolding is_nan_equivalent_def by blast

lift_definition is_finite :: "('e, 'f) floatSingleNaN \<Rightarrow> bool" is IEEE.is_finite
  unfolding is_nan_equivalent_def using nan_not_finite by blast

definition is_negative :: "('e, 'f) floatSingleNaN \<Rightarrow> bool"
  where "is_negative x \<equiv> x = minus_zero \<or> flt x minus_zero"

definition is_positive :: "('e, 'f) floatSingleNaN \<Rightarrow> bool"
  where "is_positive x \<equiv> x = 0 \<or> flt 0 x"


subsection \<open>Conversions to other sorts\<close>

subsubsection \<open>to real\<close>

text \<open>SMT-LIB leaves {\tt fp.to\_real} unspecified for $+\infty$, $-\infty$, NaN. In contrast,
@{const valof} is (partially) specified also for those arguments. This means that the SMT-LIB
semantics can prove fewer theorems about {\tt fp.to\_real} than Isabelle can prove about
@{const valof}.\<close>

lift_definition valof :: "('e,'f) floatSingleNaN \<Rightarrow> real"
  is "\<lambda>a. if IEEE.is_infinity a then undefined a
            else if IEEE.is_nan a then undefined  \<comment> \<open>returning the same value for all floats that satisfy @{const IEEE.is_nan} is necessary to obtain a function that can be lifted to the quotient type\<close>
            else IEEE.valof a"
  unfolding is_nan_equivalent_def using float_distinct(1) by fastforce

subsubsection \<open>to unsigned machine integer, represented as a bit vector\<close>

definition unsigned_word_of_floatSingleNaN :: "roundmode \<Rightarrow> ('e,'f) floatSingleNaN \<Rightarrow> 'a::len word"
  where "unsigned_word_of_floatSingleNaN mode a \<equiv>
    if is_infinity a \<or> is_nan a then undefined mode a
      else (SOME w. valof (fintrnd mode a) = real_of_word w)"

subsubsection \<open>to signed machine integer, represented as a 2's complement bit vector\<close>

definition signed_word_of_floatSingleNaN :: "roundmode \<Rightarrow> ('e,'f) floatSingleNaN \<Rightarrow> 'a::len word"
  where "signed_word_of_floatSingleNaN mode a \<equiv>
    if is_infinity a \<or> is_nan a then undefined mode a
      else (SOME w. valof (fintrnd mode a) = real_of_int (sint w))"


subsection \<open>Conversions from other sorts\<close>

subsubsection \<open>from single bitstring representation in IEEE 754 interchange format\<close>

text \<open>The intention is that @{prop \<open>LENGTH('a::len) = 1 + LENGTH('e::len) + LENGTH('f::len)\<close>}
  (recall that @{term \<open>LENGTH('f::len)\<close>} does not include the significand's hidden bit). Of course,
  the type system of Isabelle/HOL is not strong enough to enforce this.\<close>

definition floatSingleNaN_of_IEEE754_word :: "'a::len word \<Rightarrow> ('e,'f) floatSingleNaN"
  where "floatSingleNaN_of_IEEE754_word w \<equiv>
    let (se, f) = word_split w :: 'a word \<times> _; (s, e) = word_split se in fp s e f"  \<comment> \<open>using @{typ \<open>'a word\<close>} ensures that no bits are lost in @{term \<open>se\<close>}\<close>

subsubsection \<open>from real\<close>

lift_definition round :: "roundmode \<Rightarrow> real \<Rightarrow> ('e,'f) floatSingleNaN" is IEEE.round .

subsubsection \<open>from another floating point sort\<close>

definition floatSingleNaN_of_floatSingleNaN :: "roundmode \<Rightarrow> ('a,'b) floatSingleNaN \<Rightarrow> ('e,'f) floatSingleNaN"
  where "floatSingleNaN_of_floatSingleNaN mode a \<equiv>
    if a = plus_infinity then plus_infinity
      else if a = minus_infinity then minus_infinity
      else if a = NaN then NaN
      else round mode (valof a)"

subsubsection \<open>from signed machine integer, represented as a 2's complement bit vector\<close>

definition floatSingleNaN_of_signed_word :: "roundmode \<Rightarrow> 'a::len word \<Rightarrow> ('e,'f) floatSingleNaN"
  where "floatSingleNaN_of_signed_word mode w \<equiv> round mode (real_of_int (sint w))"

subsubsection \<open>from unsigned machine integer, represented as bit vector\<close>

definition floatSingleNaN_of_unsigned_word :: "roundmode \<Rightarrow> 'a::len word \<Rightarrow> ('e,'f) floatSingleNaN"
  where "floatSingleNaN_of_unsigned_word mode w \<equiv> round mode (real_of_word w)"

end
