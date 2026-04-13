(* Author: Tjark Weber, Uppsala University
*)

section \<open>Translation of the IEEE model (with a single NaN value) into SMT-LIB's floating point theory\<close>

theory IEEE_Single_NaN_SMTLIB
  imports
    IEEE_Single_NaN
begin

text \<open>SMT setup. Note that an interpretation of floating-point arithmetic in SMT-LIB allows external
  SMT solvers that support the SMT-LIB floating-point theory to find more proofs, but---in the
  absence of built-in floating-point automation in Isabelle/HOL---significantly \emph{reduces}
  Sledgehammer's proof reconstruction rate. Until such automation becomes available, you probably
  want to use the interpreted translation only if you intend to use the external SMT solvers as
  trusted oracles.\<close>
ML_file \<open>smt_float.ML\<close>

end
