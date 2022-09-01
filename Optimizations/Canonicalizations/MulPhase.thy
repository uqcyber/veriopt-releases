theory MulPhase
  imports
    Common
begin

section \<open>Optimizations for Mul Nodes\<close>

phase MulNode
  terminating size
begin

(* Word level proofs *)
lemma bin_eliminate_redundant_negative:
  "uminus (x :: 'a::len word) * uminus (y :: 'a::len word) = x * y"
  by simp

lemma bin_multiply_identity:
 "(x :: 'a::len word) * 1 = x"
  by simp

lemma bin_multiply_eliminate:
 "(x :: 'a::len word) * 0 = 0"
  by simp

lemma bin_multiply_negative:
 "(x :: 'a::len word) * uminus 1 = uminus x"
  by simp

lemma bin_multiply_power_2:
 "(x:: 'a::len word) * (2^j) = x << j"
  by simp

(* Value level proofs *)
lemma val_eliminate_redundant_negative:
  assumes "val[-x * -y] \<noteq> UndefVal"
  shows "val[-x * -y] = val[x * y]"
  using assms
  apply (cases x; cases y; auto) sorry

lemma val_multiply_neutral:
  assumes "x = new_int b v"
  shows "val[x] *  (IntVal b 1) = val[x]"
  using assms times_Value_def by force

lemma val_multiply_zero:
  assumes "x = new_int b v"
  shows "val[x] * (IntVal b 0) = IntVal b 0"
  using assms
  by (simp add: times_Value_def)

lemma val_multiply_negative:
  assumes "x = new_int b v"
  shows "x * intval_negate (IntVal b 1) = intval_negate x"
  using assms times_Value_def
  by (smt (verit) Value.disc(1) Value.inject(1) add.inverse_neutral intval_negate.simps(1) is_IntVal_def mask_0 mask_eq_take_bit_minus_one new_int.elims of_bool_eq(2) take_bit_dist_neg take_bit_of_1 val_eliminate_redundant_negative val_multiply_neutral val_multiply_zero verit_minus_simplify(4) zero_neq_one)

(* Borrowed from ShiftPhase *)
fun intval_log2 :: "Value \<Rightarrow> Value" where
  "intval_log2 (IntVal b v) = IntVal b (word_of_int (SOME e. v=2^e))" |
  "intval_log2 _ = UndefVal" 

(*
fun intval_log2_2 :: "Value \<Rightarrow> Value" where
  "intval_log2_2 (IntVal32 v) = (if v=2^e then IntVal32 (word_of_int(e)) else UndefVal)" |
  "intval_log2_2 (IntVal64 v) = (if v=2^e then IntVal32 (word_of_int(e)) else UndefVal)" |
  "intval_log2_2 _ = UndefVal" 
*)

lemma largest_32:
  assumes "y = IntVal 32 (4294967296) \<and> i = intval_log2 y"
  shows "val_to_bool(val[i < IntVal 32 (32)])"
  using assms apply (cases y; auto)
  sorry

(* Proving that (log2 (2^i)) < 32 when 2^i \<in> IntVal32 *)
lemma log2_range:
  assumes "y = IntVal 32 v \<and> intval_log2 y = i"
  shows "val_to_bool (val[i < IntVal 32 (32)])"
  using assms apply (cases y; cases i; auto)
  sorry

lemma val_multiply_power_2_last_subgoal:
  assumes "y = IntVal 32 yy"
  and     "x = IntVal 32 xx" 
  and     "val_to_bool (val[IntVal 32 0 < x])"
  and     "val_to_bool (val[IntVal 32 0 < y])" 

  shows "x * y = IntVal 32 (xx << unat (and (word_of_nat (SOME e. yy = 2^e)) 31))"
  using intval_left_shift.simps(1) assms apply (cases x; cases y; auto) 
  sorry

value "IntVal 32 x2 * IntVal 32 x2a"
value "IntVal 32 (x2 << unat (and (word_of_nat (SOME e. x2a = 2^e)) 31))"

value "val[(IntVal 32 2) * (IntVal 32 4)]"
value "val[(IntVal 32 2) << (IntVal 32 2)]"
value "IntVal 32 (2 << unat (and (2::32 word) (31::32 word)))"

(* Need to prove lemma above *)
lemma val_multiply_power_2_2:
  assumes "y = IntVal 32 v"
  and     "intval_log2 y = i"                          (*  y = 2^i  *)
  and     "val_to_bool (val[IntVal 32 0 < i])"          (*  i > 0    *)
  and     "val_to_bool (val[i < IntVal 32 32])"         (*  32 > i   *)
  and     "val_to_bool (val[IntVal 32 0 < x])"          (*  x > 0    *)
  and     "val_to_bool (val[IntVal 32 0 < y])"          (*  y > 0    *)

shows "x * y = val[x << i]"
  using assms apply (cases x; cases y; auto) 
  apply (simp add: times_Value_def) 
  using times_Value_def assms sorry

lemma val_multiply_power_2:
  fixes j :: "64 word"
  assumes "x = IntVal 32 v \<and> j \<ge> 0 \<and> j_AsNat = (sint (intval_word (IntVal 32 j)))"
  shows "x * IntVal 32 (2 ^ j_AsNat) = intval_left_shift x (IntVal 32 j)"
  using assms apply (cases x; cases j; cases j_AsNat; auto)
  sorry

(* Exp-level proofs *)
lemma exp_multiply_zero_64:
 "exp[x * (const (IntVal 64 0))] \<ge> ConstantExpr (IntVal 64 0)"
  using val_multiply_zero apply auto 
  using Value.inject(1) constantAsStamp.simps(1) int_signed_value_bounds intval_mul.elims mult_zero_right new_int.simps new_int_bin.simps nle_le numeral_eq_Suc take_bit_of_0 unfold_const valid_stamp.simps(1) valid_value.simps(1) zero_less_Suc
  by (smt (verit))

(* Optimizations *)
optimization EliminateRedundantNegative: "-x * -y \<longmapsto> x * y"
   apply auto using val_eliminate_redundant_negative bin_eval.simps(2)
  by (metis BinaryExpr)


optimization MulNeutral: "x * ConstantExpr (IntVal b 1) \<longmapsto> x"
    apply auto using val_multiply_neutral bin_eval.simps(2)  sorry (*
  by (smt (z3) Value.discI(1) Value.distinct(9) intval_mul.elims times_Value_def)*)


optimization MulEliminator: "x * ConstantExpr (IntVal b 0) \<longmapsto> const (IntVal b 0)"
  apply auto using val_multiply_zero
  using Value.inject(1) constantAsStamp.simps(1) int_signed_value_bounds intval_mul.elims mult_zero_right new_int.simps new_int_bin.simps take_bit_of_0 unfold_const valid_stamp.simps(1) valid_value.simps(1) 
  by (smt (verit))

(* Size issue *)
optimization MulNegate: "x * -(const (IntVal b 1)) \<longmapsto> -x"
  apply auto using val_multiply_negative
  by (smt (verit) Value.distinct(1) Value.sel(1) add.inverse_inverse intval_mul.elims intval_negate.simps(1) mask_eq_take_bit_minus_one new_int.simps new_int_bin.simps take_bit_dist_neg times_Value_def unary_eval.simps(2) unfold_unary val_eliminate_redundant_negative)


end (* End of MulPhase *)

lemma take_bit64[simp]: 
  fixes w :: "int64"
  shows "take_bit 64 w = w"
proof -
  have "Nat.size w = 64"
    by (simp add: size64)
  then show ?thesis
    by (metis lt2p_lem mask_eq_iff take_bit_eq_mask verit_comp_simplify1(2) wsst_TYs(3))
qed


lemma jazmin:
  fixes i :: "64 word"
  assumes "y = IntVal 64 (2 ^ unat(i))"
  and "0 < i"
  and "i < 64"
  and "(63 :: int64) = mask 6"
  and "val_to_bool(val[IntVal 64 0 < x])"
  and "val_to_bool(val[IntVal 64 0 < y])"
  shows "x*y = val[x << IntVal 64 i]"
  using assms apply (cases x; cases y; auto)
    apply (simp add: times_Value_def)
    subgoal premises p for x2
    proof -
      have 63: "(63 :: int64) = mask 6"
        using assms(4) by blast
      then have "(2::int) ^ 6 = 64"
        by eval
      then have "uint i < (2::int) ^ 6"
        by (smt (verit, ccfv_SIG) numeral_Bit0 of_int_numeral one_eq_numeral_iff p(6) uint_2p word_less_def word_not_simps(1) word_of_int_2p)
      then have "and i (mask 6) = i"
        using mask_eq_iff by blast
      then show "x2 << unat i = x2 << unat (and i (63::64 word))"
        unfolding 63
        by force
    qed
  done



end (* End of file *)
