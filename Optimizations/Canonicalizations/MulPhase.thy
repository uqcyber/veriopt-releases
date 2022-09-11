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

(* Helper *)
lemma take_bit64[simp]: 
  fixes w :: "int64"
  shows "take_bit 64 w = w"
proof -
  have "Nat.size w = 64"
    by (simp add: size64)
  then show ?thesis
    by (metis lt2p_lem mask_eq_iff take_bit_eq_mask verit_comp_simplify1(2) wsst_TYs(3))
qed


(* TODO: merge this with val_eliminate_redundant_negative *)
lemma testt:
  fixes a :: "nat"
  fixes b c :: "64 word"
  shows "take_bit a (take_bit a (b) * take_bit a (c)) = 
         take_bit a (b * c)" 
 by (smt (verit, ccfv_SIG) take_bit_mult take_bit_of_int unsigned_take_bit_eq word_mult_def)


(* Value level proofs *)
lemma val_eliminate_redundant_negative:
  assumes "val[-x * -y] \<noteq> UndefVal"
  shows "val[-x * -y] = val[x * y]"
  using assms apply (cases x; cases y; auto)
  using testt by auto

lemma val_multiply_neutral:
  assumes "x = new_int b v"
  shows "val[x] * (IntVal b 1) = val[x]"
  using assms times_Value_def by force

lemma val_multiply_zero:
  assumes "x = new_int b v"
  shows "val[x] * (IntVal b 0) = IntVal b 0"
  using assms by (simp add: times_Value_def)

lemma val_multiply_negative:
  assumes "x = new_int b v"
  shows "x * intval_negate (IntVal b 1) = intval_negate x"
  using assms times_Value_def
  by (smt (verit) Value.disc(1) Value.inject(1) add.inverse_neutral intval_negate.simps(1) 
      is_IntVal_def mask_0 mask_eq_take_bit_minus_one new_int.elims of_bool_eq(2) take_bit_dist_neg 
      take_bit_of_1 val_eliminate_redundant_negative val_multiply_neutral val_multiply_zero 
      verit_minus_simplify(4) zero_neq_one)

(* x * 2^i = x << i*)
lemma val_MulPower2:
  fixes i :: "64 word"
  assumes "y = IntVal 64 (2 ^ unat(i))"
  and     "0 < i"
  and     "i < 64"
  and     "(63 :: int64) = mask 6"
  and     "val_to_bool(val[IntVal 64 0 < x])"
  and     "val_to_bool(val[IntVal 64 0 < y])"
  shows   "x * y = val[x << IntVal 64 i]"
  using assms apply (cases x; cases y; auto)
    apply (simp add: times_Value_def)
    subgoal premises p for x2
    proof -
      have 63: "(63 :: int64) = mask 6"
        using assms(4) by blast
      then have "(2::int) ^ 6 = 64"
        by eval
      then have "uint i < (2::int) ^ 6"
        by (smt (verit, ccfv_SIG) numeral_Bit0 of_int_numeral one_eq_numeral_iff p(6) uint_2p 
            word_less_def word_not_simps(1) word_of_int_2p)
      then have "and i (mask 6) = i"
        using mask_eq_iff by blast
      then show "x2 << unat i = x2 << unat (and i (63::64 word))"
        unfolding 63
        by force
    qed
    done

(*  x * ((2 ^ j) + 1) = (x << j) + x  *)
lemma val_MulPower2Add1:
  fixes i :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) + 1)"
  and     "0 < i"
  and     "i < 64"
  and     "val_to_bool(val[IntVal 64 0 < x])"
  and     "val_to_bool(val[IntVal 64 0 < y])"
  shows   "x * y = val[(x << IntVal 64 i) + x]"
  using assms apply (cases x; cases y; auto)
    apply (simp add: times_Value_def)
    subgoal premises p for x2
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2::int) ^ 6 = 64"
      by eval
    then have "and i (mask 6) = i"
      using mask_eq_iff by (simp add: less_mask_eq p(6))
    then have "x2 * ((2::64 word) ^ unat i + (1::64 word)) = (x2 * ((2::64 word) ^ unat i)) + x2"
      by (simp add: distrib_left)
    then show "x2 * ((2::64 word) ^ unat i + (1::64 word)) = x2 << unat (and i (63::64 word)) + x2"
      by (simp add: "63" \<open>and (i::64 word) (mask (6::nat)) = i\<close>)
    qed 
  done


(*  x * ((2 ^ j) - 1) = (x << j) - x  *)
lemma val_MulPower2Sub1:
  fixes i :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) - 1)"
  and     "0 < i"
  and     "i < 64"
  and     "val_to_bool(val[IntVal 64 0 < x])"
  and     "val_to_bool(val[IntVal 64 0 < y])"
  shows   "x * y = val[(x << IntVal 64 i) - x]"
  using assms apply (cases x; cases y; auto)
    apply (simp add: times_Value_def)
    subgoal premises p for x2
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2::int) ^ 6 = 64"
      by eval
    then have "and i (mask 6) = i"
      using mask_eq_iff by (simp add: less_mask_eq p(6))
    then have "x2 * ((2::64 word) ^ unat i - (1::64 word)) = (x2 * ((2::64 word) ^ unat i)) - x2"
      by (simp add: right_diff_distrib')
    then show "x2 * ((2::64 word) ^ unat i - (1::64 word)) = x2 << unat (and i (63::64 word)) - x2"
      by (simp add: "63" \<open>and (i::64 word) (mask (6::nat)) = i\<close>)
    qed 
  done

(* Helper *)
lemma val_distribute_multiplication:
  assumes "x = new_int 64 xx \<and> q = new_int 64 qq \<and> a = new_int 64 aa"
  shows "val[x * (q + a)] = val[(x * q) + (x * a)]"
  apply (cases x; cases q; cases a; auto) using distrib_left assms by auto


(*  x * ((2 ^ j) + (2 ^ k)) = (x << j) + (x << k)  *)
lemma val_MulPower2AddPower2:
  fixes i j :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) + (2 ^ unat(j)))"
  and     "0 < i"
  and     "0 < j"
  and     "i < 64"
  and     "j < 64"
  and     "x = new_int 64 xx"
  shows   "x * y = val[(x << IntVal 64 i) + (x << IntVal 64 j)]"
  using assms
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2::int) ^ 6 = 64"
      by eval
    then have n: "IntVal 64 ((2 ^ unat(i)) + (2 ^ unat(j))) = 
           val[(IntVal 64 (2 ^ unat(i))) + (IntVal 64 (2 ^ unat(j)))]"
       (* x * (2^i + 2^j)*)
      using assms by (cases i; cases j; auto) 
   then have "val[x * ((IntVal 64 (2 ^ unat(i))) + (IntVal 64 (2 ^ unat(j))))] = 
           val[(x * IntVal 64 (2 ^ unat(i))) + (x * IntVal 64 (2 ^ unat(j)))]"
      (* (x * 2^i) + (x * 2^j)*)
     using assms val_distribute_multiplication val_MulPower2 by simp 
   then have "val[(x * IntVal 64 (2 ^ unat(i)))] = val[x << IntVal 64 i]"
     using assms val_MulPower2  sorry
    then show "?thesis"
       sorry
    qed 

(* Exp-level proofs *)
lemma exp_multiply_zero_64:
 "exp[x * (const (IntVal 64 0))] \<ge> ConstantExpr (IntVal 64 0)"
  using val_multiply_zero apply auto 
  using Value.inject(1) constantAsStamp.simps(1) int_signed_value_bounds intval_mul.elims 
        mult_zero_right new_int.simps new_int_bin.simps nle_le numeral_eq_Suc take_bit_of_0 
        unfold_const valid_stamp.simps(1) valid_value.simps(1) zero_less_Suc
  by (smt (verit))

lemma exp_multiply_neutral:
 "exp[x * (const (IntVal b 1))] \<ge> x"
  using val_multiply_neutral apply auto  sorry

lemma exp_MulPower2:
  fixes i :: "64 word"
  assumes "y = ConstantExpr (IntVal 64 (2 ^ unat(i)))"
  and     "0 < i"
  and     "i < 64"
  shows "exp[x * y] \<ge> exp[x << ConstantExpr (IntVal 64 i)]"
  using assms val_MulPower2 
  sorry


(* Optimizations *)
optimization EliminateRedundantNegative: "-x * -y \<longmapsto> x * y"
   apply auto using val_eliminate_redundant_negative bin_eval.simps(2)
  by (metis BinaryExpr)

(* Need to prove exp_multiply_neutral *)
optimization MulNeutral: "x * ConstantExpr (IntVal b 1) \<longmapsto> x"
  using exp_multiply_neutral by blast

optimization MulEliminator: "x * ConstantExpr (IntVal b 0) \<longmapsto> const (IntVal b 0)"
  apply auto using val_multiply_zero
  using Value.inject(1) constantAsStamp.simps(1) int_signed_value_bounds intval_mul.elims 
        mult_zero_right new_int.simps new_int_bin.simps take_bit_of_0 unfold_const 
        valid_stamp.simps(1) valid_value.simps(1) 
  by (smt (verit))


optimization MulNegate: "x * -(const (IntVal b 1)) \<longmapsto> -x"
  apply auto using val_multiply_negative
  by (smt (verit) Value.distinct(1) Value.sel(1) add.inverse_inverse intval_mul.elims 
      intval_negate.simps(1) mask_eq_take_bit_minus_one new_int.simps new_int_bin.simps 
      take_bit_dist_neg times_Value_def unary_eval.simps(2) unfold_unary 
      val_eliminate_redundant_negative)

(* Need to prove exp_MulPower2 *)
optimization MulPower2: "x * y \<longmapsto> x << const (IntVal 64 i) 
                              when (i > 0 \<and> 64 > i \<and>
                                    y = (ConstantExpr (IntVal 64 (2 ^ unat(i)))))"
  defer
  using exp_MulPower2
   apply blast 
  sorry (* termination issues - mul needs to be considered larger than shift *)


end (* End of MulPhase *)

end (* End of file *)
