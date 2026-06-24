subsection \<open>MulNode Phase\<close>

theory MulPhase
  imports
    Common
    Proofs.StampEvalThms
begin

fun mul_size :: "IRExpr \<Rightarrow> nat" where
  "mul_size (UnaryExpr op e) = (mul_size e) + 2" |
  "mul_size (BinaryExpr BinMul x y) = ((mul_size x) + (mul_size y) + 2) * 3" |
  "mul_size (BinaryExpr op x y) = (mul_size x) + (mul_size y) + 2" |
  "mul_size (ConditionalExpr cond t f) = (mul_size cond) + (mul_size t) + (mul_size f) + 2" |
  "mul_size (ConstantExpr c) = 1" |
  "mul_size (ParameterExpr ind s) = 2" |
  "mul_size (LeafExpr nid s) = 2" |
  "mul_size (ConstantVar c) = 2" |
  "mul_size (VariableExpr x s) = 2"

phase MulNode
  terminating mul_size
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
  by (cases x; cases y; auto simp: mergeTakeBit)

lemma val_multiply_neutral:
  assumes "x = new_int b v"
  shows "val[x * (IntVal b 1)] = x"
  by (auto simp: assms)

lemma val_multiply_zero:
  assumes "x = new_int b v"
  shows "val[x * (IntVal b 0)] = IntVal b 0"
  by (simp add: assms)

lemma val_multiply_negative:
  assumes "x = new_int b v"
  shows "val[x * -(IntVal b 1)] = val[-x]"
  using assms apply auto by (metis bin_multiply_negative mergeTakeBit take_bit_minus_one_eq_mask)

(* x * 2^i = x << i*)
lemma val_MulPower2:
  fixes i :: "64 word"
  assumes "y = IntVal 64 (2 ^ unat(i))"
  and     "0 < i"
  and     "i < 64"
  and     "val[x * y] \<noteq> UndefVal"
  shows   "val[x * y] = val[x << IntVal 64 i]"
  using assms apply (cases x; cases y; auto)
    subgoal premises p for x2
    proof -
      have 63: "(63 :: int64) = mask 6"
        by eval
      then have "(2::int) ^ 6 = 64"
        by eval
      then have "uint i < (2::int) ^ 6"
        by (metis linorder_not_less lt2p_lem of_int_numeral p(4) word_2p_lem word_of_int_2p 
            wsst_TYs(3))
      then have "and i (mask 6) = i"
        using mask_eq_iff by blast
      then show "x2 << unat i = x2 << unat (and i (63::64 word))"
        by (auto simp: 63)
    qed
  by presburger

(*  x * ((2 ^ j) + 1) = (x << j) + x  *)
lemma val_MulPower2Add1:
  fixes i :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) + 1)"
  and     "0 < i"
  and     "i < 64"
  and     "val_to_bool(val[IntVal 64 0 < x])"
  and     "val_to_bool(val[IntVal 64 0 < y])"
  shows   "val[x * y] = val[(x << IntVal 64 i) + x]"
  using assms apply (cases x; cases y; auto)
    subgoal premises p for x2
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2 :: int) ^ 6 = 64"
      by eval
    then have "and i (mask 6) = i"
      by (simp add: less_mask_eq p(6))
    then have "x2 * (2 ^ unat i + 1) = (x2 * (2 ^ unat i)) + x2"
      by (simp add: distrib_left)
    then show "x2 * (2 ^ unat i + 1) = x2 << unat (and i 63) + x2"
      by (simp add: "63" \<open>and i (mask 6) = i\<close>)
    qed 
  using val_to_bool.simps(2) by presburger

(*  x * ((2 ^ j) - 1) = (x << j) - x  *)
lemma val_MulPower2Sub1:
  fixes i :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) - 1)"
  and     "0 < i"
  and     "i < 64"
  and     "val_to_bool(val[IntVal 64 0 < x])"
  and     "val_to_bool(val[IntVal 64 0 < y])"
  shows   "val[x * y] = val[(x << IntVal 64 i) - x]"
  using assms apply (cases x; cases y; auto)
    subgoal premises p for x2
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2 :: int) ^ 6 = 64"
      by eval
    then have "and i (mask 6) = i"
      by (simp add: less_mask_eq p(6))
    then have "x2 * (2 ^ unat i - 1) = (x2 * (2 ^ unat i)) - x2"
      by (simp add: right_diff_distrib')
    then show "x2 * (2 ^ unat i - 1) = x2 << unat (and i 63) - x2"
      by (simp add: "63" \<open>and i (mask 6) = i\<close>)
    qed 
  using val_to_bool.simps(2) by presburger

(* Value level helpers *)
lemma val_distribute_multiplication:
  assumes "x = IntVal b xx \<and> q = IntVal b qq \<and> a = IntVal b aa"
  assumes "val[x * (q + a)] \<noteq> UndefVal"
  assumes "val[(x * q) + (x * a)] \<noteq> UndefVal"
  shows "val[x * (q + a)] = val[(x * q) + (x * a)]"
  using assms apply (cases x; cases q; cases a; auto) 
  by (metis (no_types, opaque_lifting) distrib_left new_int.elims new_int_unused_bits_zero
      mergeTakeBit)

lemma val_distribute_multiplication64:
  assumes "x = new_int 64 xx \<and> q = new_int 64 qq \<and> a = new_int 64 aa"
  shows "val[x * (q + a)] = val[(x * q) + (x * a)]"
  using assms apply (cases x; cases q; cases a; auto) using distrib_left by blast

(*  x * ((2 ^ j) + (2 ^ k)) = (x << j) + (x << k)  *)
lemma val_MulPower2AddPower2:
  fixes i j :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) + (2 ^ unat(j)))"
  and     "0 < i"
  and     "0 < j"
  and     "i < 64"
  and     "j < 64"
  and     "x = new_int 64 xx"
  shows   "val[x * y] = val[(x << IntVal 64 i) + (x << IntVal 64 j)]"
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2 :: int) ^ 6 = 64"
      by eval
    then have n: "IntVal 64 ((2 ^ unat(i)) + (2 ^ unat(j))) = 
             val[(IntVal 64 (2 ^ unat(i))) + (IntVal 64 (2 ^ unat(j)))]"
       (* x * (2^i + 2^j)*)
      by auto
   then have 1: "val[x * ((IntVal 64 (2 ^ unat(i))) + (IntVal 64 (2 ^ unat(j))))] = 
                 val[(x * IntVal 64 (2 ^ unat(i))) + (x * IntVal 64 (2 ^ unat(j)))]"
      (* (x * 2^i) + (x * 2^j)*)
     using assms val_distribute_multiplication64 by simp 
   then have 2: "val[(x * IntVal 64 (2 ^ unat(i)))] = val[x << IntVal 64 i]"
     by (metis (no_types, opaque_lifting) Value.distinct(1) intval_mul.simps(1) new_int.simps
         new_int_bin.simps assms(2,4,6) val_MulPower2)
   then show "?thesis" 
     by (metis (no_types, lifting) "1" Value.distinct(1) n intval_mul.simps(1) new_int_bin.elims
         new_int.simps val_MulPower2 assms(1,3,5,6))
   qed

thm_oracles val_MulPower2AddPower2

lemma val_mul_power_2_add_power_2_64:
  assumes "x = new_int b xv"
  assumes "y = new_int b yv"
  assumes "bitCount yv = 2"
  assumes "lhs = val[x << (val_top_bit y)]"
  assumes "rhs = val[x << (val_bot_bit y)]"
  assumes "b = 64"
  shows "val[x * y] = val[lhs + rhs]"
proof -
  have distribute: "xv * yv = xv << (topBit yv) + xv << (botBit yv)"
    using bitCount_2_mul_distribute assms(3) by auto
  have unfoldLhs:
      "val[(x << (val_top_bit y))] =
       new_int b (xv << shift_amount b (take_bit b (word_of_nat (topBit (take_bit b yv)))))"
    apply auto
    using assms(1,2,6) intval_left_shift.simps(1) new_int.simps shift_amount.simps take_bit64
          val_top_bit.simps(1) by presburger+
  have unfoldRhs:
      "val[(x << (val_bot_bit y))] =
       new_int b (xv << shift_amount b (take_bit b (word_of_nat (botBit (take_bit b yv)))))"
    by (simp add: assms(1,2,6))+
  have rhs:
      "val[(x << (val_top_bit y)) + (x << (val_bot_bit y))] =
       new_int b (take_bit b (xv << shift_amount b (take_bit b (word_of_nat (topBit (take_bit b yv))))) +
                             (xv << shift_amount b (take_bit b (word_of_nat (botBit (take_bit b yv))))))"
    by (simp add: unfoldLhs unfoldRhs)
  have unfold:
      "new_int b (take_bit b (xv << shift_amount b (take_bit b (word_of_nat (topBit (take_bit b yv))))) +
                             (xv << shift_amount b (take_bit b (word_of_nat (botBit (take_bit b yv))))))
     = new_int b (xv << (topBit yv) + xv << (botBit yv))"
    by (simp add: assms(3,6) unfold_botBit_64 unfold_topBit_64)+
  have "val[(x << (val_top_bit y)) + (x << (val_bot_bit y))] =
        new_int b (xv << (topBit yv) + xv << (botBit yv))"
    using rhs unfold by argo
  then have "val[x * y] = val[(x << (val_top_bit y)) + (x << (val_bot_bit y))]"
    by (simp add: assms(1,2) distribute mergeTakeBit)
  then show ?thesis
    by (simp add: assms(4,5))
qed

(* Exp-level proofs *)
lemma exp_multiply_zero_64:
  shows "exp[x * (const (IntVal b 0))] \<ge> ConstantExpr (IntVal b 0)"
  apply auto
  subgoal premises p for m p xa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis evalDet p(1,2) xv evaltree_not_undef intval_is_null.cases intval_mul.simps(3,4,5))
    then have evalNotUndef: "val[xv * (IntVal b 0)] \<noteq> UndefVal"
      using p evalDet xv by blast
    then have mulUnfold: "val[xv * (IntVal b 0)] = IntVal xb (take_bit xb (xvv * 0))"
      by (metis new_int.simps xvv new_int_bin.simps intval_mul.simps(1))
    then show ?thesis
      by (metis evalDet p(1,3) xv ConstantExpr Value.distinct(1) bin_multiply_eliminate mulUnfold
          intval_mul.simps(1) new_int_bin.elims take_bit_of_0 xvv)
  qed
  done

lemma exp_multiply_neutral:
 "exp[x * (const (IntVal b 1))] \<ge> x"
  apply auto
  subgoal premises p for m p xa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (smt (z3) evalDet intval_mul.elims p(1,2) xv)
    then have evalNotUndef: "val[xv * (IntVal b 1)] \<noteq> UndefVal"
      using p evalDet xv by blast
    then have mulUnfold: "val[xv * (IntVal b 1)] = IntVal xb (take_bit xb (xvv * 1))"
      by (metis new_int.simps xvv new_int_bin.simps intval_mul.simps(1))
    then show ?thesis
      by (metis bin_multiply_identity evalDet eval_unused_bits_zero p(1) xv xvv)
  qed
  done

thm_oracles exp_multiply_neutral

lemma exp_multiply_negative:
 "exp[x * -(const (IntVal b 1))] \<ge> exp[-x]"
  apply auto
  subgoal premises p for m p xa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis array_length.cases evalDet evaltree_not_undef intval_mul.simps(3,4,5) p(1,2) xv)
    then have rewrite: "val[-(IntVal b 1)] = IntVal b (mask b)"
      by simp
    then have mulUnfold: "val[xv * (IntVal b (mask b))] =
                          (if xb=b then (IntVal xb (take_bit xb (xvv*(mask xb)))) else UndefVal)"
      by (metis new_int.simps xvv new_int_bin.simps intval_mul.simps(1))
    then show ?thesis
      by (metis evalDet eval_unused_bits_zero new_int.elims p(1,2) rewrite unary_eval.simps(2) xvv
          unfold_unary val_multiply_negative xv)
  qed
  done

lemma exp_MulPower2:
  fixes i :: "64 word"
  assumes "y = ConstantExpr (IntVal 64 (2 ^ unat(i)))"
  and     "0 < i"
  and     "i < 64"
  and     "exp[x > (const IntVal b 0)]"
  and     "exp[y > (const IntVal b 0)]"
  shows "exp[x * y] \<ge> exp[x << ConstantExpr (IntVal 64 i)]"
  using ConstantExprE equiv_exprs_def unfold_binary assms by fastforce

lemma exp_MulPower2Add1:
  fixes i :: "64 word"
  assumes "y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) + 1))"
  and     "0 < i"
  and     "i < 64"
  and     "exp[x > (const IntVal b 0)]"
  and     "exp[y > (const IntVal b 0)]"
  shows   "exp[x * y] \<ge> exp[(x << ConstantExpr (IntVal 64 i)) + x]"
  using ConstantExprE equiv_exprs_def unfold_binary assms by fastforce

lemma exp_MulPower2Sub1:
  fixes i :: "64 word"
  assumes "y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) - 1))"
  and     "0 < i"
  and     "i < 64"
  and     "exp[x > (const IntVal b 0)]"
  and     "exp[y > (const IntVal b 0)]"
  shows   "exp[x * y] \<ge> exp[(x << ConstantExpr (IntVal 64 i)) - x]"
  using ConstantExprE equiv_exprs_def unfold_binary assms by fastforce

lemma exp_MulPower2AddPower2:
  fixes i j :: "64 word"
  assumes "y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) + (2 ^ unat(j))))"
  and     "0 < i"
  and     "0 < j"
  and     "i < 64"
  and     "j < 64"
  and     "exp[x > (const IntVal b 0)]"
  and     "exp[y > (const IntVal b 0)]"
  shows   "exp[x * y] \<ge> exp[(x << ConstantExpr (IntVal 64 i)) + (x << ConstantExpr (IntVal 64 j))]"
  using ConstantExprE equiv_exprs_def unfold_binary assms by fastforce

(* Exp level helpers *)
lemma exp_distribute_multiplication:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr q = IntegerStamp b ql qh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp q"
  assumes "wf_stamp y"
  shows "exp[(x * q) + (x * y)] \<ge> exp[x * (q + y)]"
  apply auto
  subgoal premises p for m p xa qa xb aa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p by simp
    obtain qv where qv: "[m,p] \<turnstile> q \<mapsto> qv"
      using p by simp
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p by simp
    then obtain xvv where xvv: "xv = IntVal b xvv"
      by (metis assms(1,4) valid_int wf_stamp_def xv)
    then obtain qvv where qvv: "qv = IntVal b qvv"
      by (metis qv valid_int assms(2,5) wf_stamp_def)
    then obtain yvv where yvv: "yv = IntVal b yvv"
      by (metis yv valid_int assms(3,6) wf_stamp_def)
    have "val[xv * (qv + yv)] = val[(xv * qv) + (xv * yv)]"
      using val_distribute_multiplication by (simp add: yvv qvv xvv) 
    then show ?thesis
      by (metis bin_eval.simps(1,3) BinaryExpr p(1,2,3,5,6) qv xv evalDet yv qvv Value.distinct(1)
          yvv intval_add.simps(1))
   qed
  done

lemma exp_mul_power_2_add_power_2_64:
  assumes "wf_stamp x"
  assumes "stamp_expr x = IntegerStamp b lo hi"
  assumes "y = new_int b yv"
  assumes "bitCount yv = 2"
  assumes "lhs = exp[x << const (val_top_bit y)]"
  assumes "rhs = exp[x << const (val_bot_bit y)]"
  assumes "b = 64"
  shows "exp[x * const y] \<ge> exp[lhs + rhs]"
  using assms apply auto subgoal premises p for m p xa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(8) by auto
    obtain xvv where xvv: "xv = new_int 64 xvv"
      by (metis p(1,2) stamp_eval_same_bits wf_integerstamp_eval_is_new_int xv)
    have topBitEval: "[m,p] \<turnstile> exp[const (val_top_bit y)] \<mapsto> val[val_top_bit y]"
      by (metis assms(2) p(1,3,7) stamp_eval_int val_top_bit.simps(1) xv xvv)
    have botBitEval: "[m,p] \<turnstile> exp[const (val_bot_bit y)] \<mapsto> val[val_bot_bit y]"
      using assms(2) p(1,3,7) stamp_eval_int xv xvv by fastforce
    have rhslhsEval: "[m,p] \<turnstile> exp[lhs] \<mapsto> val[xv << (val_top_bit y)]"
      by (metis (lifting) BinaryExpr assms(3,5) bin_eval.simps(10) evalDet intval_add.simps(2) xvv
          p(3,4,7,8,9) topBitEval val_mul_power_2_add_power_2_64 xv)
    have rhsrhsEval: "[m,p] \<turnstile> exp[rhs] \<mapsto> val[xv << (val_bot_bit y)]"
      by (metis BinaryExpr xvv assms(3,6) bin_eval.simps(10) botBitEval evalDet intval_add.simps(6)
          p(3,4,7,8,9) val_mul_power_2_add_power_2_64 xv)
    have "[m,p] \<turnstile> exp[(x << const (val_top_bit y)) + (x << const (val_bot_bit y))] \<mapsto>
                  val[(xv << val_top_bit y) + (xv << val_bot_bit y)]"
      by (metis BinaryExpr xvv assms(3,5,6) bin_eval.simps(1) evalDet p(3,4,7,8,9) rhslhsEval xv
          rhsrhsEval val_mul_power_2_add_power_2_64)
    then have rhsE: "[m,p] \<turnstile> exp[lhs + rhs] \<mapsto> val[(xv << val_top_bit y) + (xv << val_bot_bit y)]"
      unfolding assms(5,6) by blast
    have "val[xv * y] = val[(xv << val_top_bit y) + (xv << val_bot_bit y)]"
      using val_mul_power_2_add_power_2_64 assms apply auto by (simp add: xvv)
    then show ?thesis
      by (metis evalDet p(3,5,6,8) rhsE xv)
  qed
  done

text \<open>Optimisations\<close>

optimization EliminateRedundantNegative: "-x * -y \<longmapsto> x * y"
  apply auto by (metis BinaryExpr val_eliminate_redundant_negative bin_eval.simps(3))

optimization MulNeutral: "x * ConstantExpr (IntVal b 1) \<longmapsto> x"
  using exp_multiply_neutral by blast

optimization MulEliminator: "x * ConstantExpr (IntVal b 0) \<longmapsto> const (IntVal b 0)"
  using exp_multiply_zero_64 by fast

optimization MulNegate: "x * -(const (IntVal b 1)) \<longmapsto> -x"
  using exp_multiply_negative by presburger

optimization MulPower2: "x * y \<longmapsto> x << const (IntVal 64 i) 
                              when (i > 0 \<and> stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x \<and>
                                    64 > i \<and>
                                    y = exp[const (IntVal 64 (2 ^ unat(i)))])"
   apply simp apply (rule impI; (rule allI)+; rule impI)
   subgoal premises eval for m p v
proof -
  obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
    using eval(2) by blast
  obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> yv"
    using eval(1,2) by blast
  obtain xvv where xvv: "xv = IntVal 64 xvv"
    by (metis wf_stamp_def eval(1) ExpIntBecomesIntVal xv)
  then have lhs: "[m, p] \<turnstile> exp[x * y] \<mapsto> val[xv * yv]"
    by (metis bin_eval.simps(3) eval(1,2) evalDet unfold_binary xv yv)
  have "[m, p] \<turnstile> exp[const (IntVal 64 i)] \<mapsto> val[(IntVal 64 i)]"
    by (smt (verit, ccfv_SIG) ConstantExpr constantAsStamp.simps(1) eval_bits_1_64 take_bit64 xv xvv
        validStampIntConst wf_value_def valid_value.simps(1))
  then have rhs: "[m, p] \<turnstile> exp[x << const (IntVal 64 i)] \<mapsto> val[xv << (IntVal 64 i)]"
    by (metis Value.simps(5) bin_eval.simps(10) intval_left_shift.simps(1) new_int.simps xv xvv
        evaltree.BinaryExpr)
  then show ?thesis
    by (metis eval(1,2) evalDet lhs ConstantExprE evaltree_not_undef val_MulPower2 yv)
qed
  done

optimization MulPower2AddPower2_64: "(x * (const y)) \<longmapsto>
                                     ((x << const (val_top_bit y)) + (x << const (val_bot_bit y)))
                                     when (stamp_expr x = IntegerStamp b lo hi \<and> wf_stamp x \<and>
                                           y = new_int b yv \<and> bitCount yv = 2 \<and> b = 64)"
  using exp_mul_power_2_add_power_2_64 by force

optimization MulPower2Add1: "x * y \<longmapsto> (x << const (IntVal 64 i)) + x
                              when (i > 0 \<and> stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x \<and>
                                    64 > i \<and>
                                    y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) + 1)))"
   apply simp apply (rule impI; (rule allI)+; rule impI)
  subgoal premises p for m p v
  proof -
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
      using p by fast
    then obtain xvv where xvv: "xv = IntVal 64 xvv"
      using p by (metis valid_int wf_stamp_def)
    obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> yv"
      using p by blast
    have ygezero: "y > ConstantExpr (IntVal 64 0)"
      using p wf_value_def sorry
    then have 1: "0 < i \<and>
                  i < 64 \<and>
                  y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) + 1))"
      using p by blast
    then have lhs: "[m, p] \<turnstile> exp[x * y] \<mapsto> val[xv * yv]"
      by (metis bin_eval.simps(3) evalDet p(2) xv yv unfold_binary)
    then have "[m, p] \<turnstile> exp[const (IntVal 64 i)] \<mapsto> val[(IntVal 64 i)]"
      by (metis wf_value_def verit_comp_simplify1(2) zero_less_numeral ConstantExpr take_bit64
          constantAsStamp.simps(1) validStampIntConst valid_value.simps(1))
    then have rhs2: "[m, p] \<turnstile> exp[x << const (IntVal 64 i)] \<mapsto> val[xv << (IntVal 64 i)]"
      by (metis Value.simps(5) bin_eval.simps(10) intval_left_shift.simps(1) new_int.simps xv xvv 
          evaltree.BinaryExpr)
    then have rhs: "[m, p] \<turnstile> exp[(x << const (IntVal 64 i)) + x] \<mapsto> val[(xv << (IntVal 64 i)) + xv]" 
       by (metis (no_types, lifting) intval_add.simps(1) bin_eval.simps(1) Value.simps(5) xv xvv
           evaltree.BinaryExpr intval_left_shift.simps(1) new_int.simps)
     then have simple: "val[xv * (IntVal 64 (2 ^ unat(i)))] = val[xv << (IntVal 64 i)]"
       using val_MulPower2 sorry
     then have "val[xv * yv] = val[(xv << (IntVal 64 i)) + xv]"
       using val_MulPower2Add1 sorry
     then show ?thesis
       by (metis "1" evalDet lhs p(2) rhs)
  qed
  done

optimization MulPower2Sub1: "x * y \<longmapsto> (x << const (IntVal 64 i)) - x
                              when (i > 0 \<and> stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x \<and>
                                    64 > i \<and>
                                    y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) - 1)))"
   apply simp apply (rule impI; (rule allI)+; rule impI)
  subgoal premises p for m p v
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p by fast
    then obtain xvv where xvv: "xv = IntVal 64 xvv"
      using p by (metis valid_int wf_stamp_def)
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p by blast
    have ygezero: "y > ConstantExpr (IntVal 64 0)" sorry
    then have 1: "0 < i \<and>
                  i < 64 \<and>
                  y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) - 1))"
      using p by blast
    then have lhs: "[m, p] \<turnstile> exp[x * y] \<mapsto> val[xv * yv]"
      by (metis bin_eval.simps(3) evalDet p(2) xv yv unfold_binary)
    then have "[m, p] \<turnstile> exp[const (IntVal 64 i)] \<mapsto> val[(IntVal 64 i)]"
      by (metis wf_value_def verit_comp_simplify1(2) zero_less_numeral ConstantExpr take_bit64
          constantAsStamp.simps(1) validStampIntConst valid_value.simps(1))
    then have rhs2: "[m, p] \<turnstile> exp[x << const (IntVal 64 i)] \<mapsto> val[xv << (IntVal 64 i)]"
      by (metis Value.simps(5) bin_eval.simps(10) intval_left_shift.simps(1) new_int.simps xv xvv 
          evaltree.BinaryExpr)
    then have rhs: "[m, p] \<turnstile> exp[(x << const (IntVal 64 i)) - x] \<mapsto> val[(xv << (IntVal 64 i)) - xv]" 
      using "1" equiv_exprs_def ygezero yv by fastforce
    then have "val[xv * yv] = val[(xv << (IntVal 64 i)) - xv]"
       using "1" exp_MulPower2Sub1 ygezero sorry 
     then show ?thesis
      by (metis evalDet lhs p(1,2) rhs)
  qed
done

end (* End of MulPhase *)

end (* End of file *)
