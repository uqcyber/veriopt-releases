section \<open>jdk.vm.ci.code.CodeUtil\<close>

text \<open>Utility functions from the Java CodeUtil class\<close>

theory JavaCodeUtil
  imports
    JavaLong
begin

(* An invariant asserted by minValue and maxValue *)
definition in_bit_range :: "nat \<Rightarrow> bool" where
  "in_bit_range bits = ((0 < bits) \<and> (bits \<le> 64))"

(* An operation used by minValue, zeroExtend and signExtend *)
definition mask_shift :: "nat \<Rightarrow> 'a :: len word" where
  "mask_shift bits = ((-1) << bits)"

subsection \<open>Function definitions\<close>

(* Corresponds to CodeUtil.isOdd(I)Z *)
definition is_odd :: "'a :: len word \<Rightarrow> bool" where
  "is_odd n = ((and n 1) = 1)"

(* Corresponds to CodeUtil.isEven(I)Z *)
definition is_even :: "'a :: len word \<Rightarrow> bool" where
  "is_even n = ((and n 1) = 0)"

(* Corresponds to CodeUtil.isPowerOf2(I)Z and CodeUtil.isPowerOf2(J)Z*)
definition is_power_of_2 :: "'a :: len word \<Rightarrow> bool" where
  "is_power_of_2 val = ((0 <s val) \<and> ((and val (val - 1)) = 0))"

(* Corresponds to CodeUtil.log2(I)I and CodeUtil.log2(J)I *)
definition log2 :: "'a :: len word \<Rightarrow> nat" where
  "log2 val = (if (0 <s val) then (LENGTH('a) - 1 - numberOfLeadingZeros val) else undefined)"

text \<open>
The condition: $ if (bit value (inputBits - 1)) $

corresponds to the Java snippet: $ if ((value >>> (inputBits - 1) & 1) == 1) $

which is shown to be equivalent by @{prf shift_n_eq_bit_n}\<close>
(* Corresponds to CodeUtil.signExtend(JI)J *)
definition sign_extend :: "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" where
  "sign_extend value inputBits =
    (if (inputBits < 64)
     then (if (bit value (inputBits - 1))
           then (or value (mask_shift inputBits))
           else (and value (not (mask_shift inputBits))))
     else value)"

(* Corresponds to CodeUtil.zeroExtend(JI)J *)
definition zero_extend :: "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" where
  "zero_extend value inputBits =
    (if (inputBits < 64) then (and value (not (mask_shift inputBits))) else value)"

(* Corresponds to CodeUtil.narrow(JI)J *)
definition narrow :: "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" where
  "narrow value resultBits = sign_extend (and value (mask resultBits)) resultBits"

(* Corresponds to CodeUtil.minValue(I)J *)
definition min_value :: "nat \<Rightarrow> 'a :: len word" where
  "min_value bits = (if (in_bit_range bits) then (mask_shift (bits - 1)) else undefined)"

(* Corresponds to CodeUtil.maxValue(I)J *)
definition max_value :: "nat \<Rightarrow> 'a :: len word" where
  "max_value bits = (if (in_bit_range bits) then (mask (bits - 1)) else undefined)"

subsection \<open>Properties\<close>

subsubsection \<open>Helper functions\<close>

lemma mask_eq_not_mask_shift: "mask b = not (mask_shift b)"
  unfolding mask_shift_def shiftl_def by simp

subsubsection \<open>$is_power_of_2$\<close>

lemma is_power_of_2_nonzero: "is_power_of_2 v \<Longrightarrow> v \<noteq> 0"
  unfolding is_power_of_2_def by blast

lemma is_power_of_2_implies_bitCount: "is_power_of_2 v \<Longrightarrow> bitCount v \<noteq> 0"
  unfolding bitCount_def is_power_of_2_def by (simp, metis no_bits_implies_zero signed.neq_iff)

lemma is_power_of_2_sign_unset:
  fixes v :: "'a :: len word"
  assumes "is_power_of_2 v"
  shows "\<not>(bit v (LENGTH('a) - 1))"
  using assms unfolding is_power_of_2_def by (metis One_nat_def pos_signed_unset signed.nless_le)

subsubsection \<open>$log2$\<close>

lemma log2_highestOneBit_eq_64:
  fixes v :: "64word"
  assumes "0 <s v"
  shows "log2 v = highestOneBit v"
  using assms unfolding log2_def numberOfLeadingZeros_def apply auto
  subgoal premises p
  proof -
    have "(LENGTH(64) - 1 - numberOfLeadingZeros v) = highestOneBit v"
      by (metis bin_log2_def bin_log2_highestOneBit_eq_64 less_iff p word_gt_0)
    then show ?thesis
      by (simp add: numberOfLeadingZeros_def)
  qed
  done

subsubsection \<open>$sign_extend$ and $zero_extend$\<close>

lemma sign_zero_extend_eq:
  assumes "bits < 64"
  assumes "\<not>(bit v (bits - 1))"
  shows "sign_extend v bits = zero_extend v bits"
  using assms unfolding sign_extend_def zero_extend_def by simp

end