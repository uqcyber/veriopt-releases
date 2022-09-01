section \<open>java.lang.Long\<close>

text \<open>
Utility functions from the Long class that Graal occasionally makes use of.
\<close>

theory Long
  imports ValueThms
begin

lemma negative_all_set_32:
  "n < 32 \<Longrightarrow> bit (-1::int32) n"
  apply transfer by auto

(* TODO: better handle empty *)
definition MaxOrZero :: "nat set \<Rightarrow> nat" where
  "MaxOrZero s = (if s = {} then 0 else Max s)"

definition MinOrHighest :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "MinOrHighest s m = (if s = {} then m else Min s)"
 
(* This is a different definition to Long.highestOneBit *)
definition highestOneBit :: "('a::len) word \<Rightarrow> nat" where
  "highestOneBit v = MaxOrZero {n . bit v n}"

definition lowestOneBit :: "('a::len) word \<Rightarrow> nat" where
  "lowestOneBit v = MinOrHighest {n . bit v n} (size v + 1)"

lemma max_bit: "bit (v::('a::len) word) n \<Longrightarrow> n < size v"
  by (simp add: bit_imp_le_length size_word.rep_eq)

lemma max_set_bit: "MaxOrZero {n . bit (v::('a::len) word) n} \<le> Nat.size v"
  using max_bit unfolding MaxOrZero_def
  by force

definition numberOfLeadingZeros :: "('a::len) word \<Rightarrow> nat" where
  "numberOfLeadingZeros v = Nat.size v - highestOneBit v"

lemma MaxOrZero_zero: "MaxOrZero {} = 0"
  by (simp add: MaxOrZero_def)

lemma MaxOrZero_max: "s \<noteq> {} \<Longrightarrow> MaxOrZero s = Max s"
  by (simp add: MaxOrZero_def)

lemma zero_no_bits:
  "{n . bit 0 n} = {}"
  by simp

lemma "highestOneBit (0::64 word) = 0"
  by (simp add: MaxOrZero_zero highestOneBit_def)

lemma "numberOfLeadingZeros (0::64 word) = 64"
  unfolding numberOfLeadingZeros_def
  by (simp add: MaxOrZero_zero highestOneBit_def size64)

lemma highestOneBit_top: "Max {highestOneBit (v::64 word)} \<le> 64"
  unfolding highestOneBit_def
  by (metis Max_singleton max_set_bit size64)

lemma numberOfLeadingZeros_top: "Max {numberOfLeadingZeros (v::64 word)} \<le> 64"
  unfolding numberOfLeadingZeros_def
  by (simp add: size64)

lemma leadingZerosAddHighestOne: "numberOfLeadingZeros v + highestOneBit v = Nat.size v"
  by (simp add: highestOneBit_def max_set_bit numberOfLeadingZeros_def)

definition numberOfTrailingZeros :: "('a::len) word \<Rightarrow> nat" where
  "numberOfTrailingZeros v = lowestOneBit v - 1"

lemma lowestOneBit_bot: "lowestOneBit (0::64 word) = 65"
  unfolding lowestOneBit_def MinOrHighest_def
  by (simp add: size64)

lemma bit_zero_set_in_top: "bit (-1::'a::len word) 0"
  by auto

lemma nat_bot_set: "(0::nat) \<in> xs \<longrightarrow> (\<forall>x \<in> xs . 0 \<le> x)"
  by fastforce

lemma "numberOfTrailingZeros (0::64 word) = 64"
  unfolding numberOfTrailingZeros_def
  using lowestOneBit_bot by simp

definition bitCount :: "('a::len) word \<Rightarrow> nat" where
  "bitCount v = card {n . bit v n}"

lemma "bitCount 0 = 0"
  unfolding bitCount_def
  by (metis card.empty zero_no_bits)

lemma negone_set:
  "bit (-1::('a::len) word) n \<longleftrightarrow> n < LENGTH('a)"
  by simp

lemma negone_all_bits:
  "{n . bit (-1::('a::len) word) n} = {n . 0 \<le> n \<and> n < LENGTH('a)}"
  using negone_set
  by auto

lemma bitCount_finite:
  "finite {n . bit (v::('a::len) word) n}"
  by simp

lemma card_of_range:
  "x = card {n . 0 \<le> n \<and> n < x}"
  by simp

lemma range_of_nat:
  "{(n::nat) . 0 \<le> n \<and> n < x} = {n . n < x}"
  by simp

lemma finite_range:
  "finite {n::nat . n < x}"
  by simp


lemma range_eq:
  fixes x y :: nat
  shows "card {y..<x} = card {y<..x}"
  using card_atLeastLessThan card_greaterThanAtMost by presburger

lemma card_of_range_bound:
  fixes x y :: nat
  assumes "x > y"
  shows "x - y = card {n . y < n \<and> n \<le> x}"
proof -
  have finite: "finite {n . y \<le> n \<and> n < x}"
    by auto
  have nonempty: "{n . y \<le> n \<and> n < x} \<noteq> {}"
    using assms by blast
  have simprep: "{n . y < n \<and> n \<le> x} = {y<..x}"
    by auto
  have "x - y = card {y<..x}"
    by auto
  then show ?thesis
    unfolding simprep by blast
qed

lemma "bitCount (-1::('a::len) word) = LENGTH('a)"
  unfolding bitCount_def using card_of_range
  by (metis (no_types, lifting) Collect_cong negone_all_bits)

lemma bitCount_range:
  fixes n :: "('a::len) word"
  shows "0 \<le> bitCount n \<and> bitCount n \<le> Nat.size n"
  unfolding bitCount_def
  by (metis atLeastLessThan_iff bot_nat_0.extremum max_bit mem_Collect_eq subsetI subset_eq_atLeast0_lessThan_card)

lemma zerosAboveHighestOne:
  "n > highestOneBit a \<Longrightarrow> \<not>(bit a n)"
  unfolding highestOneBit_def MaxOrZero_def
  by (metis (mono_tags, lifting) Collect_empty_eq Max_ge bitCount_finite linorder_not_le mem_Collect_eq)

lemma union_bit_sets:
  fixes a :: "('a::len) word"
  shows "{n . n < Nat.size a \<and> bit a n} \<union> {n . n < Nat.size a \<and> \<not>(bit a n)} = {n . n < Nat.size a}"
  by fastforce

lemma disjoint_bit_sets:
  fixes a :: "('a::len) word"
  shows "{n . n < Nat.size a \<and> bit a n} \<inter> {n . n < Nat.size a \<and> \<not>(bit a n)} = {}"
  by blast

lemma qualified_bitCount:
  "bitCount v = card {n . n < Nat.size v \<and> bit v n}"
  by (metis (no_types, lifting) Collect_cong bitCount_def max_bit)

lemma card_eq:
  assumes "finite x \<and> finite y \<and> finite z"
  assumes "x \<union> y = z"
  assumes "y \<inter> x = {}"
  shows "card z - card y = card x"
  using assms add_diff_cancel_right' card_Un_disjoint
  by (metis inf.commute)

lemma card_add:
  assumes "finite x \<and> finite y \<and> finite z"
  assumes "x \<union> y = z"
  assumes "y \<inter> x = {}"
  shows "card x + card y = card z"
  using assms card_Un_disjoint
  by (metis inf.commute)

lemma intersect_bitCount_helper:
  "card {n . n < Nat.size a} - bitCount a = card {n . n < Nat.size a \<and> \<not>(bit a n)}"
proof -
  have size_def: "Nat.size a = card {n . n < Nat.size a}"
    using card_of_range by simp
  have bitCount_def: "bitCount a = card {n . n < Nat.size a \<and> bit a n}"
    using qualified_bitCount by auto
  have disjoint: "{n . n < Nat.size a \<and> bit a n} \<inter> {n . n < Nat.size a \<and> \<not>(bit a n)} = {}"
    using disjoint_bit_sets by auto
  have union: "{n . n < Nat.size a \<and> bit a n} \<union> {n . n < Nat.size a \<and> \<not>(bit a n)} = {n . n < Nat.size a}"
    using union_bit_sets by auto
  show ?thesis
    unfolding bitCount_def
    apply (rule card_eq)
    using finite_range apply simp
    using union apply blast
    using disjoint by simp
qed

lemma intersect_bitCount:
  "Nat.size a - bitCount a = card {n . n < Nat.size a \<and> \<not>(bit a n)}"
  using card_of_range intersect_bitCount_helper by auto

hide_fact intersect_bitCount_helper

end

