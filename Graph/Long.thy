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
definition MaxOrNeg :: "nat set \<Rightarrow> int" where
  "MaxOrNeg s = (if s = {} then -1 else Max s)"

definition MinOrHighest :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "MinOrHighest s m = (if s = {} then m else Min s)"
 
(* This is a different definition to Long.highestOneBit *)
definition highestOneBit :: "('a::len) word \<Rightarrow> int" where
  "highestOneBit v = MaxOrNeg {n . bit v n}"

definition lowestOneBit :: "('a::len) word \<Rightarrow> nat" where
  "lowestOneBit v = MinOrHighest {n . bit v n} (size v)"

lemma max_bit: "bit (v::('a::len) word) n \<Longrightarrow> n < size v"
  by (simp add: bit_imp_le_length size_word.rep_eq)

lemma max_set_bit: "MaxOrNeg {n . bit (v::('a::len) word) n} < Nat.size v"
  using max_bit unfolding MaxOrNeg_def
  by force

definition numberOfLeadingZeros :: "('a::len) word \<Rightarrow> nat" where
  "numberOfLeadingZeros v = nat (Nat.size v - highestOneBit v - 1)"

lemma MaxOrNeg_neg: "MaxOrNeg {} = -1"
  by (simp add: MaxOrNeg_def)

lemma MaxOrNeg_max: "s \<noteq> {} \<Longrightarrow> MaxOrNeg s = Max s"
  by (simp add: MaxOrNeg_def)

lemma zero_no_bits:
  "{n . bit 0 n} = {}"
  by simp

lemma "highestOneBit (0::64 word) = -1"
  by (simp add: MaxOrNeg_neg highestOneBit_def)

lemma "numberOfLeadingZeros (0::64 word) = 64"
  unfolding numberOfLeadingZeros_def using  MaxOrNeg_neg highestOneBit_def size64
  by (smt (verit) nat_int zero_no_bits)

lemma highestOneBit_top: "Max {highestOneBit (v::64 word)} < 64"
  unfolding highestOneBit_def
  by (metis Max_singleton int_eq_iff_numeral max_set_bit size64)

lemma numberOfLeadingZeros_top: "Max {numberOfLeadingZeros (v::64 word)} \<le> 64"
  unfolding numberOfLeadingZeros_def
  using size64
  by (simp add: MaxOrNeg_def highestOneBit_def nat_le_iff)

lemma numberOfLeadingZeros_range: "0 \<le> numberOfLeadingZeros a \<and> numberOfLeadingZeros a \<le> Nat.size a"
  unfolding numberOfLeadingZeros_def
  using MaxOrNeg_def highestOneBit_def nat_le_iff
  by (smt (verit) bot_nat_0.extremum int_eq_iff)

lemma leadingZerosAddHighestOne: "numberOfLeadingZeros v + highestOneBit v = Nat.size v - 1"
  unfolding numberOfLeadingZeros_def highestOneBit_def
  using MaxOrNeg_def int_nat_eq int_ops(6) max_bit order_less_irrefl by fastforce

definition numberOfTrailingZeros :: "('a::len) word \<Rightarrow> nat" where
  "numberOfTrailingZeros v = lowestOneBit v"

lemma lowestOneBit_bot: "lowestOneBit (0::64 word) = 64"
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

definition zeroCount :: "('a::len) word \<Rightarrow> nat" where
  "zeroCount v = card {n. n < Nat.size v \<and> \<not>(bit v n)}"

lemma zeroCount_finite: "finite {n. n < Nat.size v \<and> \<not>(bit v n)}"
  using finite_nat_set_iff_bounded by blast

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
  unfolding highestOneBit_def MaxOrNeg_def
  by (metis (mono_tags, opaque_lifting) Collect_empty_eq Max_ge finite_bit_word less_le_not_le mem_Collect_eq of_nat_le_iff)

lemma zerosBelowLowestOne:
  assumes "n < lowestOneBit a"
  shows "\<not>(bit a n)"
proof (cases "{i. bit a i} = {}")
  case True
  then show ?thesis by simp
next
  case False
  have "n < Min (Collect (bit a)) \<Longrightarrow> \<not> bit a n"
    using False by auto
  then show ?thesis
    by (metis False MinOrHighest_def assms lowestOneBit_def)
qed

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


lemma card_add_inverses:
  assumes "finite {n. Q n \<and> \<not>(P n)} \<and> finite {n. Q n \<and> P n} \<and> finite {n. Q n}"
  shows "card {n. Q n \<and> P n} + card {n. Q n \<and> \<not>(P n)} = card {n. Q n}"
  apply (rule card_add)
  using assms apply simp
  apply auto[1]
  by auto

lemma ones_zero_sum_to_width:
  "bitCount a + zeroCount a = Nat.size a"
proof -
  have add_cards: "card {n. (\<lambda>n. n < size a) n \<and> (bit a n)} + card {n. (\<lambda>n. n < size a) n \<and> \<not>(bit a n)} = card {n. (\<lambda>n. n < size a) n}"
    apply (rule card_add_inverses) by simp
  then have "... = Nat.size a"
    by auto
 then show ?thesis 
    unfolding bitCount_def zeroCount_def using max_bit
    by (metis (mono_tags, lifting) Collect_cong add_cards)
qed

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

