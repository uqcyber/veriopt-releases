theory NewAnd
  imports
    Common
begin

lemma bin_distribute_and_over_or:
  "bin[z & (x | y)] = bin[(z & x) | (z & y)]"
  by (smt (verit, best) bit_and_iff bit_eqI bit_or_iff)

lemma intval_distribute_and_over_or:
  "val[z & (x | y)] = val[(z & x) | (z & y)]"
  apply (cases x; cases y; cases z; auto)
  using bin_distribute_and_over_or by blast+

lemma exp_distribute_and_over_or:
  "exp[z & (x | y)] \<ge> exp[(z & x) | (z & y)]"
  apply simp using intval_distribute_and_over_or
  using BinaryExpr bin_eval.simps(4,5)
  using intval_or.simps(1) unfolding new_int_bin.simps new_int.simps apply auto
  by (metis bin_eval.simps(4) bin_eval.simps(5) intval_or.simps(2) intval_or.simps(5))


lemma intval_and_commute:
  "val[x & y] = val[y & x]"
  by (cases x; cases y; auto simp: and.commute)

lemma intval_or_commute:
  "val[x | y] = val[y | x]"
  by (cases x; cases y; auto simp: or.commute)

lemma intval_xor_commute:
  "val[x \<oplus> y] = val[y \<oplus> x]"
  by (cases x; cases y; auto simp: xor.commute)

lemma exp_and_commute:
  "exp[x & z] \<ge> exp[z & x]"
  apply simp using intval_and_commute by auto

lemma exp_or_commute:
  "exp[x | y] \<ge> exp[y | x]"
  apply simp using intval_or_commute by auto

lemma exp_xor_commute:
  "exp[x \<oplus> y] \<ge> exp[y \<oplus> x]"
  apply simp using intval_xor_commute by auto


lemma bin_eliminate_y:
  assumes "bin[y & z] = 0"
  shows "bin[(x | y) & z] = bin[x & z]"
  using assms
  by (simp add: and.commute bin_distribute_and_over_or)

lemma intval_eliminate_y:
  assumes "val[y & z] = IntVal b 0"
  shows "val[(x | y) & z] = val[x & z]"
  using assms bin_eliminate_y by (cases x; cases y; cases z; auto)

lemma intval_and_associative:
  "val[(x & y) & z] = val[x & (y & z)]"
  apply (cases x; cases y; cases z; auto)
  by (simp add: and.assoc)+

lemma intval_or_associative:
  "val[(x | y) | z] = val[x | (y | z)]"
  apply (cases x; cases y; cases z; auto)
  by (simp add: or.assoc)+

lemma intval_xor_associative:
  "val[(x \<oplus> y) \<oplus> z] = val[x \<oplus> (y \<oplus> z)]"
  apply (cases x; cases y; cases z; auto)
  by (simp add: xor.assoc)+

lemma exp_and_associative:
  "exp[(x & y) & z] \<ge> exp[x & (y & z)]"
  apply simp using intval_and_associative by fastforce

lemma exp_or_associative:
  "exp[(x | y) | z] \<ge> exp[x | (y | z)]"
  apply simp using intval_or_associative by fastforce

lemma exp_xor_associative:
  "exp[(x \<oplus> y) \<oplus> z] \<ge> exp[x \<oplus> (y \<oplus> z)]"
  apply simp using intval_xor_associative by fastforce


lemma intval_and_absorb_or:
  assumes "\<exists>b v . x = new_int b v" (* TODO: required? *)
  assumes "val[x & (x | y)] \<noteq> UndefVal"
  shows "val[x & (x | y)] = val[x]"
  using assms apply (cases x; cases y; auto)
  by (metis (mono_tags, lifting) intval_and.simps(5))

lemma intval_or_absorb_and:
  assumes "\<exists>b v . x = new_int b v" (* TODO: required? *)
  assumes "val[x | (x & y)] \<noteq> UndefVal"
  shows "val[x | (x & y)] = val[x]"
  using assms apply (cases x; cases y; auto)
  by (metis (mono_tags, lifting) intval_or.simps(5))

lemma exp_and_absorb_or:
  "exp[x & (x | y)] \<ge> exp[x]"
  apply auto using intval_and_absorb_or eval_unused_bits_zero
  by (smt (verit) evalDet intval_or.elims new_int.elims)

lemma exp_or_absorb_and:
  "exp[x | (x & y)] \<ge> exp[x]"
  apply auto using intval_or_absorb_and eval_unused_bits_zero
  by (smt (verit) evalDet intval_or.elims new_int.elims)

context
  includes bit_operations_syntax
begin
definition IRExpr_up :: "IRExpr \<Rightarrow> int64" where
  "IRExpr_up e = NOT 0"

definition IRExpr_down :: "IRExpr \<Rightarrow> int64" where
  "IRExpr_down e = 0"
end

lemma negative_all_set_32:
  "n < 32 \<Longrightarrow> bit (-1::int32) n"
  apply transfer by auto

definition MaxOrZero :: "nat set \<Rightarrow> nat" where
  "MaxOrZero s = (if s = {} then 0 else Max s)"

(* This is a different definition to Long.highestOneBit *)
definition highestOneBit :: "('a::len) word \<Rightarrow> nat" where
  "highestOneBit v = MaxOrZero {n . bit v n}"

lemma max_bit: "bit (v::('a::len) word) n \<Longrightarrow> n < Nat.size v"
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

lemma card_of_range_bound:
  fixes x y :: nat
  assumes "x > y"
  shows "x - y = card {n . y < n \<and> n \<le> x}"
proof -
  have finite: "finite {n . y \<le> n \<and> n < x}"
    by auto
  have "x - y \<ge> 1"
    using assms
    by simp
  show ?thesis
    apply (cases "{n . y \<le> n \<and> n < x} = {}")
    using assms apply blast
    using assms finite apply auto sorry
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

lemma
  assumes "y = 0"
  shows "x + y = or x y"
  using assms
  by simp

(*
lemma
  fixes x y :: "64 word"
  assumes "\<exists>e. n = 2^e"
  assumes "and y n = 0"
  shows "x + y = (or (and x n) (and y n)) + ((x >> n) + (y >> n) << n)"
*)

lemma no_overlap_or:
  assumes "and x y = 0"
  shows "x + y = or x y"
  using assms
  by (metis bit_and_iff bit_xor_iff disjunctive_add xor_self_eq)

(*lemma no_carry_zero_bit:
  assumes "\<not>(bit y j)"
  assumes "\<not>(bit y (Suc j))"
  shows "bit (x + y) (Suc j) = bit x (Suc j)"
  using assms sorry*)

lemma
  fixes x y :: "'a :: len word"
  assumes "(and y (mask (Suc j))) = 0"
  shows "bit (x + y) j = bit (or x y) j"
  using assms proof (induction j)
  case 0
  then show ?case
    by (metis Word.mask_Suc_0 bit_0 bit_1_iff bit_and_iff bit_mask_iff even_add even_or_iff less_numeral_extra(3) mask_0)
next
  case (Suc j)
  then show ?case sorry
qed

lemma packed_bottom_zeros_elim_add:
  fixes x y :: "'a :: len word"
  assumes "\<And>n. n \<le> j \<Longrightarrow> \<not>(bit y n)"
  shows "bit (x + y) j = bit x j"
  using assms 
proof -
  have "(and y (mask j)) = 0"
    using assms
    by (metis (no_types, opaque_lifting) bit_and_iff bit_eq_iff bit_mask_iff order_le_less zero_and_eq)
  have "bit (x + y) j = bit (or x y) j"
    using assms
    proof (induction j)
      case 0
      then show ?case
        by (simp add: even_or_iff)
    next
      case (Suc j)
      then show ?case sorry
    qed
  then show ?thesis
    by (simp add: assms bit_or_iff)
qed(*
proof (induction j)
  case 0
  then show ?case
    by auto
next
  case (Suc j)
  have "(and y (2^(Suc j))) = 0"
    using Suc.prems and_exp_eq_0_iff_not_bit by blast
  
  then show ?case sorry
qed 
  
  using assms bit_and_iff bit_xor_iff disjunctive_add xor_self_eq sorry*)
 (*
using assms proof (induction j)
  case 0
  then show ?case
    by (metis assms bit_0 bot_nat_0.extremum even_add)
next
  case (Suc j)
  have j0: "\<not>(bit y j)"
    by (simp add: Suc.prems)
  have sj0: "\<not>(bit y (Suc j))"
    by (simp add: Suc.prems)
  show ?case using j0 sj0 no_overlap_or
    by blast
qed *)

lemma packed_bits:
  fixes a :: "64 word"
  assumes "numberOfLeadingZeros a + bitCount a = 64"
  assumes "a \<noteq> 0"
  shows "n \<le> highestOneBit a \<longrightarrow> bit a n"
proof -
  obtain j where j: "j = highestOneBit a"
    by simp
  then have "\<forall>i. i < Nat.size a \<and> i > j \<longrightarrow> \<not>(bit a i)"
    unfolding highestOneBit_def
    by (simp add: j zerosAboveHighestOne)
  have "Nat.size a > highestOneBit a"
    unfolding highestOneBit_def MaxOrZero_def
    by (simp add: max_bit)
  then have jcard: "numberOfLeadingZeros a = card {i. j < i \<and> i \<le> Nat.size a}"
    unfolding numberOfLeadingZeros_def using j card_of_range_bound
    by presburger
  obtain k where k: "k = Nat.size a - numberOfLeadingZeros a"
    by presburger
  then have "k = bitCount a"
    using assms
    using size64 by auto
  have union: "{i. j < i \<and> i < Nat.size a} \<union> {i. i \<le> j} = {i. i < Nat.size a}"
    apply auto
    by (simp add: \<open>highestOneBit (a::64 word) < size_class.size a\<close> j order_le_less_trans)
  have intersect: "{i. j < i \<and> i < Nat.size a} \<inter> {i. i \<le> j} = {}"
    by force
  have "card {i. j < i \<and> i < Nat.size a} + card {i. i \<le> j} = card {i. i < Nat.size a}"
    using card_add intersect union
    by (metis (no_types, lifting) Int_commute bounded_nat_set_is_finite finite_Un mem_Collect_eq)
  then have "numberOfLeadingZeros a + card {i. i \<le> j} = Nat.size a + 1"
    unfolding jcard card_of_range apply auto
    by (metis j jcard leadingZerosAddHighestOne)
  then have "k = card {i. i < j}"
    using assms k
    by (simp add: add.commute)
  have "{i. j < i \<and> i < Nat.size a} \<inter> {i. i \<le> j} = {}"
    using intersect by blast
  have "\<forall>i . i \<in> {i. j < i \<and> i < Nat.size a} \<longrightarrow> \<not>(bit a i)"
    using \<open>\<forall>i::nat. i < size_class.size (a::64 word) \<and> (j::nat) < i \<longrightarrow> \<not> bit a i\<close> by blast
  then have "\<forall>i . i \<in> {i. i < j} \<longrightarrow> bit a i"
    sorry
  then have less: "\<forall>i. i < j \<longrightarrow> bit a i"
    by blast
  have eq: "bit a j"
    using j unfolding highestOneBit_def MaxOrZero_def
    by (metis Max_in assms(2) disjunctive_diff eq_iff_diff_eq_0 equals0D finite_bit_word mem_Collect_eq zero_and_eq)
  then show ?thesis
    using j
    by (simp add: less order_le_less)
qed


locale stamp_mask =
  fixes up :: "IRExpr \<Rightarrow> int64" ("\<up>")
  fixes down :: "IRExpr \<Rightarrow> int64" ("\<down>")
  assumes up_spec: "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> (and v (not ((ucast (\<up>e))))) = 0"
      and down_spec: "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> (and (not v) (ucast (\<down>e))) = 0"
begin

(*
lemma bitsets:
  "\<down>x \<subseteq> x \<and> x \<subseteq> \<up>x"
*)

lemma may_implies_either:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> bit (\<up>e) n \<Longrightarrow> bit v n = False \<or> bit v n = True"
  by simp

lemma not_may_implies_false:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> \<not>(bit (\<up>e) n) \<Longrightarrow> bit v n = False"
  using up_spec
  using bit_and_iff bit_eq_iff bit_not_iff bit_unsigned_iff down_spec
  by (smt (verit, best) bit.double_compl)

lemma must_implies_true:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> bit (\<down>e) n \<Longrightarrow> bit v n = True"
  using down_spec
  by (metis bit.compl_one bit_and_iff bit_minus_1_iff bit_not_iff impossible_bit ucast_id)

lemma not_must_implies_either:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> \<not>(bit (\<down>e) n) \<Longrightarrow> bit v n = False \<or> bit v n = True"
  by simp

lemma must_implies_may:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> n < 32 \<Longrightarrow> bit (\<down>e) n \<Longrightarrow> bit (\<up>e) n"
  by (meson must_implies_true not_may_implies_false)
end

context stamp_mask
begin

lemma bin_up_and_zero_implies_zero:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  shows "and xv yv = 0"
  using assms
  by (smt (z3) and.commute and.right_neutral and_zero_eq bit.compl_zero bit.conj_cancel_right bit.conj_disj_distribs(1) ucast_id up_spec word_bw_assocs(1) word_not_dist(2))

lemma intval_up_and_zero_implies_zero:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> xv"
  assumes "[m, p] \<turnstile> y \<mapsto> yv"
  assumes "val[xv & yv] \<noteq> UndefVal"
  shows "\<exists> b . val[xv & yv] = new_int b 0"
  using assms apply (cases xv; cases yv; auto)
  using bin_up_and_zero_implies_zero
  apply (smt (verit, best) take_bit_and take_bit_of_0)
  by presburger

lemma exp_eliminate_y:
  "and (\<up>y) (\<up>z) = 0 \<longrightarrow> BinaryExpr BinAnd (BinaryExpr BinOr x y) z \<ge> BinaryExpr BinAnd x z"
  apply simp apply (rule impI; rule allI; rule allI; rule allI) 
  subgoal premises p for m p v apply (rule impI) subgoal premises e
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using e by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using e by auto
    obtain zv where zv: "[m,p] \<turnstile> z \<mapsto> zv"
      using e by auto
    have lhs: "v = val[(xv | yv) & zv]"
      using xv yv zv
      by (smt (verit, best) BinaryExprE bin_eval.simps(4) bin_eval.simps(5) e evalDet)
    then have "v = val[(xv & zv) | (yv & zv)]"
      by (simp add: intval_and_commute intval_distribute_and_over_or)
    also have "\<exists>b. val[yv & zv] = new_int b 0"
      using intval_up_and_zero_implies_zero
      by (metis calculation e intval_or.simps(5) new_int.simps p take_bit_of_0 unfold_binary yv zv)
    ultimately have rhs: "v = val[xv & zv]"
      using intval_eliminate_y lhs by force
    from lhs rhs show ?thesis
      by (metis BinaryExpr BinaryExprE bin_eval.simps(4) e xv zv)
  qed
  done
  done

(*
lemma wrong:
  assumes "numberOfLeadingZeros (\<down>z) + highestOneBit (\<down>z) = 64"
  assumes "\<down>z \<noteq> 0"
  assumes "and (\<up>y) (\<down>z) = 0"
  shows "exp[(x + y) & z] \<ge> x"
  using assms apply auto sorry

lemma wrong2:
  (* assumes "numberOfLeadingZeros (\<up>z) + highestOneBit (\<up>z) = 64" see: leadingZerosAddHighestOne *)
  assumes "\<up>z \<noteq> 0"
  assumes "and (\<up>y) (\<up>z) = 0"
  shows "exp[(x + y) & z] \<ge> x"
  using assms apply simp apply (rule allI)+
  subgoal premises p for m p v apply (rule impI) subgoal premises e
    print_facts
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using e by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using e by auto
    obtain zv where zv: "[m,p] \<turnstile> z \<mapsto> zv"
      using e by auto
    have lhs: "v = val[(xv + yv) & zv]"
      using xv yv zv
      by (smt (verit, best) BinaryExprE bin_eval.simps(1) bin_eval.simps(4) e evalDet)
    have "val[yv & zv] \<noteq> UndefVal"
      sorry
    also have "\<exists>b. val[yv & zv] = new_int b 0"
      using intval_up_and_zero_implies_zero yv zv p(2)
      using calculation by presburger
    ultimately have rhs: "v = val[xv & zv]"
      using intval_eliminate_y lhs sorry
    from lhs rhs show ?thesis sorry
  qed
  done
  done*)

lemma right:
  assumes "numberOfLeadingZeros (\<up>z) + bitCount (\<up>z) = 64"
  assumes "\<up>z \<noteq> 0"
  assumes "and (\<up>y) (\<up>z) = 0"
  shows "exp[(x + y) & z] \<ge> exp[x & z]"
apply simp apply (rule allI)+ 
  subgoal premises p for m p v apply (rule impI) subgoal premises e
proof -
  obtain j where j: "j = highestOneBit (\<up>z)"
    by simp
  obtain xv b where xv: "[m,p] \<turnstile> x \<mapsto> IntVal b xv"
    using e
    by (metis EvalTreeE(5) bin_eval_inputs_are_ints bin_eval_new_int new_int.simps)
  obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> IntVal b yv"
    using e EvalTreeE(5) bin_eval_inputs_are_ints bin_eval_new_int new_int.simps
    by (smt (verit) Value.sel(1) bin_eval.simps(1) evalDet intval_add.elims xv)
  obtain xyv where xyv: "[m, p] \<turnstile> exp[x + y] \<mapsto> IntVal b xyv"
    using e EvalTreeE(5) bin_eval_inputs_are_ints bin_eval_new_int new_int.simps
    xv yv
    by (metis BinaryExpr Value.distinct(1) bin_eval.simps(1) intval_add.simps(1))
  then obtain zv where zv: "[m,p] \<turnstile> z \<mapsto> IntVal b zv"
    using e EvalTreeE(5) bin_eval_inputs_are_ints bin_eval_new_int new_int.simps
    Value.sel(1) bin_eval.simps(4) evalDet intval_and.elims
    by (smt (verit) new_int_bin.simps)
  have "xyv = take_bit b (xv + yv)"
    using xv yv xyv
    by (metis BinaryExprE Value.sel(2) bin_eval.simps(1) evalDet intval_add.simps(1))
  then have "v = IntVal b (take_bit b (and (take_bit b (xv + yv)) zv))"
    using zv
    by (smt (verit) EvalTreeE(5) Value.sel(1) Value.sel(2) bin_eval.simps(4) e evalDet intval_and.elims new_int.simps new_int_bin.simps xyv)
  then have veval: "v = IntVal b (and (xv + yv) zv)"
    by (metis (no_types, lifting) eval_unused_bits_zero take_bit_eq_mask word_bw_comms(1) word_bw_lcs(1) zv)
  have obligation: "(and (xv + yv) zv) = (and xv zv) \<Longrightarrow> [m,p] \<turnstile> BinaryExpr BinAnd x z \<mapsto> v"
    by (smt (verit) EvalTreeE(5) Value.inject(1) \<open>(v::Value) = IntVal (b::nat) (take_bit b (and (take_bit b ((xv::64 word) + (yv::64 word))) (zv::64 word)))\<close> \<open>(xyv::64 word) = take_bit (b::nat) ((xv::64 word) + (yv::64 word))\<close> bin_eval.simps(4) e evalDet eval_unused_bits_zero evaltree.simps intval_and.simps(1) take_bit_and xv xyv zv)
  have per_bit: "\<forall>n . bit (and (xv + yv) zv) n = bit (and xv zv) n \<Longrightarrow> (and (xv + yv) zv) = (and xv zv)"
    by (simp add: bit_eq_iff)
  show ?thesis
    apply (rule obligation)
    apply (rule per_bit)
    apply (rule allI)
    subgoal for n
  proof (cases "n \<le> j")
    case True
    then have "\<not>(bit yv n)"
      by (metis (no_types, opaque_lifting) assms(1) assms(2) assms(3) bit_and_iff bit_not_iff impossible_bit j packed_bits ucast_id up_spec yv)
    have "\<forall>n' . n' \<le> n \<longrightarrow> \<not>(bit yv n')"
      by (metis (no_types, lifting) True assms(1) assms(2) assms(3) bit_and_iff bit_not_iff down_spec dual_order.trans j not_may_implies_false packed_bits yv)
    then have "bit (xv + yv) n = bit xv n"
      using packed_bottom_zeros_elim_add
      by blast
    then show ?thesis
      by (simp add: bit_and_iff)
  next
    case False
    then have "\<not>(bit zv n)"
      by (metis j linorder_not_less not_may_implies_false zerosAboveHighestOne zv)
    then have v: "\<not>(bit (and (xv + yv) zv) n)"
      by (simp add: bit_and_iff)
    then have v': "\<not>(bit (and xv zv) n)"
      by (simp add: \<open>\<not> bit (zv::64 word) (n::nat)\<close> bit_and_iff)
    from v v' show ?thesis
      by simp
  qed
  done
qed
  done
  done

end

lemma ucast_zero: "(ucast (0::int64)::int32) = 0"
  by simp

lemma ucast_minus_one: "(ucast (-1::int64)::int32) = -1"
  apply transfer by auto

interpretation simple_mask: stamp_mask
  "IRExpr_up :: IRExpr \<Rightarrow> int64"
  "IRExpr_down :: IRExpr \<Rightarrow> int64"
  unfolding IRExpr_up_def IRExpr_down_def
  apply unfold_locales
  by (simp add: ucast_minus_one)+



phase NewAnd
  terminating size
begin

optimization redundant_lhs_y_or: "((x | y) & z) \<longmapsto> x & z
                                when (((and (IRExpr_up y) (IRExpr_up z)) = 0))"
  using simple_mask.exp_eliminate_y by blast

optimization redundant_lhs_x_or: "((x | y) & z) \<longmapsto> y & z
                                when (((and (IRExpr_up x) (IRExpr_up z)) = 0))"
  using simple_mask.exp_eliminate_y
  by (meson exp_or_commute mono_binary order_refl order_trans)

optimization redundant_rhs_y_or: "(z & (x | y)) \<longmapsto> z & x
                                when (((and (IRExpr_up y) (IRExpr_up z)) = 0))"
  using simple_mask.exp_eliminate_y
  by (meson exp_and_commute order.trans)

optimization redundant_rhs_x_or: "(z & (x | y)) \<longmapsto> z & y
                                when (((and (IRExpr_up x) (IRExpr_up z)) = 0))"
  using simple_mask.exp_eliminate_y
  by (meson dual_order.trans exp_and_commute exp_or_commute mono_binary order_refl)

(*
optimization redundant_lhs_add: "((x + y) & z) \<longmapsto> x & z
                               when ((and (IRExpr_up y) (IRExpr_down z)) = 0)"
*)

end

end