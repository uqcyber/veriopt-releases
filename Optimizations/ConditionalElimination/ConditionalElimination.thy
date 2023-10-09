section \<open>Conditional Elimination Phase\<close>

theory ConditionalElimination
  imports
    Semantics.IRTreeEvalThms
    Proofs.Rewrites
    Proofs.Bisimulation
begin

subsection \<open>Individual Elimination Rules\<close>

text \<open>The set of rules used for determining whether a condition @{term q1} implies
    another condition @{term q2} or its negation.
    These rules are used for conditional elimination.\<close>

inductive
  implys :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<Rrightarrow> _") and 
  nimplys :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<Rrightarrow>\<not> _") where
  q_imp_q: 
  "q \<Rrightarrow> q" |
  eq_impliesnot_less:
  "(BinaryExpr BinIntegerEquals x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerLessThan x y)" |
  eq_impliesnot_less_rev:
  "(BinaryExpr BinIntegerEquals x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerLessThan y x)" |
  less_impliesnot_rev_less:
  "(BinaryExpr BinIntegerLessThan x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerLessThan y x)" |
  less_impliesnot_eq:
  "(BinaryExpr BinIntegerLessThan x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerEquals x y)" |
  less_impliesnot_eq_rev:
  "(BinaryExpr BinIntegerLessThan x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerEquals y x)" |
  negate_true:
  "\<lbrakk>x \<Rrightarrow>\<not> y\<rbrakk> \<Longrightarrow> x \<Rrightarrow> (UnaryExpr UnaryLogicNegation y)" |
  negate_false:
  "\<lbrakk>x \<Rrightarrow> y\<rbrakk> \<Longrightarrow> x \<Rrightarrow>\<not> (UnaryExpr UnaryLogicNegation y)"

text \<open>The relation @{term "q1 \<Rrightarrow> q2"} indicates that the implication @{term "q1 \<longrightarrow> q2"}
    is known true (i.e. universally valid), 
    and the relation @{term "q1 \<Rrightarrow>\<not> q2"} indicates that the implication @{term "q1 \<longrightarrow> q2"}
    is known false (i.e. @{term "q1 \<longrightarrow>\<not> q2"} is universally valid.
    If neither @{term "q1 \<Rrightarrow> q2"} nor @{term "q1 \<Rrightarrow>\<not> q2"} then the status is unknown.
    Only the known true and known false cases can be used for conditional elimination.\<close>

fun implies_valid :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" (infix "\<Zinj>" 50) where
  "implies_valid q1 q2 = 
    (\<forall>m p v1 v2. ([m, p] \<turnstile> q1 \<mapsto> v1) \<and> ([m,p] \<turnstile> q2 \<mapsto> v2) \<longrightarrow> 
            (val_to_bool v1 \<longrightarrow> val_to_bool v2))"

fun impliesnot_valid :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" (infix "\<Zpinj>" 50) where
  "impliesnot_valid q1 q2 = 
    (\<forall>m p v1 v2. ([m, p] \<turnstile> q1 \<mapsto> v1) \<and> ([m,p] \<turnstile> q2 \<mapsto> v2) \<longrightarrow> 
            (val_to_bool v1 \<longrightarrow> \<not>val_to_bool v2))"

text \<open>The relation @{term "q1 \<Zinj> q2"} means @{term "q1 \<longrightarrow> q2"} is universally valid, 
      and the relation @{term "q1 \<Zpinj> q2"} means @{term "q1 \<longrightarrow> \<not>q2"} is universally valid.\<close>

lemma eq_impliesnot_less_helper:
  "v1 = v2 \<longrightarrow> \<not>(int_signed_value b v1 < int_signed_value b v2)" 
  by force 

lemma eq_impliesnot_less_val:
  "val_to_bool(intval_equals v1 v2) \<longrightarrow> \<not>val_to_bool(intval_less_than v1 v2)"
proof -
  have unfoldEqualDefined: "(intval_equals v1 v2 \<noteq> UndefVal) \<Longrightarrow>
        (val_to_bool(intval_equals v1 v2) \<longrightarrow> (\<not>(val_to_bool(intval_less_than v1 v2))))"
    subgoal premises p
  proof -
    obtain v1b v1v where v1v: "v1 = IntVal v1b v1v"
      by (metis array_length.cases intval_equals.simps(2,3,4,5) p)
    obtain v2b v2v where v2v: "v2 = IntVal v2b v2v"
      by (metis Value.exhaust_sel intval_equals.simps(6,7,8,9) p)
    have sameWidth: "v1b=v2b"
      by (metis bool_to_val_bin.simps intval_equals.simps(1) p v1v v2v)
    have unfoldEqual: "intval_equals v1 v2 = (bool_to_val (v1v=v2v))"
      by (simp add: sameWidth v1v v2v)
    have unfoldLessThan: "intval_less_than v1 v2 = (bool_to_val (int_signed_value v1b v1v < int_signed_value v2b v2v))"
      by (simp add: sameWidth v1v v2v)
    have val: "((v1v=v2v)) \<longrightarrow> (\<not>((int_signed_value v1b v1v < int_signed_value v2b v2v)))"
      using sameWidth by auto
    have doubleCast0: "val_to_bool (bool_to_val ((v1v = v2v))) = (v1v = v2v)"
      using bool_to_val.elims val_to_bool.simps(1) by fastforce
    have doubleCast1: "val_to_bool (bool_to_val ((int_signed_value v1b v1v < int_signed_value v2b v2v))) =
                                                 (int_signed_value v1b v1v < int_signed_value v2b v2v)"
      using bool_to_val.elims val_to_bool.simps(1) by fastforce
    then show ?thesis
      using p val unfolding unfoldEqual unfoldLessThan doubleCast0 doubleCast1 by blast
  qed done
  show ?thesis
    by (metis Value.distinct(1) val_to_bool.elims(2) unfoldEqualDefined)
qed

thm_oracles eq_impliesnot_less_val

lemma eq_impliesnot_less_rev_val:
  "val_to_bool(intval_equals v1 v2) \<longrightarrow> \<not>val_to_bool(intval_less_than v2 v1)"
proof -
  have a: "intval_equals v1 v2 = intval_equals v2 v1"
    apply (cases "intval_equals v1 v2 = UndefVal")
    apply (smt (z3) bool_to_val_bin.simps intval_equals.elims intval_equals.simps)
    subgoal premises p
    proof -
      obtain v1b v1v where v1v: "v1 = IntVal v1b v1v"
        by (metis Value.exhaust_sel intval_equals.simps(2,3,4,5) p)
      obtain v2b v2v where v2v: "v2 = IntVal v2b v2v"
        by (metis Value.exhaust_sel intval_equals.simps(6,7,8,9) p)
      then show ?thesis
        by (smt (verit) bool_to_val_bin.simps intval_equals.simps(1) v1v)
    qed done
  show ?thesis
    using a eq_impliesnot_less_val by presburger
qed

lemma less_impliesnot_rev_less_val:
  "val_to_bool(intval_less_than v1 v2) \<longrightarrow> \<not>val_to_bool(intval_less_than v2 v1)"
  apply (rule impI)
  subgoal premises p
  proof -
    obtain v1b v1v where v1v: "v1 = IntVal v1b v1v"
      by (metis Value.exhaust_sel intval_less_than.simps(2,3,4,5) p val_to_bool.simps(2))
    obtain v2b v2v where v2v: "v2 = IntVal v2b v2v"
      by (metis Value.exhaust_sel intval_less_than.simps(6,7,8,9) p val_to_bool.simps(2))
    then have unfoldLessThanRHS: "intval_less_than v2 v1 =
                                 (bool_to_val (int_signed_value v2b v2v < int_signed_value v1b v1v))"
      using p v1v by force
    then have unfoldLessThanLHS: "intval_less_than v1 v2 =
                                 (bool_to_val (int_signed_value v1b v1v < int_signed_value v2b v2v))"
      using bool_to_val_bin.simps intval_less_than.simps(1) p v1v v2v val_to_bool.simps(2) by auto
    then have symmetry: "(int_signed_value v2b v2v < int_signed_value v1b v1v) \<longrightarrow>
                       (\<not>(int_signed_value v1b v1v < int_signed_value v2b v2v))"
      by simp
    then show ?thesis
      using p unfoldLessThanLHS unfoldLessThanRHS by fastforce
  qed done

lemma less_impliesnot_eq_val:
  "val_to_bool(intval_less_than v1 v2) \<longrightarrow> \<not>val_to_bool(intval_equals v1 v2)"
  using eq_impliesnot_less_val by blast

lemma logic_negate_type:
  assumes "[m, p] \<turnstile> UnaryExpr UnaryLogicNegation x \<mapsto> v"
  shows "\<exists>b v2. [m, p] \<turnstile> x \<mapsto> IntVal b v2"
  by (metis assms UnaryExprE intval_logic_negation.elims unary_eval.simps(4))

lemma intval_logic_negation_inverse:
  assumes "b > 0"
  assumes "x = IntVal b v"
  shows "val_to_bool (intval_logic_negation x) \<longleftrightarrow> \<not>(val_to_bool x)"
  by (cases x; auto simp: logic_negate_def assms)

lemma logic_negation_relation_tree:
  assumes "[m, p] \<turnstile> y \<mapsto> val"
  assumes "[m, p] \<turnstile> UnaryExpr UnaryLogicNegation y \<mapsto> invval"
  shows "val_to_bool val \<longleftrightarrow> \<not>(val_to_bool invval)"
  by (metis UnaryExprE evalDet eval_bits_1_64 logic_negate_type unary_eval.simps(4) assms
      intval_logic_negation_inverse)

text \<open>The following theorem shows that the known true/false rules are valid.\<close>

theorem implies_impliesnot_valid:
  shows "((q1 \<Rrightarrow> q2) \<longrightarrow> (q1 \<Zinj> q2)) \<and>
         ((q1 \<Rrightarrow>\<not> q2) \<longrightarrow> (q1 \<Zpinj> q2))"
          (is "(?imp \<longrightarrow> ?val) \<and> (?notimp \<longrightarrow> ?notval)")
proof (induct q1 q2  rule: implys_nimplys.induct)
  case (q_imp_q q)
  then show ?case 
    using evalDet by fastforce
next
  case (eq_impliesnot_less x y)
  then show ?case
    apply auto[1] using eq_impliesnot_less_val evalDet by blast
next
  case (eq_impliesnot_less_rev x y)
  then show ?case
    apply auto[1] using eq_impliesnot_less_rev_val evalDet by blast
next
  case (less_impliesnot_rev_less x y)
  then show ?case
    apply auto[1] using less_impliesnot_rev_less_val evalDet by blast
next
  case (less_impliesnot_eq x y)
  then show ?case
    apply auto[1] using less_impliesnot_eq_val evalDet by blast
next
  case (less_impliesnot_eq_rev x y)
  then show ?case
    apply auto[1] by (metis eq_impliesnot_less_rev_val evalDet)
next
  case (negate_true x y)
  then show ?case
    apply auto[1] by (metis logic_negation_relation_tree unary_eval.simps(4) unfold_unary)
next
  case (negate_false x y)
  then show ?case
    apply auto[1] by (metis UnaryExpr logic_negation_relation_tree unary_eval.simps(4))
qed

thm_oracles implies_impliesnot_valid


lemma logic_negation_relation:
  assumes "[g, m, p] \<turnstile> y \<mapsto> val"
  assumes "kind g neg = LogicNegationNode y"
  assumes "[g, m, p] \<turnstile> neg \<mapsto> invval"
  assumes "invval \<noteq> UndefVal"
  shows "val_to_bool val \<longleftrightarrow> \<not>(val_to_bool invval)"
  by (metis assms(1,2,3) LogicNegationNode encodeeval_def logic_negation_relation_tree repDet)


text \<open>
The following relation corresponds to the UnaryOpLogicNode.tryFold
and BinaryOpLogicNode.tryFold methods and their associated concrete implementations.

The relation determines if a logic operation can be shown true or false
through the stamp typing information.
\<close>
inductive tryFold :: "IRNode \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> bool \<Rightarrow> bool"
  where
  "\<lbrakk>alwaysDistinct (stamps x) (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerEqualsNode x y) stamps False" |
  "\<lbrakk>neverDistinct (stamps x) (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerEqualsNode x y) stamps True" |
  "\<lbrakk>is_IntegerStamp (stamps x);
    is_IntegerStamp (stamps y);
    stpi_upper (stamps x) < stpi_lower (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerLessThanNode x y) stamps True" |
  "\<lbrakk>is_IntegerStamp (stamps x);
    is_IntegerStamp (stamps y);
    stpi_lower (stamps x) \<ge> stpi_upper (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerLessThanNode x y) stamps False"

text \<open>
Proofs that show that when the stamp lookup function is well-formed,
the tryFold relation correctly predicts the output value with respect to
our evaluation semantics.
\<close>

inductive_cases StepE:
  "g, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m',h)"


lemma isStampEmpty:
  assumes "is_stamp_empty s"
  shows "\<not>(\<exists> val. valid_value val s)"
  using assms is_stamp_empty.simps apply (cases s; auto)
  by (metis linorder_not_le not_less_iff_gr_or_eq order.strict_trans valid_value.elims(2) valid_value.simps(1) valid_value.simps(5))

lemma join_lhs:
  assumes "is_IntegerStamp s1 \<and> is_IntegerStamp s2"
  shows "(valid_value v s1 \<and> valid_value v s2) \<longrightarrow> valid_value v (join s1 s2)"
  using assms apply (cases s1; cases s2; auto)
   apply (metis Value.inject(1) valid_int)
  by (smt (z3) valid_int valid_stamp.simps(1) valid_value.simps(1))

lemma join_rhs:
  assumes "is_IntegerStamp s1 \<and> is_IntegerStamp s2"
  assumes "valid_stamp s1 \<and> valid_stamp s2"
  assumes "valid_value v (join s1 s2)"
  shows "(valid_value v s1 \<and> valid_value v s2)"
  using assms apply (cases s1; cases s2; simp)
  by (smt (verit, best) assms(2) valid_int valid_value.simps(1) valid_value.simps(22))

lemma join:
  assumes "is_IntegerStamp s1 \<and> is_IntegerStamp s2"
  assumes "valid_stamp s1 \<and> valid_stamp s2"
  shows "(valid_value v s1 \<and> valid_value v s2) = valid_value v (join s1 s2)"
  using join_lhs join_rhs
  by (metis assms(1) assms(2))

lemma alwaysDistinct:
  assumes "wf_stamp g stamps"
  assumes "alwaysDistinct (stamps x) (stamps y)"
  assumes "is_IntegerStamp (stamps x) \<and> is_IntegerStamp (stamps y) \<and> valid_stamp (stamps x) \<and> valid_stamp (stamps y)"
  shows "\<not>(\<exists> val . ([g, m, p] \<turnstile> x \<mapsto> val) \<and> ([g, m, p] \<turnstile> y \<mapsto> val))"
proof -
  obtain stampx stampy where stampdef: "stampx = stamps x \<and> stampy = stamps y"
    by simp
  then have xv: "\<forall> xv . ([g, m, p] \<turnstile> x \<mapsto> xv) \<longrightarrow> valid_value xv stampx"
    by (meson assms(1) encodeeval_def eval_in_ids wf_stamp.elims(2))
  from stampdef have yv: "\<forall> yv . ([g, m, p] \<turnstile> y \<mapsto> yv) \<longrightarrow> valid_value yv stampy"
    by (meson assms(1) encodeeval_def eval_in_ids wf_stamp.elims(2))
  have "\<forall>v. valid_value v (join stampx stampy) = (valid_value v stampx \<and> valid_value v stampy)"
    using assms(3)
    by (simp add: join stampdef)
  then show ?thesis
    using assms unfolding alwaysDistinct.simps
    using isStampEmpty stampdef xv yv by blast
qed

lemma tryFoldIntegerEqualsAlwaysDistinct:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerEqualsNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "alwaysDistinct (stamps x) (stamps y)"
  shows "\<not>(val_to_bool v)"
proof -
  have "\<forall> val. \<not>(valid_value val (join (stamps x) (stamps y)))"
    by (smt (verit, best) is_stamp_empty.elims(2) valid_int valid_value.simps(1) assms(1,4)
        alwaysDistinct.simps)
  obtain xe ye where repr: "rep g nid (BinaryExpr BinIntegerEquals xe ye)"
    by (metis assms(2) assms(3) encodeeval_def rep_integer_equals)
  moreover have evale: "[m, p] \<turnstile> (BinaryExpr BinIntegerEquals xe ye) \<mapsto> v"
    by (metis assms(3) calculation encodeeval_def repDet)
  moreover have repsub: "rep g x xe \<and> rep g y ye"
    by (metis IRNode.distinct(1955) IRNode.distinct(1997) IRNode.inject(17) IntegerEqualsNodeE assms(2) calculation)
  ultimately obtain xv yv where evalsub: "[g, m, p] \<turnstile> x \<mapsto> xv \<and> [g, m, p] \<turnstile> y \<mapsto> yv"
    by (meson BinaryExprE encodeeval_def)
  have "valid_value xv (stamps x)"
    using assms(1) encode_in_ids encodeeval_def evalsub wf_stamp.simps by blast
  then have xint: "is_IntegerStamp (stamps x)"
    using assms(4) valid_value.elims(2) by fastforce
  have "valid_value yv (stamps y)"
    using assms(1) encode_in_ids encodeeval_def evalsub wf_stamp.simps by blast
  then have yint: "is_IntegerStamp (stamps y)"
    using assms(4) valid_value.elims(2) by fastforce
  have disjoint: "\<not>(\<exists> val . ([g, m, p] \<turnstile> x \<mapsto> val) \<and> ([g, m, p] \<turnstile> y \<mapsto> val))"
    using alwaysDistinct
    using assms(1) assms(4) xint yint
    by (metis \<open>\<forall>val::Value. \<not> valid_value val (join ((stamps::nat \<Rightarrow> Stamp) (x::nat)) (stamps (y::nat)))\<close> \<open>valid_value (xv::Value) ((stamps::nat \<Rightarrow> Stamp) (x::nat))\<close> \<open>valid_value (yv::Value) ((stamps::nat \<Rightarrow> Stamp) (y::nat))\<close> evalsub graphDet join_lhs)
  have "v = bin_eval BinIntegerEquals xv yv"
    by (metis BinaryExprE encodeeval_def evale evalsub graphDet repsub)
  also have "v \<noteq> UndefVal"
    using evale by auto
  ultimately have "\<exists>b1 b2. v =  bool_to_val_bin b1 b2 (xv = yv)"
    unfolding bin_eval.simps
    by (smt (z3) Value.inject(1) bool_to_val_bin.simps intval_equals.elims)
  then show ?thesis
    by (metis (mono_tags, lifting) \<open>(v::Value) \<noteq> UndefVal\<close> bool_to_val.elims bool_to_val_bin.simps disjoint evalsub val_to_bool.simps(1))
qed
thm_oracles tryFoldIntegerEqualsAlwaysDistinct

lemma unwrap_valid:
  assumes "0 < b \<and> b \<le> 64"
  assumes "take_bit (b::nat) (vv::64 word) = vv"
  shows "(vv::64 word) = take_bit b (word_of_int (int_signed_value (b::nat) (vv::64 word)))"
  using assms apply auto[1]
  by (simp add: take_bit_signed_take_bit)

lemma asConstant:
  assumes "asConstant s = val"
  assumes "val \<noteq> UndefVal"
  assumes "valid_value v s"
  shows "v = val"
proof -
  obtain b l h where s: "s = IntegerStamp b l h"
    using assms(1,2) by (cases s; auto)
  obtain vv where vdef: "v = IntVal b vv"
    using assms(3) s valid_int by blast
  have "l \<le> int_signed_value b vv \<and> int_signed_value b vv \<le> h"
    by (metis \<open>(v::Value) = IntVal (b::nat) (vv::64 word)\<close> assms(3) s valid_value.simps(1))
  then have veq: "int_signed_value b vv = l"
    by (smt (verit) asConstant.simps(1) assms(1) assms(2) s)
  have valdef: "val = new_int b (word_of_int l)"
    by (metis asConstant.simps(1) assms(1) assms(2) s)
  have "take_bit b vv = vv"
    by (metis \<open>(v::Value) = IntVal (b::nat) (vv::64 word)\<close> assms(3) s valid_value.simps(1))
  then show ?thesis
    using veq vdef valdef
    using assms(3) s unwrap_valid by force
qed

lemma tryFoldIntegerEqualsNeverDistinct:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerEqualsNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "neverDistinct (stamps x) (stamps y)"
  shows "val_to_bool v"
proof -
  obtain val where constx: "asConstant (stamps x) = val"
    by simp
  moreover have "val \<noteq> UndefVal"
    using assms(4) calculation by auto
  then have constx: "val = asConstant (stamps y)"
    using calculation assms(4) by force
  obtain xe ye where repr: "rep g nid (BinaryExpr BinIntegerEquals xe ye)"
    by (metis assms(2) assms(3) encodeeval_def rep_integer_equals)
  moreover have evale: "[m, p] \<turnstile> (BinaryExpr BinIntegerEquals xe ye) \<mapsto> v"
    by (metis assms(3) calculation encodeeval_def repDet)
  moreover have repsub: "rep g x xe \<and> rep g y ye"
    by (metis IRNode.distinct(1955) IRNode.distinct(1997) IRNode.inject(17) IntegerEqualsNodeE assms(2) calculation)
  ultimately obtain xv yv where evalsub: "[g, m, p] \<turnstile> x \<mapsto> xv \<and> [g, m, p] \<turnstile> y \<mapsto> yv"
    by (meson BinaryExprE encodeeval_def)
  have xvalid: "valid_value xv (stamps x)"
    using assms(1) encode_in_ids encodeeval_def evalsub wf_stamp.simps by blast
  then have xint: "is_IntegerStamp (stamps x)"
    using assms(4) valid_value.elims(2) by fastforce
  have yvalid: "valid_value yv (stamps y)"
    using assms(1) encode_in_ids encodeeval_def evalsub wf_stamp.simps by blast
  then have yint: "is_IntegerStamp (stamps y)"
    using assms(4) valid_value.elims(2) by fastforce
  have eq: "\<forall>v1 v2. (([g, m, p] \<turnstile> x \<mapsto> v1) \<and> ([g, m, p] \<turnstile> y \<mapsto> v2)) \<longrightarrow> v1 = v2"
    by (metis asConstant assms(4) encodeEvalDet evalsub neverDistinct.elims(1) xvalid yvalid)
  have "v = bin_eval BinIntegerEquals xv yv"
    by (metis BinaryExprE encodeeval_def evale evalsub graphDet repsub)
  also have "v \<noteq> UndefVal"
    using evale by auto
  ultimately have "\<exists>b1 b2. v =  bool_to_val_bin b1 b2 (xv = yv)"
    unfolding bin_eval.simps
    by (smt (z3) Value.inject(1) bool_to_val_bin.simps intval_equals.elims)
  then show ?thesis
    using \<open>(v::Value) \<noteq> UndefVal\<close> eq evalsub by fastforce
qed

lemma tryFoldIntegerLessThanTrue:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerLessThanNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "stpi_upper (stamps x) < stpi_lower (stamps y)"
  shows "val_to_bool v"
proof -
  obtain xe ye where repr: "rep g nid (BinaryExpr BinIntegerLessThan xe ye)"
    by (metis assms(2) assms(3) encodeeval_def rep_integer_less_than)
  moreover have evale: "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan xe ye) \<mapsto> v"
    by (metis assms(3) calculation encodeeval_def repDet)
  moreover have repsub: "rep g x xe \<and> rep g y ye"
    by (metis IRNode.distinct(2047) IRNode.distinct(2089) IRNode.inject(18) IntegerLessThanNodeE assms(2) repr)
  ultimately obtain xv yv where evalsub: "[g, m, p] \<turnstile> x \<mapsto> xv \<and> [g, m, p] \<turnstile> y \<mapsto> yv"
    by (meson BinaryExprE encodeeval_def)
  have vval: "v = intval_less_than xv yv"
    by (metis BinaryExprE bin_eval.simps(14) encodeEvalDet encodeeval_def evale evalsub repsub)
  then obtain b xvv where "xv = IntVal b xvv"
    by (metis bin_eval.simps(14) defined_eval_is_intval evale evaltree_not_undef is_IntVal_def)
  also have xvalid: "valid_value xv (stamps x)"
    by (meson assms(1) encodeeval_def eval_in_ids evalsub wf_stamp.elims(2))
  then obtain xl xh where xstamp: "stamps x = IntegerStamp b xl xh"
    using calculation valid_value.simps apply (cases "stamps x"; auto)
    by presburger
  from vval obtain yvv where yint: "yv = IntVal b yvv"
    by (metis Value.collapse(1) bin_eval.simps(14) bool_to_val_bin.simps calculation defined_eval_is_intval evale evaltree_not_undef intval_less_than.simps(1))
  then have yvalid: "valid_value yv (stamps y)"
    using assms(1) encodeeval_def evalsub no_encoding wf_stamp.simps by blast
  then obtain yl yh where ystamp: "stamps y = IntegerStamp b yl yh"
    using calculation yint valid_value.simps apply (cases "stamps y"; auto)
    by presburger
  have "int_signed_value b xvv \<le> xh"
    using calculation valid_value.simps(1) xstamp xvalid by presburger
  moreover have "yl \<le> int_signed_value b yvv"
    using valid_value.simps(1) yint ystamp yvalid by presburger
  moreover have "xh < yl"
    using assms(4) xstamp ystamp by auto
  ultimately have "int_signed_value b xvv < int_signed_value b yvv"
    by linarith
  then have "val_to_bool (intval_less_than xv yv)"
    by (simp add: \<open>(xv::Value) = IntVal (b::nat) (xvv::64 word)\<close> yint)
  then show ?thesis
    by (simp add: vval)
qed

lemma tryFoldIntegerLessThanFalse:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerLessThanNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "stpi_lower (stamps x) \<ge> stpi_upper (stamps y)"
  shows "\<not>(val_to_bool v)"
proof -
  obtain xe ye where repr: "rep g nid (BinaryExpr BinIntegerLessThan xe ye)"
    by (metis assms(2) assms(3) encodeeval_def rep_integer_less_than)
  moreover have evale: "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan xe ye) \<mapsto> v"
    by (metis assms(3) calculation encodeeval_def repDet)
  moreover have repsub: "rep g x xe \<and> rep g y ye"
    by (metis IRNode.distinct(2047) IRNode.distinct(2089) IRNode.inject(18) IntegerLessThanNodeE assms(2) repr)
  ultimately obtain xv yv where evalsub: "[g, m, p] \<turnstile> x \<mapsto> xv \<and> [g, m, p] \<turnstile> y \<mapsto> yv"
    by (meson BinaryExprE encodeeval_def)
  have vval: "v = intval_less_than xv yv"
    by (metis BinaryExprE bin_eval.simps(14) encodeEvalDet encodeeval_def evale evalsub repsub)
  then obtain b xvv where "xv = IntVal b xvv"
    by (metis bin_eval.simps(14) defined_eval_is_intval evale evaltree_not_undef is_IntVal_def)
  also have xvalid: "valid_value xv (stamps x)"
    by (meson assms(1) encodeeval_def eval_in_ids evalsub wf_stamp.elims(2))
  then obtain xl xh where xstamp: "stamps x = IntegerStamp b xl xh"
    using calculation valid_value.simps apply (cases "stamps x"; auto)
    by presburger
  from vval obtain yvv where yint: "yv = IntVal b yvv"
    by (metis Value.collapse(1) bin_eval.simps(14) bool_to_val_bin.simps calculation defined_eval_is_intval evale evaltree_not_undef intval_less_than.simps(1))
  then have yvalid: "valid_value yv (stamps y)"
    using assms(1) encodeeval_def evalsub no_encoding wf_stamp.simps by blast
  then obtain yl yh where ystamp: "stamps y = IntegerStamp b yl yh"
    using calculation yint valid_value.simps apply (cases "stamps y"; auto)
    by presburger
  have "xl \<le> int_signed_value b xvv"
    using calculation valid_value.simps(1) xstamp xvalid by presburger
  moreover have "int_signed_value b yvv \<le> yh"
    using valid_value.simps(1) yint ystamp yvalid by presburger
  moreover have "xl \<ge> yh"
    using assms(4) xstamp ystamp by auto
  ultimately have "int_signed_value b xvv \<ge> int_signed_value b yvv"
    by linarith
  then have "\<not>(val_to_bool (intval_less_than xv yv))"
    by (simp add: \<open>(xv::Value) = IntVal (b::nat) (xvv::64 word)\<close> yint)
  then show ?thesis
    by (simp add: vval)
qed

theorem tryFoldProofTrue:
  assumes "wf_stamp g stamps"
  assumes "tryFold (kind g nid) stamps True"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  shows "val_to_bool v"
  using assms(2) proof (induction "kind g nid" stamps True rule: tryFold.induct)
case (1 stamps x y)
  then show ?case
    using tryFoldIntegerEqualsAlwaysDistinct assms by force
next
  case (2 stamps x y)
  then show ?case
    by (smt (verit, best) one_neq_zero tryFold.cases tryFoldIntegerEqualsNeverDistinct assms
        tryFoldIntegerLessThanTrue val_to_bool.simps(1))
next
  case (3 stamps x y)
  then show ?case
    by (smt (verit, best) one_neq_zero tryFold.cases tryFoldIntegerEqualsNeverDistinct assms
        val_to_bool.simps(1) tryFoldIntegerLessThanTrue)
next
case (4 stamps x y)
  then show ?case
    by force
qed

theorem tryFoldProofFalse:
  assumes "wf_stamp g stamps"
  assumes "tryFold (kind g nid) stamps False"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  shows "\<not>(val_to_bool v)"
using assms(2) proof (induction "kind g nid" stamps False rule: tryFold.induct)
case (1 stamps x y)
  then show ?case
    by (smt (verit) tryFoldIntegerLessThanFalse tryFoldIntegerEqualsAlwaysDistinct tryFold.cases
        tryFoldIntegerEqualsNeverDistinct val_to_bool.simps(1) assms)
next
case (2 stamps x y)
  then show ?case
    by blast
next
  case (3 stamps x y)
  then show ?case
    by blast
next
  case (4 stamps x y)
  then show ?case
    by (smt (verit, del_insts) tryFold.cases tryFoldIntegerEqualsAlwaysDistinct val_to_bool.simps(1)
        tryFoldIntegerLessThanFalse assms)
qed

text \<open>
Perform conditional elimination rewrites on the graph for a particular node.

In order to determine conditional eliminations appropriately the rule needs two
data structures produced by static analysis.
The first parameter is the set of IRNodes that we know result in a true value
when evaluated.
The second parameter is a mapping from node identifiers to the flow-sensitive stamp.

The relation transforms the third parameter to the fifth parameter for a node identifier
which represents the fourth parameter.
\<close>
inductive ConditionalEliminationStep :: 
  "IRExpr set \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> IRGraph \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> bool" where
  impliesTrue:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    g \<turnstile> cid \<simeq> cond;
    \<exists> ce \<in> conds . (ce \<Rrightarrow> cond);
    g' = constantCondition True ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'" |

  impliesFalse:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    g \<turnstile> cid \<simeq> cond;
    \<exists> ce \<in> conds . (ce \<Rrightarrow>\<not> cond);
    g' = constantCondition False ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'" |

  tryFoldTrue:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    tryFold (kind g cid) stamps True;
    g' = constantCondition True ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'" |

  tryFoldFalse:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    tryFold (kind g cid) stamps False;
    g' = constantCondition False ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps g ifcond g'"


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationStep .

thm ConditionalEliminationStep.equation

subsection \<open>Control-flow Graph Traversal\<close>

type_synonym Seen = "ID set"
type_synonym Condition = "IRExpr"
type_synonym Conditions = "Condition list"
type_synonym StampFlow = "(ID \<Rightarrow> Stamp) list"

text \<open>
nextEdge helps determine which node to traverse next by returning the first successor
edge that isn't in the set of already visited nodes.
If there is not an appropriate successor, None is returned instead.
\<close>
fun nextEdge :: "Seen \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> ID option" where
  "nextEdge seen nid g = 
    (let nids = (filter (\<lambda>nid'. nid' \<notin> seen) (successors_of (kind g nid))) in 
     (if length nids > 0 then Some (hd nids) else None))"

text \<open>
pred determines which node, if any, acts as the predecessor of another.

Merge nodes represent a special case where-in the predecessor exists as
an input edge of the merge node, to simplify the traversal we treat only
the first input end node as the predecessor, ignoring that multiple nodes
may act as a successor.

For all other nodes, the predecessor is the first element of the predecessors set.
Note that in a well-formed graph there should only be one element in the predecessor set.\<close>
fun pred :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID option" where
  "pred g nid = (case kind g nid of
    (MergeNode ends _ _) \<Rightarrow> Some (hd ends) |
    _ \<Rightarrow> 
      (if IRGraph.predecessors g nid = {} 
        then None else
        Some (hd (sorted_list_of_set (IRGraph.predecessors g nid)))
      )
  )"


text \<open>
When the basic block of an if statement is entered, we know that the condition of the
preceding if statement must be true.
As in the GraalVM compiler, we introduce the registerNewCondition funciton which roughly
corresponds to the ConditionalEliminationPhase.registerNewCondition.
This method updates the flow-sensitive stamp information based on the condition which
we know must be true. 
\<close>
fun clip_upper :: "Stamp \<Rightarrow> int \<Rightarrow> Stamp" where
  "clip_upper (IntegerStamp b l h) c = (IntegerStamp b l c)" |
  "clip_upper s c = s"
fun clip_lower :: "Stamp \<Rightarrow> int \<Rightarrow> Stamp" where
  "clip_lower (IntegerStamp b l h) c = (IntegerStamp b c h)" |
  "clip_lower s c = s"

fun registerNewCondition :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> (ID \<Rightarrow> Stamp)" where
  (* constrain equality by joining the stamps *)
  "registerNewCondition g (IntegerEqualsNode x y) stamps =
    (stamps
      (x := join (stamps x) (stamps y)))
      (y := join (stamps x) (stamps y))" |
  (* constrain less than by removing overlapping stamps *)
  "registerNewCondition g (IntegerLessThanNode x y) stamps =
    (stamps
      (x := clip_upper (stamps x) (stpi_lower (stamps y))))
      (y := clip_lower (stamps y) (stpi_upper (stamps x)))" |
  "registerNewCondition g _ stamps = stamps"

fun hdOr :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "hdOr (x # xs) de = x" |
  "hdOr [] de = de"

text \<open>
The Step relation is a small-step traversal of the graph which handles transitions between
individual nodes of the graph.

It relates a pairs of tuple of the current node, the set of seen nodes, 
the always true stack of IfNode conditions, and the flow-sensitive stamp information.
\<close>
inductive Step 
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> Conditions \<times> StampFlow) \<Rightarrow> (ID \<times> Seen \<times> Conditions \<times> StampFlow) option \<Rightarrow> bool"
  for g where
  \<comment> \<open>
  Hit a BeginNode with an IfNode predecessor which represents
  the start of a basic block for the IfNode.
     1. nid' will be the successor of the begin node.
     2. Find the first and only predecessor.
     3. Extract condition from the preceding IfNode.
     4. Negate condition if the begin node is second branch
        (we've taken the else branch of the condition)
     5. Add the condition or the negated condition to stack
     6. Perform any stamp updates based on the condition using
        the registerNewCondition function and place them on the
        top of the stack of stamp information
  \<close>
  "\<lbrakk>kind g nid = BeginNode nid';

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    Some ifcond = pred g nid;
    kind g ifcond = IfNode cond t f;

    i = find_index nid (successors_of (kind g ifcond));
    c = (if i = 0 then kind g cond else LogicNegationNode cond);
    rep g cond ce;
    ce' = (if i = 0 then ce else UnaryExpr UnaryLogicNegation ce);
    conds' = ce' # conds;

    flow' = registerNewCondition g c (hdOr flow (stamp g))\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow' # flow))" |

  \<comment> \<open>
  Hit an EndNode
     1. nid' will be the usage of EndNode
     2. pop the conditions and stamp stack
  \<close>
  "\<lbrakk>kind g nid = EndNode;

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    nid' = any_usage g nid;

    conds' = tl conds;
    flow' = tl flow\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'))" |

  \<comment> \<open>We can find a successor edge that is not in seen, go there\<close>
  "\<lbrakk>\<not>(is_EndNode (kind g nid));
    \<not>(is_BeginNode (kind g nid));

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    Some nid' = nextEdge seen' nid g\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds, flow) (Some (nid', seen', conds, flow))" |

  \<comment> \<open>We can cannot find a successor edge that is not in seen, give back None\<close>
  "\<lbrakk>\<not>(is_EndNode (kind g nid));
    \<not>(is_BeginNode (kind g nid));

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    None = nextEdge seen' nid g\<rbrakk>
    \<Longrightarrow> Step g (nid, seen, conds, flow) None" |

  \<comment> \<open>We've already seen this node, give back None\<close>
  "\<lbrakk>nid \<in> seen\<rbrakk> \<Longrightarrow> Step g (nid, seen, conds, flow) None"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) Step .

text \<open>
The ConditionalEliminationPhase relation is responsible for combining
the individual traversal steps from the Step relation and the optimizations
from the ConditionalEliminationStep relation to perform a transformation of the
whole graph.
\<close>

inductive ConditionalEliminationPhase 
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> Conditions \<times> StampFlow) \<Rightarrow> IRGraph \<Rightarrow> bool" where

  \<comment> \<open>Can do a step and optimise for the current node\<close>
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    ConditionalEliminationStep (set conds) (hdOr flow (stamp g)) g nid g';
    
    ConditionalEliminationPhase g' (nid', seen', conds', flow') g''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds, flow) g''" |

  \<comment> \<open>Can do a step, matches whether optimised or not causing non-determinism
      We need to find a way to negate ConditionalEliminationStep\<close>
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    
    ConditionalEliminationPhase g (nid', seen', conds', flow') g'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds, flow) g'" |

  \<comment> \<open>Can't do a step but there is a predecessor we can backtrace to\<close>
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    Some nid' = pred g nid;
    seen' = {nid} \<union> seen;
    ConditionalEliminationPhase g (nid', seen', conds, flow) g'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds, flow) g'" |

  \<comment> \<open>Can't do a step and have no predecessors so terminate\<close>
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    None = pred g nid\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase g (nid, seen, conds, flow) g"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationPhase .

definition runConditionalElimination :: "IRGraph \<Rightarrow> IRGraph" where
  "runConditionalElimination g = 
    (Predicate.the (ConditionalEliminationPhase_i_i_o g (0, {}, ([], []))))"

(*

inductive ConditionalEliminationPhaseWithTrace\<^marker>\<open>tag invisible\<close>
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> Conditions \<times> StampFlow) \<Rightarrow> ID list \<Rightarrow> IRGraph \<Rightarrow> ID list \<Rightarrow> Conditions \<Rightarrow> bool" where\<^marker>\<open>tag invisible\<close>

  (* Can do a step and optimise for the current nid *)
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    ConditionalEliminationStep (set conds) (hdOr flow (stamp g)) g nid g';
    
    ConditionalEliminationPhaseWithTrace g' (nid', seen', conds', flow') (nid # t) g'' t' conds''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g'' t' conds''" |

  (* Can do a step, matches whether optimised or not causing non-determinism
     Need to find a way to negate ConditionalEliminationStep *)
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    
    ConditionalEliminationPhaseWithTrace g (nid', seen', conds', flow') (nid # t) g' t' conds''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g' t' conds''" |

  (* Can't do a step but there is a predecessor we can backtrace to *)
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    Some nid' = pred g nid;
    seen' = {nid} \<union> seen;
    ConditionalEliminationPhaseWithTrace g (nid', seen', conds, flow) (nid # t) g' t' conds'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g' t' conds'" |

  (* Can't do a step and have no predecessors do terminate *)
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    None = pred g nid\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g (nid # t) conds"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationPhaseWithTrace .


lemma IfNodeStepE: "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h) \<Longrightarrow>
  (\<And>cond tb fb val.
        kind g nid = IfNode cond tb fb \<Longrightarrow>
        nid' = (if val_to_bool val then tb else fb) \<Longrightarrow> 
        [g, m, p] \<turnstile> kind g cond \<mapsto> val \<Longrightarrow> m' = m)"
  using StepE
  by (smt (verit, best) IfNode Pair_inject stepDet)

lemma ifNodeHasCondEvalStutter:
  assumes "(g m p h \<turnstile> nid \<leadsto> nid')"
  assumes "kind g nid = IfNode cond t f"
  shows "\<exists> v. ([g, m, p] \<turnstile> kind g cond \<mapsto> v)"
  using IfNodeStepE assms(1) assms(2)  stutter.cases
  by (meson IfNodeCond)

lemma ifNodeHasCondEval:
  assumes "(g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h'))"
  assumes "kind g nid = IfNode cond t f"
  shows "\<exists> v. ([g, m, p] \<turnstile> kind g cond \<mapsto> v)"
  using IfNodeStepE assms(1) assms(2)
  by (smt (z3) IRNode.disc(932) IRNode.simps(938) IRNode.simps(958) IRNode.simps(972) IRNode.simps(974) IRNode.simps(978) Pair_inject StutterStep ifNodeHasCondEvalStutter is_AbstractEndNode.simps is_EndNode.simps(12) step.cases)


lemma replace_if_t:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "[g, m, p] \<turnstile> kind g cond \<mapsto> bool"
  assumes "val_to_bool bool"
  assumes g': "g' = replace_usages nid tb g"
  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longleftrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
proof -
  have g1step: "g, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    by (meson IfNode assms(1) assms(2) assms(3))
  have g2step: "g', p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using g' unfolding replace_usages.simps
    by (simp add: stepRefNode)
  from g1step g2step show ?thesis
    using StutterStep by blast
qed

lemma replace_if_t_imp:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "[g, m, p] \<turnstile> kind g cond \<mapsto> bool"
  assumes "val_to_bool bool"
  assumes g': "g' = replace_usages nid tb g"
  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
  using replace_if_t assms by blast

lemma replace_if_f:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "[g, m, p] \<turnstile> kind g cond \<mapsto> bool"
  assumes "\<not>(val_to_bool bool)"
  assumes g': "g' = replace_usages nid fb g"
  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longleftrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
proof -
  have g1step: "g, p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    by (meson IfNode assms(1) assms(2) assms(3))
  have g2step: "g', p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    using g' unfolding replace_usages.simps
    by (simp add: stepRefNode)
  from g1step g2step show ?thesis
    using StutterStep by blast
qed

text \<open>
Prove that the individual conditional elimination rules are correct
with respect to preservation of stuttering steps.
\<close>
lemma ConditionalEliminationStepProof:
  assumes wg: "wf_graph g"
  assumes ws: "wf_stamps g"
  assumes wv: "wf_values g"
  assumes nid: "nid \<in> ids g"
  assumes conds_valid: "\<forall> c \<in> conds . \<exists> v. ([g, m, p] \<turnstile> c \<mapsto> v) \<and> val_to_bool v"
  assumes ce: "ConditionalEliminationStep conds stamps g nid g'"

  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
  using ce using assms
proof (induct g nid g' rule: ConditionalEliminationStep.induct)
  case (impliesTrue g ifcond cid t f cond conds g')
  show ?case proof (cases "(g m p h \<turnstile> ifcond \<leadsto> nid')")
    case True
    obtain condv where condv: "[g, m, p] \<turnstile> kind g cid \<mapsto> condv"
      using implies.simps impliesTrue.hyps(3) impliesTrue.prems(4)
      using impliesTrue.hyps(2) True
      by (metis ifNodeHasCondEvalStutter impliesTrue.hyps(1))
    have condvTrue: "val_to_bool condv"
      by (metis condition_implies.intros(2) condv impliesTrue.hyps(2) impliesTrue.hyps(3) impliesTrue.prems(1) impliesTrue.prems(3) impliesTrue.prems(5) implies_true_valid)
    then show ?thesis
      using constantConditionValid 
      using impliesTrue.hyps(1) condv impliesTrue.hyps(4)
      by blast
  next
    case False
    then show ?thesis by auto
  qed
next
  case (impliesFalse g ifcond cid t f cond conds g')
  then show ?case 
  proof (cases "(g m p h \<turnstile> ifcond \<leadsto> nid')")
    case True
    obtain condv where condv: "[g, m, p] \<turnstile> kind g cid \<mapsto> condv"
      using ifNodeHasCondEvalStutter impliesFalse.hyps(1)
      using True by blast
    have condvFalse: "False = val_to_bool condv"
      by (metis condition_implies.intros(2) condv impliesFalse.hyps(2) impliesFalse.hyps(3) impliesFalse.prems(1) impliesFalse.prems(3) impliesFalse.prems(5) implies_false_valid)
    then show ?thesis
      using constantConditionValid 
      using impliesFalse.hyps(1) condv impliesFalse.hyps(4)
      by blast
  next
    case False
    then show ?thesis
      by auto
  qed
next
  case (tryFoldTrue g ifcond cid t f cond g' conds)
  then show ?case using constantConditionValid tryFoldProofTrue
    using StutterStep constantConditionTrue by metis
next
  case (tryFoldFalse g ifcond cid t f cond g' conds)
  then show ?case using constantConditionValid tryFoldProofFalse
    using StutterStep constantConditionFalse by metis
qed


text \<open>
Prove that the individual conditional elimination rules are correct
with respect to finding a bisimulation between the unoptimized and optimized graphs.
\<close>
lemma ConditionalEliminationStepProofBisimulation:
  assumes wf: "wf_graph g \<and> wf_stamp g stamps \<and> wf_values g"
  assumes nid: "nid \<in> ids g"
  assumes conds_valid: "\<forall> c \<in> conds . \<exists> v. ([g, m, p] \<turnstile> c \<mapsto> v) \<and> val_to_bool v"
  assumes ce: "ConditionalEliminationStep conds stamps g nid g'"
  assumes gstep: "\<exists> h nid'. (g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h))" (* we don't yet consider optimizations which produce a step that didn't already exist *)

  shows "nid | g \<sim> g'"
  using ce gstep using assms
proof (induct g nid g' rule: ConditionalEliminationStep.induct)
  case (impliesTrue g ifcond cid t f cond conds g' stamps)
  from impliesTrue(5) obtain h where gstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    by (metis IfNode StutterStep condition_implies.intros(2) ifNodeHasCondEvalStutter impliesTrue.hyps(1) impliesTrue.hyps(2) impliesTrue.hyps(3) impliesTrue.prems(2) impliesTrue.prems(4) implies_true_valid)
  have "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using constantConditionTrue impliesTrue.hyps(1) impliesTrue.hyps(4) by blast
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
next
  case (impliesFalse g ifcond cid t f cond conds g' stamps)
  from impliesFalse(5) obtain h where gstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    by (metis IfNode condition_implies.intros(2) ifNodeHasCondEval impliesFalse.hyps(1) impliesFalse.hyps(2) impliesFalse.hyps(3) impliesFalse.prems(2) impliesFalse.prems(4) implies_false_valid)
  have "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using constantConditionFalse impliesFalse.hyps(1) impliesFalse.hyps(4) by blast
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
next
  case (tryFoldTrue g ifcond cid t f cond stamps g' conds)
  from tryFoldTrue(5) obtain val where "[g, m, p] \<turnstile> kind g cid \<mapsto> val"
    using ifNodeHasCondEval tryFoldTrue.hyps(1) by blast
  then have "val_to_bool val"
    using tryFoldProofTrue tryFoldTrue.prems(2) tryFoldTrue(3) 
    by blast
  then obtain h where gstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using tryFoldTrue(5)
    by (meson IfNode \<open>[g, m, p] \<turnstile> kind g cid \<mapsto> val\<close> tryFoldTrue.hyps(1))
  have "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using constantConditionTrue tryFoldTrue.hyps(1) tryFoldTrue.hyps(4) by presburger
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
next
  case (tryFoldFalse g ifcond cid t f cond stamps g' conds)
  from tryFoldFalse(5) obtain h where gstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    by (meson IfNode ifNodeHasCondEval tryFoldFalse.hyps(1) tryFoldFalse.hyps(3) tryFoldFalse.prems(2) tryFoldProofFalse)
  have "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using constantConditionFalse tryFoldFalse.hyps(1) tryFoldFalse.hyps(4) by blast
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
qed


text \<open>Mostly experimental proofs from here on out.\<close>

experiment begin
lemma if_step:
  assumes "nid \<in> ids g"
  assumes "(kind g nid) \<in> control_nodes"
  shows "(g m p h \<turnstile> nid \<leadsto> nid')"
  using assms apply (cases "kind g nid") sorry

lemma StepConditionsValid:
  assumes "\<forall> cond \<in> set conds. ([g, m, p] \<turnstile> cond \<mapsto> v) \<and> val_to_bool v"
  assumes "Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'))"
  shows "\<forall> cond \<in> set conds'. ([g, m, p] \<turnstile> cond \<mapsto> v) \<and> val_to_bool v"
  using assms(2) 
proof (induction "(nid, seen, conds, flow)" "Some (nid', seen', conds', flow')" rule: Step.induct)
  case (1 ifcond cond t f i c)
  obtain cv where cv: "[g, m, p] \<turnstile> c \<mapsto> cv"
    sorry
  have cvt: "val_to_bool cv"
    sorry
  have "set conds' = {c} \<union> set conds"
    using "1.hyps"(8) by auto
  then show ?case using cv cvt assms(1) sorry
next
  case (2)
  from 2(5) have "set conds' \<subseteq> set conds"
    by (metis list.sel(2) list.set_sel(2) subsetI)
  then show ?case using assms(1)
    by blast
next
case (3)
  then show ?case
    using assms(1) by force
qed

lemma ConditionalEliminationPhaseProof:
  assumes "wf_graph g"
  assumes "wf_stamps g"
  assumes "ConditionalEliminationPhase g (0, {}, [], []) g'"
  
  shows "\<exists>nid' .(g m p h \<turnstile> 0 \<leadsto> nid') \<longrightarrow> (g' m p h \<turnstile> 0 \<leadsto> nid')"
proof -
  have "0 \<in> ids g"
    using assms(1) wf_folds by blast
  show ?thesis
using assms(3) assms proof (induct rule: ConditionalEliminationPhase.induct)
case (1 g nid g' succs nid' g'')
  then show ?case sorry
next
  case (2 succs g nid nid' g'')
  then show ?case sorry
next
  case (3 succs g nid)
  then show ?case 
    by simp
next
  case (4)
  then show ?case sorry
qed
qed
end
*)

end