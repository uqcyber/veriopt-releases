section \<open>Data-flow Expression-Tree Theorems\<close>

theory IRTreeEvalThms
  imports
    TreeToGraph
begin


subsection \<open>Extraction and Evaluation of Expression Trees is Deterministic.\<close>

text \<open>First, we prove some extra rules that relate each
  type of IRNode to the corresponding IRExpr type that 'rep' will produce.
  These are very helpful for proving that 'rep' is deterministic.
\<close>

lemma rep_constant: 
  "g \<turnstile> n \<simeq> e \<Longrightarrow> 
   kind g n = ConstantNode c \<Longrightarrow> 
   e = ConstantExpr c"
  by (induction rule: rep.induct; auto)
  
lemma rep_parameter: 
  "g \<turnstile> n \<simeq> e \<Longrightarrow> 
   kind g n = ParameterNode i \<Longrightarrow>
   (\<exists>s. e = ParameterExpr i s)"
  by (induction rule: rep.induct; auto)

lemma rep_conditional:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = ConditionalNode c t f \<Longrightarrow>
   (\<exists> ce te fe. e = ConditionalExpr ce te fe)"
  by (induction rule: rep.induct; auto)

lemma rep_abs:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = AbsNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryAbs xe)"
  by (induction rule: rep.induct; auto)

lemma rep_not:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = NotNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryNot xe)"
  by (induction rule: rep.induct; auto)

lemma rep_negate:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = NegateNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryNeg xe)"
  by (induction rule: rep.induct; auto)

lemma rep_logicnegation:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = LogicNegationNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryLogicNegation xe)"
  by (induction rule: rep.induct; auto)

lemma rep_add:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = AddNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinAdd xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_sub:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = SubNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinSub xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_mul:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = MulNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinMul xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_and:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = AndNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinAnd xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_or:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = OrNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinOr xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_xor:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = XorNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinXor xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_below:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerBelowNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerBelow xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_equals:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerEqualsNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerEquals xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_less_than:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerLessThanNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerLessThan xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_narrow:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = NarrowNode ib rb x \<Longrightarrow>
   (\<exists>x. e = UnaryExpr (UnaryNarrow ib rb) x)"
  by (induction rule: rep.induct; auto)
 
lemma rep_sign_extend:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = SignExtendNode ib rb x \<Longrightarrow>
   (\<exists>x. e = UnaryExpr (UnarySignExtend ib rb) x)"
  by (induction rule: rep.induct; auto)

lemma rep_zero_extend:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = ZeroExtendNode ib rb x \<Longrightarrow>
   (\<exists>x. e = UnaryExpr (UnaryZeroExtend ib rb) x)"
  by (induction rule: rep.induct; auto)

lemma rep_load_field:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   is_preevaluated (kind g n) \<Longrightarrow>
   (\<exists>s. e = LeafExpr n s)"
  by (induction rule: rep.induct; auto)

lemmas reps =
  rep_constant
  rep_parameter
  rep_conditional
  rep_abs
  rep_not
  rep_negate
  rep_logicnegation
  rep_add
  rep_sub
  rep_mul
  rep_and
  rep_or
  rep_xor
  rep_integer_below
  rep_integer_equals
  rep_integer_less_than
  rep_narrow
  rep_sign_extend
  rep_zero_extend
  rep_load_field


text \<open>Now we can prove that 'rep' and 'eval', and their list versions, are deterministic.
\<close>
lemma repDet:
  shows "(g \<turnstile> n \<simeq> e1) \<Longrightarrow> (g \<turnstile> n \<simeq> e2) \<Longrightarrow> e1 = e2"
proof (induction arbitrary: e2 rule: "rep.induct")
  case (ConstantNode n c)
  then show ?case using rep_constant by auto
next
  case (ParameterNode n i s)
  then show ?case using rep_parameter by auto
next
  case (ConditionalNode n c t f ce te fe)
  then show ?case 
    by (metis rep_conditional ConditionalNodeE IRNode.inject(6)) 
next
  case (AbsNode n x xe)
  then show ?case 
    by (metis rep_abs AbsNodeE IRNode.inject(1))
next
  case (NotNode n x xe)
  then show ?case
    by (metis IRNode.inject(31) NotNodeE rep_not)
next
  case (NegateNode n x xe)
  then show ?case
    by (metis  IRNode.inject(28) NegateNodeE rep_negate)
next
  case (LogicNegationNode n x xe)
  then show ?case
    by (metis IRNode.inject(20) LogicNegationNodeE rep_logicnegation)
next
  case (AddNode n x y xe ye)
  then show ?case
    by (metis AddNodeE IRNode.inject(2) rep_add) 
next
  case (MulNode n x y xe ye)
  then show ?case
    by (metis IRNode.inject(26) MulNodeE rep_mul)
next
  case (SubNode n x y xe ye)
  then show ?case
    by (metis IRNode.inject(42) SubNodeE rep_sub)
next
  case (AndNode n x y xe ye)
  then show ?case
    by (metis AndNodeE IRNode.inject(3) rep_and)
next
  case (OrNode n x y xe ye)
  then show ?case
  by (metis IRNode.inject(32) OrNodeE rep_or)
next
  case (XorNode n x y xe ye)
  then show ?case
    by (metis IRNode.inject(46) XorNodeE rep_xor)
next
  case (IntegerBelowNode n x y xe ye)
  then show ?case
    by (metis IRNode.inject(12) IntegerBelowNodeE rep_integer_below)
next
  case (IntegerEqualsNode n x y xe ye)
  then show ?case
    by (metis IRNode.inject(13) IntegerEqualsNodeE rep_integer_equals)
next
  case (IntegerLessThanNode n x y xe ye)
  then show ?case
    by (metis IRNode.inject(14) IntegerLessThanNodeE rep_integer_less_than)
next
  case (NarrowNode n x xe)
  then show ?case
    by (metis IRNode.inject(27) NarrowNodeE rep_narrow)
next
  case (SignExtendNode n x xe)
  then show ?case
    by (metis IRNode.inject(37) SignExtendNodeE rep_sign_extend)
next
  case (ZeroExtendNode n x xe)
  then show ?case
    by (metis IRNode.inject(47) ZeroExtendNodeE rep_zero_extend)
next
  case (LeafNode n s)
  then show ?case using rep_load_field LeafNodeE by blast 
qed

lemma repAllDet:
  "g \<turnstile> xs \<simeq>\<^sub>L e1 \<Longrightarrow>
   g \<turnstile> xs \<simeq>\<^sub>L e2 \<Longrightarrow>
   e1 = e2"
proof (induction arbitrary: e2 rule: "replist.induct")
  case RepNil
  then show ?case
    using replist.cases by auto 
next
  case (RepCons x xe xs xse)
  then show ?case
    by (metis list.distinct(1) list.sel(1) list.sel(3) repDet replist.cases) 
qed


lemma evalDet:
  "[m,p] \<turnstile> e \<mapsto> v1 \<Longrightarrow> 
   [m,p] \<turnstile> e \<mapsto> v2 \<Longrightarrow>
   v1 = v2"
  apply (induction arbitrary: v2 rule: "evaltree.induct")
  by (elim EvalTreeE; auto)+

lemma evalAllDet:
  "[m,p] \<turnstile> e \<mapsto>\<^sub>L v1 \<Longrightarrow> 
   [m,p] \<turnstile> e \<mapsto>\<^sub>L v2 \<Longrightarrow>
   v1 = v2"
  apply (induction arbitrary: v2 rule: "evaltrees.induct")
   apply (elim EvalTreeE; auto)
  using evalDet by force

lemma encodeEvalDet:
  "[g,m,p] \<turnstile> e \<mapsto> v1 \<Longrightarrow> 
   [g,m,p] \<turnstile> e \<mapsto> v2 \<Longrightarrow>
   v1 = v2"
  by (metis encodeeval_def evalDet repDet)

lemma graphDet: "([g,m,p] \<turnstile> nid \<mapsto> v1) \<and> ([g,m,p] \<turnstile> nid \<mapsto> v2) \<Longrightarrow> v1 = v2"
  using encodeEvalDet by blast

text \<open>A valid value cannot be $UndefVal$.\<close>
lemma valid_not_undef:
  assumes a1: "valid_value s val"
  assumes a2: "s \<noteq> VoidStamp"
  shows "val \<noteq> UndefVal"
  apply (rule valid_value.elims(1)[of s val True])
  using a1 a2 by auto

(* Elimination rules for valid_value, for each kind of stamp. *)
lemma valid_VoidStamp[elim]:
  shows "valid_value VoidStamp val \<Longrightarrow>
      val = UndefVal"
  using valid_value.simps by (metis IRTreeEval.val_to_bool.cases)

lemma valid_ObjStamp[elim]:
  shows "valid_value (ObjectStamp klass exact nonNull alwaysNull) val \<Longrightarrow>
      (\<exists>v. val = ObjRef v)"
  using valid_value.simps by (metis IRTreeEval.val_to_bool.cases)

lemma valid_int32[elim]:
  shows "valid_value (IntegerStamp 32 l h) val \<Longrightarrow>
      (\<exists>v. val = IntVal32 v)"
  apply (rule IRTreeEval.val_to_bool.cases[of val])
  using Value.distinct by simp+
                    
lemma valid_int64[elim]:
  shows "valid_value (IntegerStamp 64 l h) val \<Longrightarrow>
      (\<exists>v. val = IntVal64 v)"
  apply (rule IRTreeEval.val_to_bool.cases[of val])
  using Value.distinct by simp+

  
  
text \<open>TODO: could we prove that expression evaluation never returns $UndefVal$?
  But this might require restricting unary and binary operators to be total...
\<close>
(*
lemma evaltree_not_undef:
  fixes m p e v
  shows "([m,p] \<turnstile> e \<mapsto> v) \<Longrightarrow> v \<noteq> UndefVal"
  apply (induction rule: "evaltree.induct")
  using valid_not_undef apply auto
*)



lemma leafint32:
  assumes ev: "[m,p] \<turnstile> LeafExpr i (IntegerStamp 32 lo hi) \<mapsto> val"
  shows "\<exists>v. val = (IntVal32 v)"
(* Note: we could also add: ...\<and> lo \<le> sint v \<and> sint v \<le> hi *)
proof - 
  have "valid_value (IntegerStamp 32 lo hi) val"
    using ev by (rule LeafExprE; simp)
  then show ?thesis by auto
qed


lemma leafint64:
  assumes ev: "[m,p] \<turnstile> LeafExpr i (IntegerStamp 64 lo hi) \<mapsto> val"
  shows "\<exists>v. val = (IntVal64 v)"
(* Note: we could also add: ...\<and> lo \<le> sint v \<and> sint v \<le> hi *)
proof -
  have "valid_value (IntegerStamp 64 lo hi) val"
    using ev by (rule LeafExprE; simp)
  then show ?thesis by auto
qed

lemma default_stamp [simp]: "default_stamp = IntegerStamp 32 (-2147483648) 2147483647"
  using default_stamp_def by auto

lemma valid32 [simp]:
  assumes "valid_value (IntegerStamp 32 lo hi) val"
  shows "\<exists>v. (val = (IntVal32 v) \<and> lo \<le> sint v \<and> sint v \<le> hi)"
  using assms valid_int32 by force 

lemma valid64 [simp]:
  assumes "valid_value (IntegerStamp 64 lo hi) val"
  shows "\<exists>v. (val = (IntVal64 v) \<and> lo \<le> sint v \<and> sint v \<le> hi)"
  using assms valid_int64 by force

experiment begin
lemma int_stamp_implies_valid_value:
  "[m,p] \<turnstile> expr \<mapsto> val \<Longrightarrow>
   valid_value (stamp_expr expr) val"
proof (induction rule: evaltree.induct)
  case (ConstantExpr c)
  then show ?case sorry
next
  case (ParameterExpr s i)
  then show ?case sorry
next
  case (ConditionalExpr ce cond branch te fe v)
  then show ?case sorry
next
  case (UnaryExpr xe v op)
  then show ?case sorry
next
  case (BinaryExpr xe x ye y op)
  then show ?case sorry
next
  case (LeafExpr val nid s)
  then show ?case sorry
qed
end

lemma valid32or64:
  assumes "valid_value (IntegerStamp b lo hi) x"
  shows "(\<exists> v1. (x = IntVal32 v1)) \<or> (\<exists> v2. (x = IntVal64 v2))"
  using valid32 valid64 assms valid_value.elims(2) by blast

lemma valid32or64_both:
  assumes "valid_value (IntegerStamp b lox hix) x"
  and "valid_value (IntegerStamp b loy hiy) y"
  shows "(\<exists> v1 v2. x = IntVal32 v1 \<and> y = IntVal32 v2) \<or> (\<exists> v3 v4. x = IntVal64 v3 \<and> y = IntVal64 v4)"
  using assms valid32or64 valid32 valid_value.elims(2) valid_value.simps(1) by metis


subsection \<open>Example Data-flow Optimisations\<close>

(* An example refinement: a + 0 \<ge> a *)
lemma a0a_helper [simp]:
  assumes a: "valid_value (IntegerStamp 32 lo hi) v"
  shows "intval_add v (IntVal32 0) = v"
proof -
  obtain v32 :: int32 where "v = (IntVal32 v32)" using a valid32 by blast
  then show ?thesis by simp 
qed

lemma a0a: "(BinaryExpr BinAdd (LeafExpr 1 default_stamp) (ConstantExpr (IntVal32 0)))
              \<ge> (LeafExpr 1 default_stamp)"
  by (auto simp add: evaltree.LeafExpr)


(* Another example refinement: x + (y - x) \<ge> y *)
lemma xyx_y_helper [simp]:
  assumes "valid_value (IntegerStamp 32 lox hix) x"
  assumes "valid_value (IntegerStamp 32 loy hiy) y"
  shows "intval_add x (intval_sub y x) = y"
proof -
  obtain x32 :: int32 where x: "x = (IntVal32 x32)" using assms valid32 by blast
  obtain y32 :: int32 where y: "y = (IntVal32 y32)" using assms valid32 by blast
  show ?thesis using x y by simp
qed

lemma xyx_y: 
  "(BinaryExpr BinAdd
     (LeafExpr x (IntegerStamp 32 lox hix))
     (BinaryExpr BinSub
       (LeafExpr y (IntegerStamp 32 loy hiy))
       (LeafExpr x (IntegerStamp 32 lox hix))))
   \<ge> (LeafExpr y (IntegerStamp 32 loy hiy))"
  by (auto simp add: LeafExpr)



subsection \<open>Monotonicity of Expression Optimization\<close>

text \<open>We prove that each subexpression position is monotonic.
That is, optimizing a subexpression anywhere deep inside a top-level expression
also optimizes that top-level expression.  

Note that we might also be able to do
this via reusing Isabelle's 'mono' operator (HOL.Orderings theory), proving instantiations
like 'mono (UnaryExpr op)', but it is not obvious how to do this for both arguments
of the binary expressions.\<close>

lemma mono_unary: 
  assumes "e \<ge> e'"
  shows "(UnaryExpr op e) \<ge> (UnaryExpr op e')"
  using UnaryExpr assms by auto

lemma mono_binary: 
  assumes "x \<ge> x'"
  assumes "y \<ge> y'"
  shows "(BinaryExpr op x y) \<ge> (BinaryExpr op x' y')"
  using BinaryExpr assms by auto 

lemma mono_conditional: 
  assumes "ce \<ge> ce'"
  assumes "te \<ge> te'"
  assumes "fe \<ge> fe'"
  shows "(ConditionalExpr ce te fe) \<ge> (ConditionalExpr ce' te' fe')"
proof (simp only: le_expr_def; (rule allI)+; rule impI)
  fix m p v
  assume a: "[m,p] \<turnstile> ConditionalExpr ce te fe \<mapsto> v"
  then obtain cond where ce: "[m,p] \<turnstile> ce \<mapsto> cond" by auto
  then have ce': "[m,p] \<turnstile> ce' \<mapsto> cond" using assms by auto
  define branch  where b:  "branch  = (if val_to_bool cond then te else fe)"
  define branch' where b': "branch' = (if val_to_bool cond then te' else fe')"
  then have "[m,p] \<turnstile> branch \<mapsto> v" using a b ce evalDet by blast 
  then have "[m,p] \<turnstile> branch' \<mapsto> v" using assms b b' by auto
  then show "[m,p] \<turnstile> ConditionalExpr ce' te' fe' \<mapsto> v"
    using ConditionalExpr ce' b' by auto 
qed


(*
Step 3: if e1 isrefby e2 then g[e1] isREFby g[e2]
   Note: This needs to go after IRStepObj.thy.


lemma graph_refined:
  assumes "e1 \<ge> e2"
  assumes "g \<triangleleft> e1 \<leadsto> (g1, x1)"
  assumes "g \<triangleleft> e2 \<leadsto> (g2, x2)"
  shows "\<forall> m m' h h'. (g \<turnstile> (x1, m, h) \<rightarrow> (nid, m', h'))
                  \<longrightarrow> (g \<turnstile> (x2, m, h) \<rightarrow> (nid, m', h'))"
*)
end

