subsection \<open>Tree to Graph Theorems\<close>

theory TreeToGraphThms
imports
  IRTreeEvalThms
  IRGraphFrames
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"
begin

subsubsection \<open>Extraction and Evaluation of Expression Trees is Deterministic.\<close>

text \<open>First, we prove some extra rules that relate each
  type of IRNode to the corresponding IRExpr type that 'rep' will produce.
  These are very helpful for proving that 'rep' is deterministic.
\<close>

named_theorems rep

lemma rep_constant [rep]: 
  "g \<turnstile> n \<simeq> e \<Longrightarrow> 
   kind g n = ConstantNode c \<Longrightarrow> 
   e = ConstantExpr c"
  by (induction rule: rep.induct; auto)
  
lemma rep_parameter [rep]: 
  "g \<turnstile> n \<simeq> e \<Longrightarrow> 
   kind g n = ParameterNode i \<Longrightarrow>
   (\<exists>s. e = ParameterExpr i s)"
  by (induction rule: rep.induct; auto)

lemma rep_conditional [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = ConditionalNode c t f \<Longrightarrow>
   (\<exists> ce te fe. e = ConditionalExpr ce te fe)"
  by (induction rule: rep.induct; auto)

lemma rep_abs [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = AbsNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryAbs xe)"
  by (induction rule: rep.induct; auto)

lemma rep_not [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = NotNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryNot xe)"
  by (induction rule: rep.induct; auto)

lemma rep_negate [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = NegateNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryNeg xe)"
  by (induction rule: rep.induct; auto)

lemma rep_logicnegation [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = LogicNegationNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryLogicNegation xe)"
  by (induction rule: rep.induct; auto)

lemma rep_add [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = AddNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinAdd xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_sub [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = SubNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinSub xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_mul [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = MulNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinMul xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_and [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = AndNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinAnd xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_or [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = OrNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinOr xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_xor [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = XorNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinXor xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_left_shift [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = LeftShiftNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinLeftShift xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_right_shift [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = RightShiftNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinRightShift xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_unsigned_right_shift [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = UnsignedRightShiftNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinURightShift xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_below [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerBelowNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerBelow xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_equals [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerEqualsNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerEquals xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_less_than [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerLessThanNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerLessThan xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_narrow [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = NarrowNode ib rb x \<Longrightarrow>
   (\<exists>x. e = UnaryExpr (UnaryNarrow ib rb) x)"
  by (induction rule: rep.induct; auto)
 
lemma rep_sign_extend [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = SignExtendNode ib rb x \<Longrightarrow>
   (\<exists>x. e = UnaryExpr (UnarySignExtend ib rb) x)"
  by (induction rule: rep.induct; auto)

lemma rep_zero_extend [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = ZeroExtendNode ib rb x \<Longrightarrow>
   (\<exists>x. e = UnaryExpr (UnaryZeroExtend ib rb) x)"
  by (induction rule: rep.induct; auto)

lemma rep_load_field [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   is_preevaluated (kind g n) \<Longrightarrow>
   (\<exists>s. e = LeafExpr n s)"
  by (induction rule: rep.induct; auto)

lemma rep_ref [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = RefNode n' \<Longrightarrow>
   g \<turnstile> n' \<simeq> e"
  by (induction rule: rep.induct; auto)


method solve_det uses node =
  (match node in "kind _ _ = node _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ = node _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x. _ = node x \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>match IRNode.distinct in d: "node _ \<noteq> RefNode _" \<Rightarrow>
            \<open>metis i e r d\<close>\<close>\<close>\<close>\<close> |
   match node in "kind _ _ = node _ _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ _ = node _ _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x y. _ = node x y \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>match IRNode.distinct in d: "node _ _ \<noteq> RefNode _" \<Rightarrow>
            \<open>metis i e r d\<close>\<close>\<close>\<close>\<close> |
   match node in "kind _ _ = node _ _ _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ _ _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ _ _ = node _ _ _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x y z. _ = node x y z \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>match IRNode.distinct in d: "node _ _ _ \<noteq> RefNode _" \<Rightarrow>
            \<open>metis i e r d\<close>\<close>\<close>\<close>\<close> |
  match node in "kind _ _ = node _ _ _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ _ _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ _ _ = node _ _ _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x. _ = node _ _ x \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>match IRNode.distinct in d: "node _ _ _ \<noteq> RefNode _" \<Rightarrow>
            \<open>metis i e r d\<close>\<close>\<close>\<close>\<close>)

text \<open>Now we can prove that 'rep' and 'eval', and their list versions, are deterministic.
\<close>
lemma repDet:
  shows "(g \<turnstile> n \<simeq> e\<^sub>1) \<Longrightarrow> (g \<turnstile> n \<simeq> e\<^sub>2) \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
proof (induction arbitrary: e\<^sub>2 rule: "rep.induct")
  case (ConstantNode n c)
  then show ?case using rep_constant by auto
next
  case (ParameterNode n i s)
  then show ?case
    by (metis IRNode.disc(2685) ParameterNodeE is_RefNode_def rep_parameter)
next
  case (ConditionalNode n c t f ce te fe)
  then show ?case
    using IRNode.distinct(593)
    using IRNode.inject(6) ConditionalNodeE rep_conditional
    by metis
next
  case (AbsNode n x xe)
  then show ?case
    by (solve_det node: AbsNode)
next
  case (NotNode n x xe)
  then show ?case
    by (solve_det node: NotNode)
next
  case (NegateNode n x xe)
  then show ?case
    by (solve_det node: NegateNode)
next
  case (LogicNegationNode n x xe)
  then show ?case
    by (solve_det node: LogicNegationNode)
next
  case (AddNode n x y xe ye)
  then show ?case
    by (solve_det node: AddNode)
next
  case (MulNode n x y xe ye)
  then show ?case
    by (solve_det node: MulNode)
next
  case (SubNode n x y xe ye)
  then show ?case
    by (solve_det node: SubNode)
next
  case (AndNode n x y xe ye)
  then show ?case
    by (solve_det node: AndNode)
next
  case (OrNode n x y xe ye)
  then show ?case
    by (solve_det node: OrNode)
next
  case (XorNode n x y xe ye)
  then show ?case
    by (solve_det node: XorNode)
next
  case (LeftShiftNode n x y xe ye)
  then show ?case
    by (solve_det node: LeftShiftNode)
next
  case (RightShiftNode n x y xe ye)
  then show ?case
    by (solve_det node: RightShiftNode)
next
  case (UnsignedRightShiftNode n x y xe ye)
  then show ?case
    by (solve_det node: UnsignedRightShiftNode)
next
  case (IntegerBelowNode n x y xe ye)
  then show ?case
    by (solve_det node: IntegerBelowNode)
next
  case (IntegerEqualsNode n x y xe ye)
  then show ?case
    by (solve_det node: IntegerEqualsNode)
next
  case (IntegerLessThanNode n x y xe ye)
  then show ?case
    by (solve_det node: IntegerLessThanNode)
next
  case (NarrowNode n x xe)
  then show ?case
    by (metis IRNode.distinct(2203) IRNode.inject(28) NarrowNodeE rep_narrow)
next
  case (SignExtendNode n x xe)
  then show ?case 
    by (metis IRNode.distinct(2599) IRNode.inject(39) SignExtendNodeE rep_sign_extend)
next
  case (ZeroExtendNode n x xe)
  then show ?case
    by (metis IRNode.distinct(2753) IRNode.inject(50) ZeroExtendNodeE rep_zero_extend)
next
  case (LeafNode n s)
  then show ?case using rep_load_field LeafNodeE
    by (metis is_preevaluated.simps(53))
next
  case (RefNode n')
  then show ?case
    using rep_ref by blast
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

lemma encodeEvalDet:
  "[g,m,p] \<turnstile> e \<mapsto> v1 \<Longrightarrow> 
   [g,m,p] \<turnstile> e \<mapsto> v2 \<Longrightarrow>
   v1 = v2"
  by (metis encodeeval_def evalDet repDet)

lemma graphDet: "([g,m,p] \<turnstile> n \<mapsto> v\<^sub>1) \<and> ([g,m,p] \<turnstile> n \<mapsto> v\<^sub>2) \<Longrightarrow> v\<^sub>1 = v\<^sub>2"
  using encodeEvalDet by blast


subsubsection \<open>Monotonicity of Graph Refinement\<close>

text \<open>
Lift refinement monotonicity to graph level.
Hopefully these shouldn't really be required.
\<close>

lemma mono_abs:
  assumes "kind g1 n = AbsNode x \<and> kind g2 n = AbsNode x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis AbsNode assms(1) assms(2) assms(3) assms(4) mono_unary repDet)

lemma mono_not:
  assumes "kind g1 n = NotNode x \<and> kind g2 n = NotNode x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis NotNode assms(1) assms(2) assms(3) assms(4) mono_unary repDet)

lemma mono_negate:
  assumes "kind g1 n = NegateNode x \<and> kind g2 n = NegateNode x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis NegateNode assms(1) assms(2) assms(3) assms(4) mono_unary repDet)

lemma mono_logic_negation:
  assumes "kind g1 n = LogicNegationNode x \<and> kind g2 n = LogicNegationNode x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis LogicNegationNode assms(1) assms(2) assms(3) assms(4) mono_unary repDet)

lemma mono_narrow:
  assumes "kind g1 n = NarrowNode ib rb x \<and> kind g2 n = NarrowNode ib rb x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  using assms mono_unary repDet NarrowNode
  by metis

lemma mono_sign_extend:
  assumes "kind g1 n = SignExtendNode ib rb x \<and> kind g2 n = SignExtendNode ib rb x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis SignExtendNode assms(1) assms(2) assms(3) assms(4) mono_unary repDet)

lemma mono_zero_extend:
  assumes "kind g1 n = ZeroExtendNode ib rb x \<and> kind g2 n = ZeroExtendNode ib rb x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  using assms mono_unary repDet ZeroExtendNode
  by metis

lemma mono_conditional_graph:
  assumes "kind g1 n = ConditionalNode c t f \<and> kind g2 n = ConditionalNode c t f"
  assumes "(g1 \<turnstile> c \<simeq> ce1) \<and> (g2 \<turnstile> c \<simeq> ce2)"
  assumes "(g1 \<turnstile> t \<simeq> te1) \<and> (g2 \<turnstile> t \<simeq> te2)"
  assumes "(g1 \<turnstile> f \<simeq> fe1) \<and> (g2 \<turnstile> f \<simeq> fe2)"
  assumes "ce1 \<ge> ce2 \<and> te1 \<ge> te2 \<and> fe1 \<ge> fe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  using ConditionalNodeE IRNode.inject(6) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) mono_conditional repDet rep_conditional
  by (smt (verit, best) ConditionalNode)

lemma mono_add:
  assumes "kind g1 n = AddNode x y \<and> kind g2 n = AddNode x y"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "(g1 \<turnstile> y \<simeq> ye1) \<and> (g2 \<turnstile> y \<simeq> ye2)"
  assumes "xe1 \<ge> xe2 \<and> ye1 \<ge> ye2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  using mono_binary assms AddNodeE IRNode.inject(2) repDet rep_add
  by (metis IRNode.distinct(205))

lemma mono_mul:
  assumes "kind g1 n = MulNode x y \<and> kind g2 n = MulNode x y"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "(g1 \<turnstile> y \<simeq> ye1) \<and> (g2 \<turnstile> y \<simeq> ye2)"
  assumes "xe1 \<ge> xe2 \<and> ye1 \<ge> ye2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  using mono_binary assms IRNode.inject(27) MulNodeE repDet rep_mul
  by (smt (verit, best) MulNode)


lemma term_graph_evaluation:
  "(g \<turnstile> n \<unlhd> e) \<Longrightarrow> (\<forall> m p v . ([m,p] \<turnstile> e \<mapsto> v) \<longrightarrow> ([g,m,p] \<turnstile> n \<mapsto> v))"
  unfolding graph_represents_expression_def apply auto
  by (meson encodeeval_def)

lemma encodes_contains:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
  kind g n \<noteq> NoNode"
  apply (induction rule: rep.induct)
  apply (match IRNode.distinct in e: "?n \<noteq> NoNode" \<Rightarrow>
          \<open>presburger add: e\<close>)+
  apply force
  by fastforce

lemma no_encoding:
  assumes "n \<notin> ids g"
  shows "\<not>(g \<turnstile> n \<simeq> e)"
  using assms apply simp apply (rule notI) by (induction e; simp add: encodes_contains)

lemma not_excluded_keep_type:
  assumes "n \<in> ids g1"
  assumes "n \<notin> excluded"
  assumes "(excluded \<unlhd> as_set g1) \<subseteq> as_set g2"
  shows "kind g1 n = kind g2 n \<and> stamp g1 n = stamp g2 n"
  using assms unfolding as_set_def domain_subtraction_def by blast

method metis_node_eq_unary for node :: "'a \<Rightarrow> IRNode" =
  (match IRNode.inject in i: "(node _ = node _) = _" \<Rightarrow> 
      \<open>metis i\<close>)
method metis_node_eq_binary for node :: "'a \<Rightarrow> 'a \<Rightarrow> IRNode" =
  (match IRNode.inject in i: "(node _ _ = node _ _) = _" \<Rightarrow> 
      \<open>metis i\<close>)
method metis_node_eq_ternary for node :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> IRNode" =
  (match IRNode.inject in i: "(node _ _ _ = node _ _ _) = _" \<Rightarrow> 
      \<open>metis i\<close>)

subsubsection \<open>Lift Data-flow Tree Refinement to Graph Refinement\<close>


theorem graph_semantics_preservation:
  assumes a: "e1' \<ge> e2'"
  assumes b: "({n'} \<unlhd> as_set g1) \<subseteq> as_set g2"
  assumes c: "g1 \<turnstile> n' \<simeq> e1'"
  assumes d: "g2 \<turnstile> n' \<simeq> e2'"
  shows "graph_refinement g1 g2"
  unfolding graph_refinement_def apply rule
  apply (metis b d ids_some no_encoding not_excluded_keep_type singleton_iff subsetI)
  apply (rule allI) apply (rule impI) apply (rule allI) apply (rule impI)
  unfolding graph_represents_expression_def
proof -
  fix n e1
  assume e: "n \<in> ids g1"
  assume f: "(g1 \<turnstile> n \<simeq> e1)"

  show "\<exists> e2. (g2 \<turnstile> n \<simeq> e2) \<and> e1 \<ge> e2"
  proof (cases "n = n'")
    case True
    have g: "e1 = e1'" using c f True repDet by simp
    have h: "(g2 \<turnstile> n \<simeq> e2') \<and> e1' \<ge> e2'"
      using True a d by blast
    then show ?thesis 
      using g by blast
  next
    case False
    have "n \<notin> {n'}"
      using False by simp
    then have i: "kind g1 n = kind g2 n \<and> stamp g1 n = stamp g2 n"
      using not_excluded_keep_type
      using b e by presburger
    show ?thesis using f i
    proof (induction e1)
      case (ConstantNode n c)
      then show ?case
        by (metis eq_refl rep.ConstantNode)
    next
      case (ParameterNode n i s)
      then show ?case
        by (metis eq_refl rep.ParameterNode)
    next
      case (ConditionalNode n c t f ce1 te1 fe1)
      have k: "g1 \<turnstile> n \<simeq> ConditionalExpr ce1 te1 fe1" using f ConditionalNode
        by (simp add: ConditionalNode.hyps(2) rep.ConditionalNode)
      obtain cn tn fn where l: "kind g1 n = ConditionalNode cn tn fn"
        using ConditionalNode.hyps(1) by blast
      then have mc: "g1 \<turnstile> cn \<simeq> ce1"
        using ConditionalNode.hyps(1) ConditionalNode.hyps(2) by fastforce
      from l have mt: "g1 \<turnstile> tn \<simeq> te1"
        using ConditionalNode.hyps(1) ConditionalNode.hyps(3) by fastforce
      from l have mf: "g1 \<turnstile> fn \<simeq> fe1"
        using ConditionalNode.hyps(1) ConditionalNode.hyps(4) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> cn \<simeq> ce1" using mc by simp
        have "g1 \<turnstile> tn \<simeq> te1" using mt by simp
        have "g1 \<turnstile> fn \<simeq> fe1" using mf by simp
        have cer: "\<exists> ce2. (g2 \<turnstile> cn \<simeq> ce2) \<and> ce1 \<ge> ce2"
          using ConditionalNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_ternary ConditionalNode)
        have ter: "\<exists> te2. (g2 \<turnstile> tn \<simeq> te2) \<and> te1 \<ge> te2"
          using ConditionalNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_ternary ConditionalNode)
        have "\<exists> fe2. (g2 \<turnstile> fn \<simeq> fe2) \<and> fe1 \<ge> fe2"
          using ConditionalNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_ternary ConditionalNode)
        then have "\<exists> ce2 te2 fe2. (g2 \<turnstile> n \<simeq> ConditionalExpr ce2 te2 fe2) \<and> ConditionalExpr ce1 te1 fe1 \<ge> ConditionalExpr ce2 te2 fe2"
          using ConditionalNode.prems l rep.ConditionalNode cer ter
          by (smt (verit) mono_conditional)
        then show ?thesis
          by meson
      qed
    next
      case (AbsNode n x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr UnaryAbs xe1" using f AbsNode
        by (simp add: AbsNode.hyps(2) rep.AbsNode)
      obtain xn where l: "kind g1 n = AbsNode xn"
        using AbsNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using AbsNode.hyps(1) AbsNode.hyps(2) by fastforce
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr UnaryAbs e2'" using AbsNode.hyps(1) l m n
          using AbsNode.prems True d rep.AbsNode by simp
        then have r: "UnaryExpr UnaryAbs e1' \<ge> UnaryExpr UnaryAbs e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using AbsNode
          using False b encodes_contains l not_excluded_keep_type not_in_g singleton_iff
          by (metis_node_eq_unary AbsNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr UnaryAbs xe2) \<and> UnaryExpr UnaryAbs xe1 \<ge> UnaryExpr UnaryAbs xe2"
          by (metis AbsNode.prems l mono_unary rep.AbsNode)
        then show ?thesis
          by meson
      qed
    next
      case (NotNode n x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr UnaryNot xe1" using f NotNode
        by (simp add: NotNode.hyps(2) rep.NotNode)
      obtain xn where l: "kind g1 n = NotNode xn"
        using NotNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using NotNode.hyps(1) NotNode.hyps(2) by fastforce
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr UnaryNot e2'" using NotNode.hyps(1) l m n
          using NotNode.prems True d rep.NotNode by simp
        then have r: "UnaryExpr UnaryNot e1' \<ge> UnaryExpr UnaryNot e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using NotNode
          using False i b l not_excluded_keep_type singletonD no_encoding
          by (metis_node_eq_unary NotNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr UnaryNot xe2) \<and> UnaryExpr UnaryNot xe1 \<ge> UnaryExpr UnaryNot xe2"
          by (metis NotNode.prems l mono_unary rep.NotNode)
        then show ?thesis
          by meson
      qed
    next
      case (NegateNode n x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr UnaryNeg xe1" using f NegateNode
        by (simp add: NegateNode.hyps(2) rep.NegateNode)
      obtain xn where l: "kind g1 n = NegateNode xn"
        using NegateNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using NegateNode.hyps(1) NegateNode.hyps(2) by fastforce
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr UnaryNeg e2'" using NegateNode.hyps(1) l m n
          using NegateNode.prems True d rep.NegateNode by simp
        then have r: "UnaryExpr UnaryNeg e1' \<ge> UnaryExpr UnaryNeg e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using NegateNode
          using False i b l not_excluded_keep_type singletonD no_encoding
          by (metis_node_eq_unary NegateNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr UnaryNeg xe2) \<and> UnaryExpr UnaryNeg xe1 \<ge> UnaryExpr UnaryNeg xe2"
          by (metis NegateNode.prems l mono_unary rep.NegateNode)
        then show ?thesis
          by meson
      qed
    next
      case (LogicNegationNode n x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr UnaryLogicNegation xe1" using f LogicNegationNode
        by (simp add: LogicNegationNode.hyps(2) rep.LogicNegationNode)
      obtain xn where l: "kind g1 n = LogicNegationNode xn"
        using LogicNegationNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using LogicNegationNode.hyps(1) LogicNegationNode.hyps(2) by fastforce
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr UnaryLogicNegation e2'" using LogicNegationNode.hyps(1) l m n
          using LogicNegationNode.prems True d rep.LogicNegationNode by simp
        then have r: "UnaryExpr UnaryLogicNegation e1' \<ge> UnaryExpr UnaryLogicNegation e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using LogicNegationNode
          using False i b l not_excluded_keep_type singletonD no_encoding
          by (metis_node_eq_unary LogicNegationNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr UnaryLogicNegation xe2) \<and> UnaryExpr UnaryLogicNegation xe1 \<ge> UnaryExpr UnaryLogicNegation xe2"
          by (metis LogicNegationNode.prems l mono_unary rep.LogicNegationNode)
        then show ?thesis
          by meson
      qed
    next
      case (AddNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinAdd xe1 ye1" using f AddNode
        by (simp add: AddNode.hyps(2) rep.AddNode)
      obtain xn yn where l: "kind g1 n = AddNode xn yn"
        using AddNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using AddNode.hyps(1) AddNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using AddNode.hyps(1) AddNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using AddNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary AddNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using AddNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary AddNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinAdd xe2 ye2) \<and> BinaryExpr BinAdd xe1 ye1 \<ge> BinaryExpr BinAdd xe2 ye2"
          by (metis AddNode.prems l mono_binary rep.AddNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (MulNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinMul xe1 ye1" using f MulNode
        by (simp add: MulNode.hyps(2) rep.MulNode)
      obtain xn yn where l: "kind g1 n = MulNode xn yn"
        using MulNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using MulNode.hyps(1) MulNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using MulNode.hyps(1) MulNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using MulNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary MulNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using MulNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary MulNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinMul xe2 ye2) \<and> BinaryExpr BinMul xe1 ye1 \<ge> BinaryExpr BinMul xe2 ye2"
          by (metis MulNode.prems l mono_binary rep.MulNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (SubNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinSub xe1 ye1" using f SubNode
        by (simp add: SubNode.hyps(2) rep.SubNode)
      obtain xn yn where l: "kind g1 n = SubNode xn yn"
        using SubNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using SubNode.hyps(1) SubNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using SubNode.hyps(1) SubNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using SubNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary SubNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using SubNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary SubNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinSub xe2 ye2) \<and> BinaryExpr BinSub xe1 ye1 \<ge> BinaryExpr BinSub xe2 ye2"
          by (metis SubNode.prems l mono_binary rep.SubNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (AndNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinAnd xe1 ye1" using f AndNode
        by (simp add: AndNode.hyps(2) rep.AndNode)
      obtain xn yn where l: "kind g1 n = AndNode xn yn"
        using AndNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using AndNode.hyps(1) AndNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using AndNode.hyps(1) AndNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using AndNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary AndNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using AndNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary AndNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinAnd xe2 ye2) \<and> BinaryExpr BinAnd xe1 ye1 \<ge> BinaryExpr BinAnd xe2 ye2"
          by (metis AndNode.prems l mono_binary rep.AndNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (OrNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinOr xe1 ye1" using f OrNode
        by (simp add: OrNode.hyps(2) rep.OrNode)
      obtain xn yn where l: "kind g1 n = OrNode xn yn"
        using OrNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using OrNode.hyps(1) OrNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using OrNode.hyps(1) OrNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using OrNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary OrNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using OrNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary OrNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinOr xe2 ye2) \<and> BinaryExpr BinOr xe1 ye1 \<ge> BinaryExpr BinOr xe2 ye2"
          by (metis OrNode.prems l mono_binary rep.OrNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (XorNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinXor xe1 ye1" using f XorNode
        by (simp add: XorNode.hyps(2) rep.XorNode)
      obtain xn yn where l: "kind g1 n = XorNode xn yn"
        using XorNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using XorNode.hyps(1) XorNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using XorNode.hyps(1) XorNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using XorNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary XorNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using XorNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary XorNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinXor xe2 ye2) \<and> BinaryExpr BinXor xe1 ye1 \<ge> BinaryExpr BinXor xe2 ye2"
          by (metis XorNode.prems l mono_binary rep.XorNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (LeftShiftNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinLeftShift xe1 ye1" using f LeftShiftNode
        by (simp add: LeftShiftNode.hyps(2) rep.LeftShiftNode)
      obtain xn yn where l: "kind g1 n = LeftShiftNode xn yn"
        using LeftShiftNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using LeftShiftNode.hyps(1) LeftShiftNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using LeftShiftNode.hyps(1) LeftShiftNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using LeftShiftNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary LeftShiftNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using LeftShiftNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary LeftShiftNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinLeftShift xe2 ye2) \<and> BinaryExpr BinLeftShift xe1 ye1 \<ge> BinaryExpr BinLeftShift xe2 ye2"
          by (metis LeftShiftNode.prems l mono_binary rep.LeftShiftNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (RightShiftNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinRightShift xe1 ye1" using f RightShiftNode
        by (simp add: RightShiftNode.hyps(2) rep.RightShiftNode)
      obtain xn yn where l: "kind g1 n = RightShiftNode xn yn"
        using RightShiftNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using RightShiftNode.hyps(1) RightShiftNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using RightShiftNode.hyps(1) RightShiftNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using RightShiftNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary RightShiftNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using RightShiftNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary RightShiftNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinRightShift xe2 ye2) \<and> BinaryExpr BinRightShift xe1 ye1 \<ge> BinaryExpr BinRightShift xe2 ye2"
          by (metis RightShiftNode.prems l mono_binary rep.RightShiftNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (UnsignedRightShiftNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinURightShift xe1 ye1" using f UnsignedRightShiftNode
        by (simp add: UnsignedRightShiftNode.hyps(2) rep.UnsignedRightShiftNode)
      obtain xn yn where l: "kind g1 n = UnsignedRightShiftNode xn yn"
        using UnsignedRightShiftNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using UnsignedRightShiftNode.hyps(1) UnsignedRightShiftNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using UnsignedRightShiftNode.hyps(1) UnsignedRightShiftNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using UnsignedRightShiftNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary UnsignedRightShiftNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using UnsignedRightShiftNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary UnsignedRightShiftNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinURightShift xe2 ye2) \<and> BinaryExpr BinURightShift xe1 ye1 \<ge> BinaryExpr BinURightShift xe2 ye2"
          by (metis UnsignedRightShiftNode.prems l mono_binary rep.UnsignedRightShiftNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerBelowNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinIntegerBelow xe1 ye1" using f IntegerBelowNode
        by (simp add: IntegerBelowNode.hyps(2) rep.IntegerBelowNode)
      obtain xn yn where l: "kind g1 n = IntegerBelowNode xn yn"
        using IntegerBelowNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using IntegerBelowNode.hyps(1) IntegerBelowNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using IntegerBelowNode.hyps(1) IntegerBelowNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using IntegerBelowNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerBelowNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using IntegerBelowNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerBelowNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinIntegerBelow xe2 ye2) \<and> BinaryExpr BinIntegerBelow xe1 ye1 \<ge> BinaryExpr BinIntegerBelow xe2 ye2"
          by (metis IntegerBelowNode.prems l mono_binary rep.IntegerBelowNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerEqualsNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinIntegerEquals xe1 ye1" using f IntegerEqualsNode
        by (simp add: IntegerEqualsNode.hyps(2) rep.IntegerEqualsNode)
      obtain xn yn where l: "kind g1 n = IntegerEqualsNode xn yn"
        using IntegerEqualsNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using IntegerEqualsNode.hyps(1) IntegerEqualsNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using IntegerEqualsNode.hyps(1) IntegerEqualsNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using IntegerEqualsNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerEqualsNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using IntegerEqualsNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerEqualsNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinIntegerEquals xe2 ye2) \<and> BinaryExpr BinIntegerEquals xe1 ye1 \<ge> BinaryExpr BinIntegerEquals xe2 ye2"
          by (metis IntegerEqualsNode.prems l mono_binary rep.IntegerEqualsNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerLessThanNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinIntegerLessThan xe1 ye1" using f IntegerLessThanNode
        by (simp add: IntegerLessThanNode.hyps(2) rep.IntegerLessThanNode)
      obtain xn yn where l: "kind g1 n = IntegerLessThanNode xn yn"
        using IntegerLessThanNode.hyps(1) by blast
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using IntegerLessThanNode.hyps(1) IntegerLessThanNode.hyps(2) by fastforce
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using IntegerLessThanNode.hyps(1) IntegerLessThanNode.hyps(3) by fastforce
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" using mx by simp
        have "g1 \<turnstile> yn \<simeq> ye1" using my by simp
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using IntegerLessThanNode
          using a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerLessThanNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using IntegerLessThanNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerLessThanNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinIntegerLessThan xe2 ye2) \<and> BinaryExpr BinIntegerLessThan xe1 ye1 \<ge> BinaryExpr BinIntegerLessThan xe2 ye2"
          by (metis IntegerLessThanNode.prems l mono_binary rep.IntegerLessThanNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (NarrowNode n inputBits resultBits x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr (UnaryNarrow inputBits resultBits) xe1" using f NarrowNode
        by (simp add: NarrowNode.hyps(2) rep.NarrowNode)
      obtain xn where l: "kind g1 n = NarrowNode inputBits resultBits xn"
        using NarrowNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using NarrowNode.hyps(1) NarrowNode.hyps(2)
        by auto
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr (UnaryNarrow inputBits resultBits) e2'" using NarrowNode.hyps(1) l m n
          using NarrowNode.prems True d rep.NarrowNode by simp
        then have r: "UnaryExpr (UnaryNarrow inputBits resultBits) e1' \<ge> UnaryExpr (UnaryNarrow inputBits resultBits) e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using NarrowNode
          using False b encodes_contains l not_excluded_keep_type not_in_g singleton_iff
          by (metis_node_eq_ternary NarrowNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr (UnaryNarrow inputBits resultBits) xe2) \<and> UnaryExpr (UnaryNarrow inputBits resultBits) xe1 \<ge> UnaryExpr (UnaryNarrow inputBits resultBits) xe2"
          by (metis NarrowNode.prems l mono_unary rep.NarrowNode)
        then show ?thesis
          by meson
      qed
    next
      case (SignExtendNode n inputBits resultBits x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr (UnarySignExtend inputBits resultBits) xe1" using f SignExtendNode
        by (simp add: SignExtendNode.hyps(2) rep.SignExtendNode)
      obtain xn where l: "kind g1 n = SignExtendNode inputBits resultBits xn"
        using SignExtendNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using SignExtendNode.hyps(1) SignExtendNode.hyps(2)
        by auto
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr (UnarySignExtend inputBits resultBits) e2'" using SignExtendNode.hyps(1) l m n
          using SignExtendNode.prems True d rep.SignExtendNode by simp
        then have r: "UnaryExpr (UnarySignExtend inputBits resultBits) e1' \<ge> UnaryExpr (UnarySignExtend inputBits resultBits) e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using SignExtendNode
          using False b encodes_contains l not_excluded_keep_type not_in_g singleton_iff
          by (metis_node_eq_ternary SignExtendNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr (UnarySignExtend inputBits resultBits) xe2) \<and> UnaryExpr (UnarySignExtend inputBits resultBits) xe1 \<ge> UnaryExpr (UnarySignExtend inputBits resultBits) xe2"
          by (metis SignExtendNode.prems l mono_unary rep.SignExtendNode)
        then show ?thesis
          by meson
      qed
    next
      case (ZeroExtendNode n inputBits resultBits x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr (UnaryZeroExtend inputBits resultBits) xe1" using f ZeroExtendNode
        by (simp add: ZeroExtendNode.hyps(2) rep.ZeroExtendNode)
      obtain xn where l: "kind g1 n = ZeroExtendNode inputBits resultBits xn"
        using ZeroExtendNode.hyps(1) by blast
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using ZeroExtendNode.hyps(1) ZeroExtendNode.hyps(2)
        by auto
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" using c m repDet by simp
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr (UnaryZeroExtend inputBits resultBits) e2'" using ZeroExtendNode.hyps(1) l m n
          using ZeroExtendNode.prems True d rep.ZeroExtendNode by simp
        then have r: "UnaryExpr (UnaryZeroExtend inputBits resultBits) e1' \<ge> UnaryExpr (UnaryZeroExtend inputBits resultBits) e2'"
          by (meson a mono_unary)
        then show ?thesis using ev r
          by (metis n)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" using m by simp
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using ZeroExtendNode
          using False b encodes_contains l not_excluded_keep_type not_in_g singleton_iff
          by (metis_node_eq_ternary ZeroExtendNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr (UnaryZeroExtend inputBits resultBits) xe2) \<and> UnaryExpr (UnaryZeroExtend inputBits resultBits) xe1 \<ge> UnaryExpr (UnaryZeroExtend inputBits resultBits) xe2"
          by (metis ZeroExtendNode.prems l mono_unary rep.ZeroExtendNode)
        then show ?thesis
          by meson
      qed
    next
      case (LeafNode n s)
      then show ?case
        by (metis eq_refl rep.LeafNode)
    next
      case (RefNode n')
      then show ?case
        by (metis a b c d no_encoding not_excluded_keep_type rep.RefNode repDet singletonD)
    qed
  qed
qed

lemma graph_semantics_preservation_subscript:
  assumes a: "e\<^sub>1' \<ge> e\<^sub>2'"
  assumes b: "({n} \<unlhd> as_set g\<^sub>1) \<subseteq> as_set g\<^sub>2"
  assumes c: "g\<^sub>1 \<turnstile> n \<simeq> e\<^sub>1'"
  assumes d: "g\<^sub>2 \<turnstile> n \<simeq> e\<^sub>2'"
  shows "graph_refinement g\<^sub>1 g\<^sub>2"
  using graph_semantics_preservation assms by simp


lemma tree_to_graph_rewriting:
  "e\<^sub>1 \<ge> e\<^sub>2 
  \<and> (g\<^sub>1 \<turnstile> n \<simeq> e\<^sub>1) \<and> maximal_sharing g\<^sub>1
  \<and> ({n} \<unlhd> as_set g\<^sub>1) \<subseteq> as_set g\<^sub>2 
  \<and> (g\<^sub>2 \<turnstile> n \<simeq> e\<^sub>2) \<and> maximal_sharing g\<^sub>2
  \<Longrightarrow> graph_refinement g\<^sub>1 g\<^sub>2"
  using graph_semantics_preservation
  by auto

declare [[simp_trace]]
lemma equal_refines:
  fixes e1 e2 :: IRExpr
  assumes "e1 = e2"
  shows "e1 \<ge> e2"
  using assms
  by simp
declare [[simp_trace=false]]

inductive_cases UnaryRepE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr op xe)"
inductive_cases BinaryRepE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr op xe ye)"


lemma eval_contains_id[simp]: "g1 \<turnstile> n \<simeq> e \<Longrightarrow> n \<in> ids g1"
  using no_encoding by blast

lemma subset_kind[simp]: "as_set g1 \<subseteq> as_set g2 \<Longrightarrow> g1 \<turnstile> n \<simeq> e \<Longrightarrow> kind g1 n = kind g2 n"
  using eval_contains_id unfolding as_set_def
  by blast

lemma subset_stamp[simp]: "as_set g1 \<subseteq> as_set g2 \<Longrightarrow> g1 \<turnstile> n \<simeq> e \<Longrightarrow> stamp g1 n = stamp g2 n"
  using eval_contains_id unfolding as_set_def
  by blast

method solve_subset_eval uses as_set eval =
  (metis eval as_set subset_kind subset_stamp |
   metis eval as_set subset_kind)

(*
lemmas rep_rules =
  ConstantNode
  ParameterNode
  ConditionalNode

method solve_subset_eval uses as_set =
  (match premises in "kind _ _ = node _ \<Longrightarrow> _" for node \<Rightarrow>
    \<open>match rep_rules in eval: "kind _ _ = node _ \<Longrightarrow> _" \<Rightarrow> 
       \<open>metis eval as_set subset_kind\<close>\<close>)

method solve_subset_debug uses as_set =
  (match premises in k: "kind _ _ = node _ _" for node \<Rightarrow>
    \<open>match rep_rules in eval: "kind _ _ = node _ _ \<Longrightarrow> _" \<Rightarrow> 
       \<open>print_term node\<close>\<close>)
*)

lemma subset_implies_evals:
  assumes "as_set g1 \<subseteq> as_set g2"
  assumes "(g1 \<turnstile> n \<simeq> e)"
  shows "(g2 \<turnstile> n \<simeq> e)"
  using assms(2)
  apply (induction e)
                          apply (solve_subset_eval as_set: assms(1) eval: ConstantNode)
                         apply (solve_subset_eval as_set: assms(1) eval: ParameterNode)
                        apply (solve_subset_eval as_set: assms(1) eval: ConditionalNode)
                       apply (solve_subset_eval as_set: assms(1) eval: AbsNode)
                      apply (solve_subset_eval as_set: assms(1) eval: NotNode)
                     apply (solve_subset_eval as_set: assms(1) eval: NegateNode)
                    apply (solve_subset_eval as_set: assms(1) eval: LogicNegationNode)
                   apply (solve_subset_eval as_set: assms(1) eval: AddNode)
                  apply (solve_subset_eval as_set: assms(1) eval: MulNode)
                 apply (solve_subset_eval as_set: assms(1) eval: SubNode)
                apply (solve_subset_eval as_set: assms(1) eval: AndNode)
               apply (solve_subset_eval as_set: assms(1) eval: OrNode)
             apply (solve_subset_eval as_set: assms(1) eval: XorNode)
            apply (solve_subset_eval as_set: assms(1) eval: LeftShiftNode)
           apply (solve_subset_eval as_set: assms(1) eval: RightShiftNode)
          apply (solve_subset_eval as_set: assms(1) eval: UnsignedRightShiftNode)
         apply (solve_subset_eval as_set: assms(1) eval: IntegerBelowNode)
        apply (solve_subset_eval as_set: assms(1) eval: IntegerEqualsNode)
       apply (solve_subset_eval as_set: assms(1) eval: IntegerLessThanNode)
      apply (solve_subset_eval as_set: assms(1) eval: NarrowNode)
     apply (solve_subset_eval as_set: assms(1) eval: SignExtendNode)
    apply (solve_subset_eval as_set: assms(1) eval: ZeroExtendNode)
   apply (solve_subset_eval as_set: assms(1) eval: LeafNode)
  by (solve_subset_eval as_set: assms(1) eval: RefNode)

lemma subset_refines:
  assumes "as_set g1 \<subseteq> as_set g2"
  shows "graph_refinement g1 g2"
proof -
  have "ids g1 \<subseteq> ids g2" using assms unfolding as_set_def
    by blast
  then show ?thesis unfolding graph_refinement_def apply rule
    apply (rule allI) apply (rule impI) apply (rule allI) apply (rule impI)
    unfolding graph_represents_expression_def
    proof -
      fix n e1
      assume 1:"n \<in> ids g1"
      assume 2:"g1 \<turnstile> n \<simeq> e1"
  
      show "\<exists>e2. (g2 \<turnstile> n \<simeq> e2) \<and> e1 \<ge> e2"
        using assms 1 2 using subset_implies_evals
        by (meson equal_refines)
    qed
  qed

lemma graph_construction:
  "e\<^sub>1 \<ge> e\<^sub>2
  \<and> as_set g\<^sub>1 \<subseteq> as_set g\<^sub>2
  \<and> (g\<^sub>2 \<turnstile> n \<simeq> e\<^sub>2)
  \<Longrightarrow> (g\<^sub>2 \<turnstile> n \<unlhd> e\<^sub>1) \<and> graph_refinement g\<^sub>1 g\<^sub>2"
  using subset_refines
  by (meson encodeeval_def graph_represents_expression_def le_expr_def)


subsubsection \<open>Term Graph Reconstruction\<close>

lemma find_exists_kind:
  assumes "find_node_and_stamp g (node, s) = Some nid"
  shows "kind g nid = node"
  using assms unfolding find_node_and_stamp.simps
  by (metis (mono_tags, lifting) find_Some_iff)

lemma find_exists_stamp:
  assumes "find_node_and_stamp g (node, s) = Some nid"
  shows "stamp g nid = s"
  using assms unfolding find_node_and_stamp.simps
  by (metis (mono_tags, lifting) find_Some_iff)

lemma find_new_kind:
  assumes "g' = add_node nid (node, s) g"
  assumes "node \<noteq> NoNode"
  shows "kind g' nid = node"
  using assms
  using add_node_lookup by presburger

lemma find_new_stamp:
  assumes "g' = add_node nid (node, s) g"
  assumes "node \<noteq> NoNode"
  shows "stamp g' nid = s"
  using assms
  using add_node_lookup by presburger

lemma sorted_bottom:
  assumes "finite xs"
  assumes "x \<in> xs"
  shows "x \<le> last(sorted_list_of_set(xs::nat set))"
  using assms
  using sorted2_simps(2) sorted_list_of_set(2)
  by (smt (verit, del_insts) Diff_iff Max_ge Max_in empty_iff list.set(1) snoc_eq_iff_butlast sorted_insort_is_snoc sorted_list_of_set(1) sorted_list_of_set.fold_insort_key.infinite sorted_list_of_set.fold_insort_key.remove)

lemma fresh: "finite xs \<Longrightarrow> last(sorted_list_of_set(xs::nat set)) + 1 \<notin> xs"
  using sorted_bottom
  using not_le by auto

lemma fresh_ids:
  assumes "n = get_fresh_id g"
  shows "n \<notin> ids g"
proof -
  have "finite (ids g)" using Rep_IRGraph by auto
  then show ?thesis
    using assms fresh unfolding get_fresh_id.simps
    by blast
qed

lemma graph_unchanged_rep_unchanged:
  assumes "\<forall>n \<in> ids g. kind g n = kind g' n"
  assumes "\<forall>n \<in> ids g. stamp g n = stamp g' n"
  shows "(g \<turnstile> n \<simeq> e) \<longrightarrow> (g' \<turnstile> n \<simeq> e)"
  apply (rule impI) subgoal premises e using e assms
    apply (induction n e)
                          apply (metis no_encoding rep.ConstantNode)
                         apply (metis no_encoding rep.ParameterNode)
                        apply (metis no_encoding rep.ConditionalNode)
                       apply (metis no_encoding rep.AbsNode)
                      apply (metis no_encoding rep.NotNode)
                     apply (metis no_encoding rep.NegateNode)
                    apply (metis no_encoding rep.LogicNegationNode)
                   apply (metis no_encoding rep.AddNode)
                  apply (metis no_encoding rep.MulNode)
                 apply (metis no_encoding rep.SubNode)
                apply (metis no_encoding rep.AndNode)
               apply (metis no_encoding rep.OrNode)
               apply (metis no_encoding rep.XorNode)
              apply (metis no_encoding rep.LeftShiftNode)
             apply (metis no_encoding rep.RightShiftNode)
            apply (metis no_encoding rep.UnsignedRightShiftNode)
           apply (metis no_encoding rep.IntegerBelowNode)
          apply (metis no_encoding rep.IntegerEqualsNode)
         apply (metis no_encoding rep.IntegerLessThanNode)
        apply (metis no_encoding rep.NarrowNode)
       apply (metis no_encoding rep.SignExtendNode)
      apply (metis no_encoding rep.ZeroExtendNode)
     apply (metis no_encoding rep.LeafNode)
    by (metis no_encoding rep.RefNode)
  done

lemma fresh_node_subset:
  assumes "n \<notin> ids g"
  assumes "g' = add_node n (k, s) g"
  shows "as_set g \<subseteq> as_set g'"
  using assms
  by (smt (verit, del_insts) Collect_mono_iff Diff_idemp Diff_insert_absorb add_changed as_set_def disjoint_change unchanged.simps)

lemma unrep_subset:
  assumes "(g \<oplus> e \<leadsto> (g', n))"
  shows "as_set g \<subseteq> as_set g'"
  using assms proof (induction g e "(g', n)" arbitrary: g' n)
  case (ConstantNodeSame g c n)
  then show ?case by blast
next
  case (ConstantNodeNew g c n g')
  then show ?case using fresh_ids fresh_node_subset
    by presburger
next
  case (ParameterNodeSame g i s n)
  then show ?case by blast
next
  case (ParameterNodeNew g i s n g')
  then show ?case using fresh_ids fresh_node_subset
    by presburger
next
  case (ConditionalNodeSame g ce g2 c te g3 t fe g4 f s' n)
  then show ?case by blast
next
  case (ConditionalNodeNew g ce g2 c te g3 t fe g4 f s' n g')
  then show ?case using fresh_ids fresh_node_subset
    by (meson subset_trans)
next
  case (UnaryNodeSame g xe g2 x s' op n)
  then show ?case by blast
next
  case (UnaryNodeNew g xe g2 x s' op n g')
  then show ?case using fresh_ids fresh_node_subset
    by (meson subset_trans)
next
  case (BinaryNodeSame g xe g2 x ye g3 y s' op n)
  then show ?case by blast
next
  case (BinaryNodeNew g xe g2 x ye g3 y s' op n g')
  then show ?case using fresh_ids fresh_node_subset
    by (meson subset_trans)
next
  case (AllLeafNodes g n s)
  then show ?case by blast
qed

lemma fresh_node_preserves_other_nodes:
  assumes "n' = get_fresh_id g"
  assumes "g' = add_node n' (k, s) g"
  shows "\<forall> n \<in> ids g . (g \<turnstile> n \<simeq> e) \<longrightarrow> (g' \<turnstile> n \<simeq> e)"
  using assms
  by (smt (verit, ccfv_SIG) Diff_idemp Diff_insert_absorb add_changed disjoint_change fresh_ids graph_unchanged_rep_unchanged unchanged.elims(2))

lemma found_node_preserves_other_nodes:
  assumes "find_node_and_stamp g (k, s) = Some n"
  shows "\<forall> n \<in> ids g. (g \<turnstile> n \<simeq> e) \<longleftrightarrow> (g \<turnstile> n \<simeq> e)"
  using assms
  by blast

lemma unrep_ids_subset[simp]:
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "ids g \<subseteq> ids g'"
  using assms unrep_subset
  by (meson graph_refinement_def subset_refines)

lemma unrep_unchanged:
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "\<forall> n \<in> ids g . \<forall> e. (g \<turnstile> n \<simeq> e) \<longrightarrow> (g' \<turnstile> n \<simeq> e)"
  using assms unrep_subset fresh_node_preserves_other_nodes
  by (meson subset_implies_evals)

theorem term_graph_reconstruction:
  "g \<oplus> e \<leadsto> (g', n) \<Longrightarrow> (g' \<turnstile> n \<simeq> e) \<and> as_set g \<subseteq> as_set g'"
  subgoal premises e apply (rule conjI) defer
    using e unrep_subset apply blast using e
  proof (induction g e "(g', n)" arbitrary: g' n)
    case (ConstantNodeSame g' c n)
    then have "kind g' n = ConstantNode c"
      using find_exists_kind local.ConstantNodeSame by blast
    then show ?case using ConstantNode by blast
  next
    case (ConstantNodeNew g c)
    then show ?case
      using ConstantNode IRNode.distinct(683) add_node_lookup by presburger
  next
    case (ParameterNodeSame i s)
    then show ?case
      by (metis ParameterNode find_exists_kind find_exists_stamp)
  next
    case (ParameterNodeNew g i s)
    then show ?case
      by (metis IRNode.distinct(2447) ParameterNode add_node_lookup)
  next
    case (ConditionalNodeSame g ce g2 c te g3 t fe g4 f s' n)
    then have k: "kind g4 n = ConditionalNode c t f"
      using find_exists_kind by blast
    have c: "g4 \<turnstile> c \<simeq> ce" using local.ConditionalNodeSame unrep_unchanged
      using no_encoding by blast
    have t: "g4 \<turnstile> t \<simeq> te" using local.ConditionalNodeSame unrep_unchanged
      using no_encoding by blast
    have f: "g4 \<turnstile> f \<simeq> fe" using local.ConditionalNodeSame unrep_unchanged
      using no_encoding by blast
    then show ?case using c t f
      using ConditionalNode k by blast
  next
    case (ConditionalNodeNew g ce g2 c te g3 t fe g4 f s' n g')
    moreover have "ConditionalNode c t f \<noteq> NoNode"
      using unary_node.elims by blast
    ultimately have k: "kind g' n = ConditionalNode c t f"
      using find_new_kind local.ConditionalNodeNew
      by presburger
    then have c: "g' \<turnstile> c \<simeq> ce" using local.ConditionalNodeNew unrep_unchanged
      using no_encoding
      by (metis ConditionalNodeNew.hyps(9) fresh_node_preserves_other_nodes)
    then have t: "g' \<turnstile> t \<simeq> te" using local.ConditionalNodeNew unrep_unchanged
      using no_encoding fresh_node_preserves_other_nodes
      by metis
    then have f: "g' \<turnstile> f \<simeq> fe" using local.ConditionalNodeNew unrep_unchanged
      using no_encoding fresh_node_preserves_other_nodes
      by metis
    then show ?case using c t f
      using ConditionalNode k by blast
  next
    case (UnaryNodeSame g xe g' x s' op n)
    then have k: "kind g' n = unary_node op x"
      using find_exists_kind local.UnaryNodeSame by blast
    then have "g' \<turnstile> x \<simeq> xe" using local.UnaryNodeSame by blast
    then show ?case using k
      apply (cases op)
      using AbsNode unary_node.simps(1) apply presburger
      using NegateNode unary_node.simps(3) apply presburger
      using NotNode unary_node.simps(2) apply presburger
      using LogicNegationNode unary_node.simps(4) apply presburger
      using NarrowNode unary_node.simps(5) apply presburger
      using SignExtendNode unary_node.simps(6) apply presburger
      using ZeroExtendNode unary_node.simps(7) by presburger
  next
    case (UnaryNodeNew g xe g2 x s' op n g')
    moreover have "unary_node op x \<noteq> NoNode"
      using unary_node.elims by blast
    ultimately have k: "kind g' n = unary_node op x"
      using find_new_kind local.UnaryNodeNew
      by presburger
    have "x \<in> ids g2" using local.UnaryNodeNew
      using eval_contains_id by blast
    then have "x \<noteq> n" using local.UnaryNodeNew(5) fresh_ids by blast
    have "g' \<turnstile> x \<simeq> xe" using local.UnaryNodeNew fresh_node_preserves_other_nodes
      using \<open>x \<in> ids g2\<close> by blast
    then show ?case using k
      apply (cases op)
      using AbsNode unary_node.simps(1) apply presburger
      using NegateNode unary_node.simps(3) apply presburger
      using NotNode unary_node.simps(2) apply presburger
      using LogicNegationNode unary_node.simps(4) apply presburger
      using NarrowNode unary_node.simps(5) apply presburger
      using SignExtendNode unary_node.simps(6) apply presburger
      using ZeroExtendNode unary_node.simps(7) by presburger
  next
    case (BinaryNodeSame g xe g2 x ye g3 y s' op n)
    then have k: "kind g3 n = bin_node op x y"
      using find_exists_kind by blast
    have x: "g3 \<turnstile> x \<simeq> xe" using local.BinaryNodeSame unrep_unchanged
      using no_encoding by blast
    have y: "g3 \<turnstile> y \<simeq> ye" using local.BinaryNodeSame unrep_unchanged
      using no_encoding by blast
    then show ?case using x y k apply (cases op)
      using AddNode bin_node.simps(1) apply presburger
      using MulNode bin_node.simps(2) apply presburger
      using SubNode bin_node.simps(3) apply presburger
      using AndNode bin_node.simps(4) apply presburger
      using OrNode bin_node.simps(5) apply presburger
      using XorNode bin_node.simps(6) apply presburger
      using LeftShiftNode bin_node.simps(7) apply presburger
      using RightShiftNode bin_node.simps(8) apply presburger
      using UnsignedRightShiftNode bin_node.simps(9) apply presburger
      using IntegerEqualsNode bin_node.simps(10) apply presburger
      using IntegerLessThanNode bin_node.simps(11) apply presburger
      using IntegerBelowNode bin_node.simps(12) by presburger
  next
    case (BinaryNodeNew g xe g2 x ye g3 y s' op n g')
    moreover have "bin_node op x y \<noteq> NoNode"
      using bin_node.elims by blast
    ultimately have k: "kind g' n = bin_node op x y"
      using find_new_kind local.BinaryNodeNew
      by presburger
    then have k: "kind g' n = bin_node op x y"
      using find_exists_kind by blast
    have x: "g' \<turnstile> x \<simeq> xe" using local.BinaryNodeNew unrep_unchanged
      using no_encoding
      by (meson fresh_node_preserves_other_nodes)
    have y: "g' \<turnstile> y \<simeq> ye" using local.BinaryNodeNew unrep_unchanged
      using no_encoding
      by (meson fresh_node_preserves_other_nodes)
    then show ?case using x y k apply (cases op)
      using AddNode bin_node.simps(1) apply presburger
      using MulNode bin_node.simps(2) apply presburger
      using SubNode bin_node.simps(3) apply presburger
      using AndNode bin_node.simps(4) apply presburger
      using OrNode bin_node.simps(5) apply presburger
      using XorNode bin_node.simps(6) apply presburger
      using LeftShiftNode bin_node.simps(7) apply presburger
      using RightShiftNode bin_node.simps(8) apply presburger
      using UnsignedRightShiftNode bin_node.simps(9) apply presburger
      using IntegerEqualsNode bin_node.simps(10) apply presburger
      using IntegerLessThanNode bin_node.simps(11) apply presburger
      using IntegerBelowNode bin_node.simps(12) by presburger
  next
    case (AllLeafNodes g n s)
    then show ?case using rep.LeafNode by blast
  qed
  done

lemma ref_refinement:
  assumes "g \<turnstile> n \<simeq> e\<^sub>1"
  assumes "kind g n' = RefNode n"
  shows "g \<turnstile> n' \<unlhd> e\<^sub>1"
  using assms RefNode
  by (meson equal_refines graph_represents_expression_def)

lemma unrep_refines:
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "graph_refinement g g'"
  using assms
  using graph_refinement_def subset_refines unrep_subset by blast

lemma add_new_node_refines:
  assumes "n \<notin> ids g"
  assumes "g' = add_node n (k, s) g"
  shows "graph_refinement g g'"
  using assms unfolding graph_refinement
  using fresh_node_subset subset_refines by presburger

lemma add_node_as_set:
  assumes "g' = add_node n (k, s) g"
  shows "({n} \<unlhd> as_set g) \<subseteq> as_set g'"
  using assms unfolding as_set_def domain_subtraction_def 
  using add_changed
  by (smt (z3) case_prodE changeonly.simps mem_Collect_eq prod.sel(1) subsetI)


theorem refined_insert:
  assumes "e\<^sub>1 \<ge> e\<^sub>2"
  assumes "g\<^sub>1 \<oplus> e\<^sub>2 \<leadsto> (g\<^sub>2, n')"
  shows "(g\<^sub>2 \<turnstile> n' \<unlhd> e\<^sub>1) \<and> graph_refinement g\<^sub>1 g\<^sub>2"
  using assms
  using graph_construction term_graph_reconstruction by blast

lemma ids_finite: "finite (ids g)"
  using Rep_IRGraph ids.rep_eq by simp

lemma unwrap_sorted: "set (sorted_list_of_set (ids g)) = ids g"
  using Rep_IRGraph set_sorted_list_of_set ids_finite
  by blast

lemma find_none:
  assumes "find_node_and_stamp g (k, s) = None"
  shows "\<forall> n \<in> ids g. kind g n \<noteq> k \<or> stamp g n \<noteq> s"
proof -
  have "(\<nexists>n. n \<in> ids g \<and> (kind g n = k \<and> stamp g n = s))"
    using assms unfolding find_node_and_stamp.simps using find_None_iff unwrap_sorted
    by (metis (mono_tags, lifting))
  then show ?thesis
    by blast
qed


(*

section \<open>An attempt at a constructive refinement proof\<close>
lemma add_node_ids_subset:
  assumes "n \<in> ids g"
  assumes "g' = add_node n node g"
  shows "ids g' = ids g \<union> {n}"
  using assms unfolding add_node_def
  apply (cases "fst node = NoNode") 
  using ids.rep_eq replace_node.rep_eq replace_node_def apply auto[1]
  unfolding ids_def
  by (smt (verit, best) Collect_cong Un_insert_right dom_fun_upd fst_conv fun_upd_apply ids.rep_eq ids_def insert_absorb mem_Collect_eq option.inject option.simps(3) replace_node.rep_eq replace_node_def sup_bot.right_neutral)
  
theorem constructive_refinement:
  assumes 1: "e\<^sub>1 \<ge> e\<^sub>2"
  assumes "g\<^sub>1 \<turnstile> n \<simeq> e\<^sub>1"
  assumes "g\<^sub>1 \<oplus> e\<^sub>2 \<leadsto> (g\<^sub>2, n')"
  assumes "n \<noteq> n'"
  assumes "g\<^sub>3 = add_node n (RefNode n', stamp g\<^sub>2 n') g\<^sub>2"
  shows "graph_refinement g\<^sub>1 g\<^sub>3"
proof -
  have step1: "graph_refinement g\<^sub>1 g\<^sub>2"
    using assms(2,3)
    by (simp add: subset_refines unrep_subset)
  have "n \<in> ids g\<^sub>2"
    using assms(2) assms(3) no_encoding unrep_unchanged by blast
  then have "ids g\<^sub>2 = ids g\<^sub>3"
    using assms(5) add_node_ids_subset
    by blast
  have 3: "g\<^sub>2 \<turnstile> n \<simeq> e\<^sub>1"
    using assms(3)
    using assms(2) subset_implies_evals unrep_subset by blast
  then have g2rep1: "g\<^sub>2 \<turnstile> n \<unlhd> e\<^sub>1"
    using 1 unfolding graph_represents_expression_def
    by blast
  have g2rep: "g\<^sub>2 \<turnstile> n' \<unlhd> e\<^sub>1"
    using assms(3) term_graph_reconstruction
    using "1" graph_construction by blast
  have 2: "({n} \<unlhd> as_set g\<^sub>2) \<subseteq> as_set g\<^sub>3"
    using assms(5) add_node_as_set by blast
  have "kind g\<^sub>3 n = RefNode n'"
    using assms(5) find_new_kind by blast
  have g3rep: "(g\<^sub>3 \<turnstile> n' \<unlhd> e\<^sub>1)"
    using g2rep1 g2rep assms(4) 2 
    (*by (meson \<open>kind g\<^sub>3 n = RefNode n'\<close> assms(5) graph_represents_expression_def rep_ref)*)
  have refkind: "kind g\<^sub>3 n = RefNode n'"
    using assms(5) add_node_lookup
    by (metis IRNode.distinct(2755))
  then have 4: "g\<^sub>3 \<turnstile> n \<unlhd> e\<^sub>1"
    using assms
    using RefNode g3rep
    by (meson graph_represents_expression_def)
  have step2: "graph_refinement g\<^sub>2 g\<^sub>3"
    using graph_semantics_preservation 1 2 3 4
    by (meson graph_represents_expression_def order_trans)
  from step1 step2 show ?thesis
    by (meson assms(3) graph_refinement_def order_trans subsetD subset_implies_evals unrep_subset)
qed
*)





(*
lemma
  assumes "maximal_sharing g\<^sub>1"
  assumes "e\<^sub>1 \<ge> e\<^sub>2"
  assumes "g\<^sub>1 \<oplus> e\<^sub>2 \<leadsto> (g\<^sub>2, n')"
  shows "maximal_sharing g\<^sub>2"
  using assms(3,1)
  apply (induction g\<^sub>1 e\<^sub>2 "(g\<^sub>2, n')" arbitrary: g\<^sub>2 n') 
  apply blast using find_none sorry
*)


(*
lemma
  assumes "maximal_sharing g"
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "\<forall>n' . n' \<in> ids g' - ids g \<longrightarrow> 
         (\<forall>e . (g' \<turnstile> n' \<simeq> e) \<longrightarrow> 
          \<not>(\<exists>n'' . n'' \<in> true_ids g' \<and> n'' = n' \<and> (g' \<turnstile> n'' \<simeq> e)))"
  using assms(2)
  apply (induction g e "(g', n)" arbitrary: g' n) 
  apply blast sorry

lemma
  "maximal_sharing g \<Longrightarrow> g \<oplus> e \<leadsto> (g', n) \<Longrightarrow> maximal_sharing g'"
  sorry

lemma only_n_changes:
  assumes "({n} \<unlhd> as_set g) \<subseteq> as_set g'"
  shows "\<forall>n'. n' \<in> ids g - {n} \<longrightarrow> (\<forall>e. (g \<turnstile> n' \<simeq> e) \<longrightarrow> (g' \<turnstile> n' \<simeq> e))"
  apply (rule allI) apply (rule impI)
  subgoal premises set for n' apply (rule allI) apply (rule impI)
    subgoal premises eval for e
      using eval set assms proof (induction n' e )
      case (ConstantNode n c)
      then show ?case
        by (metis Diff_iff not_excluded_keep_type rep.ConstantNode)
    next
      case (ParameterNode n i s)
      then show ?case
        by (metis DiffD1 DiffD2 not_excluded_keep_type rep.ParameterNode)
    next
      case (ConditionalNode n c t f ce te fe)
      then show ?case sorry
    next
      case (AbsNode n x xe)
      then show ?case sorry
    next
      case (NotNode n x xe)
      then show ?case sorry
    next
      case (NegateNode n x xe)
      then show ?case sorry
    next
      case (LogicNegationNode n x xe)
      then show ?case sorry
    next
      case (AddNode n x y xe ye)
      then show ?case sorry
    next
      case (MulNode n x y xe ye)
      then show ?case sorry
    next
      case (SubNode n x y xe ye)
      then show ?case sorry
    next
      case (AndNode n x y xe ye)
      then show ?case sorry
    next
      case (OrNode n x y xe ye)
      then show ?case sorry
    next
      case (XorNode n x y xe ye)
      then show ?case sorry
    next
      case (LeftShiftNode n x y xe ye)
      then show ?case sorry
    next
      case (RightShiftNode n x y xe ye)
      then show ?case sorry
    next
      case (UnsignedRightShiftNode n x y xe ye)
      then show ?case sorry
    next
      case (IntegerBelowNode n x y xe ye)
      then show ?case sorry
    next
      case (IntegerEqualsNode n x y xe ye)
      then show ?case sorry
    next
      case (IntegerLessThanNode n x y xe ye)
      then show ?case sorry
    next
      case (NarrowNode n inputBits resultBits x xe)
      then show ?case sorry
    next
      case (SignExtendNode n inputBits resultBits x xe)
      then show ?case sorry
    next
      case (ZeroExtendNode n inputBits resultBits x xe)
      then show ?case sorry
    next
      case (LeafNode n s)
      then show ?case sorry
    next
      case (RefNode n n' e)
      then show ?case sorry
    qed
     
      apply (metis ConstantNode DiffE not_excluded_keep_type)
      apply (metis DiffD1 DiffD2 ParameterNode not_excluded_keep_type) sorry
  proof -
    have "kind g n' = kind g' n'"
      using assms set
      by (meson Diff_iff not_excluded_keep_type)
    moreover have "stamp g n' = stamp g' n'"
      using assms set
      by (meson DiffE not_excluded_keep_type)
    ultimately show "\<forall>e. (g \<turnstile> n' \<simeq> e) \<longrightarrow> (g' \<turnstile> n' \<simeq> e)"
      using assms sorry
  qed
  done*)

method ref_represents uses node =
  (metis IRNode.distinct(2755) RefNode dual_order.refl find_new_kind fresh_node_subset node subset_implies_evals)

(*
lemma
  assumes "kind g n = RefNode n'"
  assumes "g \<turnstile> n \<simeq> e"
  assumes "n \<noteq> n'"
  shows "n \<notin> eval_usages g n'"
  using assms(2,1,3) apply (induction e arbitrary: n; auto) sorry


lemma unaffected_rep:
  assumes "({n} \<unlhd> as_set g) \<subseteq> as_set g'"
  assumes "g \<turnstile> n' \<simeq> e"
  assumes "n \<notin> eval_usages g n'"
  shows "g' \<turnstile> n' \<simeq> e"
  using assms(2)
proof -
  have ne: "n \<noteq> n'"
    using assms(3)
    using assms(2) eval_contains_id eval_usages_self by blast
  show ?thesis 
    using assms(2) assms ne apply (induction e) using ne 
                        apply (metis ConstantNode encodes_contains not_excluded_keep_type not_in_g singleton_iff)
                      apply (metis ParameterNode empty_iff encode_in_ids insertE not_excluded_keep_type)
    sorry
qed

lemma ref_add_represents:
  assumes "g \<turnstile> n \<unlhd> e"
  assumes "g \<turnstile> n' \<unlhd> e"
  assumes "g' = add_node n' (RefNode n, s) g"
  assumes "n' \<notin> eval_usages g n"
  shows "g' \<turnstile> n' \<unlhd> e" using assms
  by (metis IRNode.distinct(2755) RefNode add_node_as_set find_new_kind graph_represents_expression_def unaffected_rep)
(*proof -
  have as_set: "({n'} \<unlhd> as_set g) \<subseteq> as_set g'"
    using assms(3)
    by (simp add: add_node_as_set)
  have "kind g' n' = RefNode n"
    using assms(3)
    using find_new_kind by blast
  show ?thesis unfolding graph_represents_expression_def 
  proof -
    obtain e' where e'def: "(g \<turnstile> n \<simeq> e') \<and> e \<ge> e'"
      using assms(1) graph_represents_expression_def by blast
    then obtain e2' where "g' \<turnstile> n \<simeq> e2'"
      using as_set using unaffected_rep
      using assms(4) by blast
    obtain e'' where e''def: "(g \<turnstile> n' \<simeq> e'') \<and> e \<ge> e''"
      using assms(2) graph_represents_expression_def by blast
    have "g' \<turnstile> n' \<simeq> e''"
      using as_set e''def sorry
    show "\<exists>e'. (g' \<turnstile> n' \<simeq> e') \<and> e \<ge> e'"
   sorry
   sorry
                      (*apply (ref_represents node: rep.ConstantNode)
                      apply (ref_represents node: rep.ParameterNode)
                      apply (ref_represents node: rep.ConditionalNode)
                      apply (ref_represents node: rep.AbsNode)
                     apply (ref_represents node: rep.NotNode)
                    apply (ref_represents node: rep.NegateNode)
                   apply (ref_represents node: rep.LogicNegationNode)
                  apply (ref_represents node: rep.AddNode)
                 apply (ref_represents node: rep.MulNode)
                apply (ref_represents node: rep.SubNode)
               apply (ref_represents node: rep.AndNode)
              apply (ref_represents node: rep.OrNode)
             apply (ref_represents node: rep.XorNode)
            apply (ref_represents node: rep.LeftShiftNode)
           apply (ref_represents node: rep.RightShiftNode)
          apply (ref_represents node: rep.UnsignedRightShiftNode)
         apply (ref_represents node: rep.IntegerBelowNode)
        apply (ref_represents node: rep.IntegerEqualsNode)
       apply (ref_represents node: rep.IntegerLessThanNode)
      apply (ref_represents node: rep.NarrowNode)
     apply (ref_represents node: rep.SignExtendNode)
    apply (ref_represents node: rep.ZeroExtendNode)
   apply (ref_represents node: rep.LeafNode)
  by (ref_represents node: rep.RefNode)*)
*)

theorem constructive_refinement:
  assumes 1: "e\<^sub>1 \<ge> e\<^sub>2"
  assumes "g\<^sub>1 \<turnstile> n \<simeq> e\<^sub>1"
  assumes "g\<^sub>1 \<triangleleft> e\<^sub>2 \<leadsto> (g\<^sub>2, n')"
  assumes "n \<noteq> n'"
  assumes "g\<^sub>3 = add_node n (RefNode n', stamp g\<^sub>2 n') g\<^sub>2"
  shows "graph_refinement g\<^sub>1 g\<^sub>3"
proof -
  have step1: "graph_refinement g\<^sub>1 g\<^sub>2"
    using assms(2,3)
    by (simp add: subset_refines unrep_subset)
  have "ids g\<^sub>2 \<subseteq> ids g\<^sub>3"
    using assms(5)
    by (metis (no_types, lifting) IRNode.distinct(2755) add_node_def assms(2) assms(3) find_new_kind ids_some insertE insert_Diff no_encoding replace_node_def replace_node_unchanged subsetI unrep_unchanged)
  have 3: "g\<^sub>2 \<turnstile> n \<simeq> e\<^sub>1"
    using assms(3)
    using assms(2) subset_implies_evals unrep_subset by blast
  then have g2rep1: "g\<^sub>2 \<turnstile> n \<unlhd> e\<^sub>1"
    using 1 unfolding graph_represents_expression_def
    by blast
  have g2rep: "g\<^sub>2 \<turnstile> n' \<unlhd> e\<^sub>1"
    using assms(3) term_graph_reconstruction
    using "1" graph_construction by blast
  have 2: "({n} \<unlhd> as_set g\<^sub>2) \<subseteq> as_set g\<^sub>3"
    using assms(5) add_node_as_set by blast
  have "kind g\<^sub>3 n = RefNode n'"
    using assms(5) find_new_kind by blast
  have g3rep: "(g\<^sub>3 \<turnstile> n' \<unlhd> e\<^sub>1)"
    using g2rep1 g2rep assms(4) 2 ref_add_represents g2rep1 sorry
    (*by (meson \<open>kind g\<^sub>3 n = RefNode n'\<close> assms(5) graph_represents_expression_def rep_ref)*)
  have refkind: "kind g\<^sub>3 n = RefNode n'"
    using assms(5) add_node_lookup
    by (metis IRNode.distinct(2755))
  then have 4: "g\<^sub>3 \<turnstile> n \<unlhd> e\<^sub>1"
    using assms
    using RefNode g3rep
    by (meson graph_represents_expression_def)
  have step2: "graph_refinement g\<^sub>2 g\<^sub>3"
    using graph_semantics_preservation 1 2 3 4
    by (meson graph_represents_expression_def order_trans)
  from step1 step2 show ?thesis
    by (meson assms(3) graph_refinement_def order_trans subsetD subset_implies_evals unrep_subset)
qed
*)



subsubsection \<open>Data-flow Tree to Subgraph Preserves Maximal Sharing\<close>

lemma same_kind_stamp_encodes_equal:
  assumes "kind g n = kind g n'"
  assumes "stamp g n = stamp g n'"
  assumes "\<not>(is_preevaluated (kind g n))"
  shows "\<forall> e. (g \<turnstile> n \<simeq> e) \<longrightarrow> (g \<turnstile> n' \<simeq> e)"
  apply (rule allI)
  subgoal for e
    apply (rule impI)
    subgoal premises eval using eval assms
      apply (induction e)
    using ConstantNode apply presburger
    using ParameterNode apply presburger 
                        apply (metis ConditionalNode)
                        apply (metis AbsNode)
                       apply (metis NotNode)
                      apply (metis NegateNode)
                     apply (metis LogicNegationNode)
                    apply (metis AddNode)
                   apply (metis MulNode)
                  apply (metis SubNode)
                 apply (metis AndNode)
                apply (metis OrNode)
               apply (metis XorNode)
              apply (metis LeftShiftNode)
             apply (metis RightShiftNode)
            apply (metis UnsignedRightShiftNode)
           apply (metis IntegerBelowNode)
          apply (metis IntegerEqualsNode)
         apply (metis IntegerLessThanNode)
        apply (metis NarrowNode)
       apply (metis SignExtendNode)
      apply (metis ZeroExtendNode)
    defer
     apply (metis RefNode)
    by blast
    done
  done

lemma new_node_not_present:
  assumes "find_node_and_stamp g (node, s) = None"
  assumes "n = get_fresh_id g"
  assumes "g' = add_node n (node, s) g"
  shows "\<forall> n' \<in> true_ids g. (\<forall>e. ((g \<turnstile> n \<simeq> e) \<and> (g \<turnstile> n' \<simeq> e)) \<longrightarrow> n = n')"
  using assms
  using encode_in_ids fresh_ids by blast

lemma true_ids_def:
  "true_ids g = {n \<in> ids g. \<not>(is_RefNode (kind g n)) \<and> ((kind g n) \<noteq> NoNode)}"
  unfolding true_ids_def ids_def
  using ids_def is_RefNode_def by fastforce


lemma add_node_some_node_def:
  assumes "k \<noteq> NoNode"
  assumes "g' = add_node nid (k, s) g"
  shows "g' = Abs_IRGraph ((Rep_IRGraph g)(nid \<mapsto> (k, s)))"
  using assms
  by (metis Rep_IRGraph_inverse add_node.rep_eq fst_conv)

(*
lemma dropdown:
  assumes "update = (\<lambda>k nid g. (if fst k = NoNode then g else g(nid \<mapsto> k)))"
  assumes "g' = update (k, s) (nid::ID) g"
  assumes "k \<noteq> NoNode"
  shows "{nid \<in> dom g' . \<nexists>s. g' nid = (Some (NoNode, s))} = ({nid \<in> dom g . \<nexists>s. g nid = (Some (NoNode, s))} \<union> {nid})"
proof -
  have "g' = g(nid \<mapsto> (k, s))"
    using assms
    by simp
  then have "\<forall> s. g' nid \<noteq> (Some (NoNode, s))"
    by (simp add: assms(3))
  have "dom g' = dom g \<union> {nid}"
    by (simp add: \<open>g' = g(nid \<mapsto> (k, s))\<close>)
  have "{nid \<in> dom g . \<forall>s. g nid \<noteq> (Some (NoNode, s))} \<subseteq> {nid \<in> dom g' . \<forall>s. g' nid \<noteq> (Some (NoNode, s))}"
    using \<open>\<forall>s. g' nid \<noteq> Some (NoNode, s)\<close> \<open>g' = g(nid \<mapsto> (k, s))\<close> by auto
  then show ?thesis using assms(3) sorry
qed
*)

lemma ids_add_update_v1:
  assumes "g' = add_node nid (k, s) g"
  assumes "k \<noteq> NoNode"
  shows "dom (Rep_IRGraph g') = dom (Rep_IRGraph g) \<union> {nid}"
  using assms ids.rep_eq add_node_some_node_def
  by (simp add: add_node.rep_eq)

lemma ids_add_update_v2:
  assumes "g' = add_node nid (k, s) g"
  assumes "k \<noteq> NoNode"
  shows "nid \<in> ids g'"
  using assms
  using find_new_kind ids_some by presburger

lemma add_node_ids_subset:
  assumes "n \<in> ids g"
  assumes "g' = add_node n node g"
  shows "ids g' = ids g \<union> {n}"
  using assms unfolding add_node_def
  apply (cases "fst node = NoNode") 
  using ids.rep_eq replace_node.rep_eq replace_node_def apply auto[1]
  unfolding ids_def
  by (smt (verit, best) Collect_cong Un_insert_right dom_fun_upd fst_conv fun_upd_apply ids.rep_eq ids_def insert_absorb mem_Collect_eq option.inject option.simps(3) replace_node.rep_eq replace_node_def sup_bot.right_neutral)

(*
lemma ids_add_update:
  assumes "g' = add_node nid (k, s) g"
  assumes "k \<noteq> NoNode"
  shows "ids g' = ids g \<union> {nid}"
  using assms apply transfer subgoal premises e for g' nid k s g
    proof -
      have "g' = g(nid \<mapsto> (k, s))"
        using e(3,4) by simp
      then have dom_eq: "dom g' = dom g \<union> {nid}"
        by force
      have "\<not>(\<exists>s . g' nid = Some (NoNode, s))"
        by (simp add: \<open>g' = g(nid \<mapsto> (k, s))\<close> e(4))
      then show ?thesis using dom_eq sorry
    qed
    done

lemma true_ids_add_update:
  assumes "n \<notin> ids g"
  assumes "g' = add_node n (node, s) g"
  assumes "\<not>(is_RefNode node)"
  assumes "node \<noteq> NoNode"
  shows "true_ids g' = true_ids g \<union> {n}"
proof -
  have "kind g' n = node" using assms
    using add_node_lookup by presburger
  then have "ids g' = ids g \<union> {n}"
    using assms(2,4) ids_add_update
    by presburger
  then show ?thesis using assms(3) true_ids_def
    by (smt (verit, ccfv_SIG) Collect_cong Diff_insert_absorb IRGraph.true_ids_def Un_insert_right \<open>kind g' n = node\<close> add_node_def assms(1) assms(2) insert_Diff_if insert_iff is_RefNode_def mem_Collect_eq replace_node_def replace_node_unchanged sup_bot.right_neutral)
qed
*)

(*
lemma maintain_maximal_sharing:
  assumes "maximal_sharing g"
  assumes "as_set g \<subseteq> as_set g'"
  assumes "new_nodes = true_ids g' - true_ids g"
  assumes "\<forall> n1 n2. n1 \<in> new_nodes \<and> n2 \<in> new_nodes
           \<longrightarrow> (\<forall>e. ((g' \<turnstile> n1 \<simeq> e) \<and> (g' \<turnstile> n2 \<simeq> e)) \<longrightarrow> n1 = n2)"
  shows "maximal_sharing g'"
  unfolding maximal_sharing
  apply (rule allI)+ apply (rule impI) apply (rule conjE)
  using assms unfolding maximal_sharing
proof -
  fix n1 n2
  assume n1in: "n1 \<in> true_ids g'"
  assume n2in: "n2 \<in> true_ids g'"
  from n1in n2in have "\<forall>e. (g \<turnstile> n1 \<simeq> e) \<and> (g \<turnstile> n2 \<simeq> e) \<longrightarrow> n1 = n2"
    using assms sorry
    by (metis (no_types, lifting) true_ids_def assms(1) assms(2) maximal_sharing mem_Collect_eq no_encoding subset_kind)
  then show  "\<forall>e. (g' \<turnstile> n1 \<simeq> e) \<and> (g' \<turnstile> n2 \<simeq> e) \<longrightarrow> n1 = n2"
    proof (cases "n1 \<in> new_nodes")
      case True
      then show ?thesis using assms(3) n2in sorry
    next
      case False
      then show ?thesis using assms(2) sorry
    qed
  qed
*)

lemma convert_maximal:
  assumes "\<forall>n n'. n \<in> true_ids g \<and> n' \<in> true_ids g \<longrightarrow> (\<forall>e e'. (g \<turnstile> n \<simeq> e) \<and> (g \<turnstile> n' \<simeq> e') \<longrightarrow> e \<noteq> e')"
  shows "maximal_sharing g"
  using assms
  using maximal_sharing by blast

lemma fresh_node_unique:
  assumes "find_node_and_stamp g (k, s) = None"
  assumes "n = get_fresh_id g"
  assumes "g' = add_node n (k, s) g"
  assumes "g' \<turnstile> n \<simeq> e"
  shows "\<forall>n' . n' \<in> true_ids g \<longrightarrow> (\<forall>e'. (g \<turnstile> n' \<simeq> e') \<and> (stamp g n' \<noteq> s) \<longrightarrow> e \<noteq> e')"
  using assms unfolding find_node_and_stamp.simps
proof -
  have "n \<notin> ids g"
    using assms(2) fresh_ids by presburger
  have unique: "\<not>(\<exists>n' \<in> ids g . kind g n' = k \<and> stamp g n' = s)"
    using assms(1) find_none by blast
  show ?thesis 
    apply (rule allI; rule impI) 
    subgoal premises in_trueids for n'
    apply (rule allI; rule impI)
    subgoal premises eval for e'
      using eval (*apply (induction rule: rep.induct)*) sorry
    done
  done
qed

(*
  apply (rule allI) apply (rule impI) apply (rule allI)
  subgoal premises true for n' e' apply (rule impI)
    subgoal premises eval
      apply (subgoal_tac "n \<noteq> n'")
      defer using assms
      apply (metis eval fresh_ids no_encoding)
      using eval apply auto sledgehammer
    done
  done
*)


(*
lemma add_node_new:
  assumes "n \<notin> ids g"
  assumes "g' = add_node n (k, s) g"
  assumes "\<not>(is_RefNode k)"
  assumes "k \<noteq> NoNode"
  shows "true_ids g' - true_ids g = {n}"
  using assms true_ids_add_update
  by (simp add: IRGraph.true_ids_def insert_Diff_if)
*)

(*
lemma new_nodes_maximal_sharing:
  assumes "g \<oplus> e \<leadsto> (g', n)"
  assumes "new = true_ids g' - true_ids g"
  shows "\<forall>n'' \<in> new. \<forall>n' \<in> true_ids g. (\<forall>e. (g' \<turnstile> n1 \<simeq> e) \<and> (g' \<turnstile> n2 \<simeq> e) \<and> (stamp g n = stamp g n') \<longrightarrow> n1 = n2)"
  using assms(1,2) proof (induction g e "(g', n)" arbitrary: g' n)
  case (ConstantNodeSame g c n)
  then show ?case
    by blast
next
  case (ConstantNodeNew g c n g')
  then have "new = {n}" using add_node_new
    using IRNode.disc(2657) IRNode.distinct(683) fresh_ids by presburger
  then show ?case using fresh_node_unique convert_maximal sledgehammer
next
  case (ParameterNodeSame g i s n)
  then show ?case sorry
next
  case (ParameterNodeNew g i s n g')
  then show ?case sorry
next
  case (ConditionalNodeSame g ce g2 c te g3 t fe g4 f s' n)
  then show ?case sorry
next
  case (ConditionalNodeNew g ce g2 c te g3 t fe g4 f s' n g')
  then show ?case sorry
next
  case (UnaryNodeSame g xe g2 x s' op n)
  then show ?case sorry
next
  case (UnaryNodeNew g xe g2 x s' op n g')
  then show ?case sorry
next
  case (BinaryNodeSame g xe g2 x ye g3 y s' op n)
  then show ?case sorry
next
  case (BinaryNodeNew g xe g2 x ye g3 y s' op n g')
  then show ?case sorry
next
  case (AllLeafNodes g n s)
  then show ?case sorry
qed
*)

(*
lemma fresh_maintain_maximal_sharing:
  assumes "maximal_sharing g"
  assumes "find_node_and_stamp g (k, s) = None"
  assumes "n = get_fresh_id g"
  assumes "g' = add_node n (k, s) g"
  shows "maximal_sharing g'"
  using assms 
  by (smt (z3) Collect_cong DiffD1 DiffD2 Rep_IRGraph_inverse TreeToGraphThms.true_ids_def Un_commute add_changed add_node.rep_eq add_node_new disjoint_change find_new_kind fresh_ids fresh_node_subset fst_conv ids_add_update insert_Diff insert_Diff1 insert_iff insert_is_Un maintain_maximal_sharing node_unchanged)

lemma maintain_maximal_sharing:
  assumes "maximal_sharing g"
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "maximal_sharing g'"
  unfolding maximal_sharing apply (rule allI)+
  subgoal for n1 n2
    apply (cases "n1 \<in> true_ids g \<and> n2 \<in> true_ids g")
    using assms unfolding maximal_sharing using unrep_unchanged sorry
  using new_nodes_maximal_sharing assms
  done*)

lemma fresh_sharing:
  assumes "g' \<turnstile> n \<simeq> e"
  assumes "find_node_and_stamp g (k, s) = None"
  assumes "n = get_fresh_id g"
  assumes "g' = add_node n (k, s) g"
  shows "\<not>(\<exists>n' \<in> ids g'. (g' \<turnstile> n' \<simeq> e) \<and> n \<noteq> n' \<and> stamp g' n \<noteq> stamp g' n')"
  using assms proof (induction n e)
  case (ConstantNode n c)
  then show ?case sorry
next
  case (ParameterNode n i s)
  then show ?case sorry
next
  case (ConditionalNode n c t f ce te fe)
  then show ?case sorry
next
  case (AbsNode n x xe)
  then show ?case sorry
next
  case (NotNode n x xe)
  then show ?case sorry
next
  case (NegateNode n x xe)
  then show ?case sorry
next
  case (LogicNegationNode n x xe)
  then show ?case sorry
next
  case (AddNode n x y xe ye)
  then show ?case sorry
next
  case (MulNode n x y xe ye)
  then show ?case sorry
next
  case (SubNode n x y xe ye)
  then show ?case sorry
next
  case (AndNode n x y xe ye)
  then show ?case sorry
next
  case (OrNode n x y xe ye)
  then show ?case sorry
next
  case (XorNode n x y xe ye)
  then show ?case sorry
next
  case (LeftShiftNode n x y xe ye)
  then show ?case sorry
next
  case (RightShiftNode n x y xe ye)
  then show ?case sorry
next
  case (UnsignedRightShiftNode n x y xe ye)
  then show ?case sorry
next
  case (IntegerBelowNode n x y xe ye)
  then show ?case sorry
next
  case (IntegerEqualsNode n x y xe ye)
  then show ?case sorry
next
  case (IntegerLessThanNode n x y xe ye)
  then show ?case sorry
next
  case (NarrowNode n inputBits resultBits x xe)
  then show ?case sorry
next
  case (SignExtendNode n inputBits resultBits x xe)
  then show ?case sorry
next
  case (ZeroExtendNode n inputBits resultBits x xe)
  then show ?case sorry
next
  case (LeafNode n s)
  then show ?case sorry
next
  case (RefNode n n' e)
  then show ?case sorry
qed


(*lemma
  assumes "\<not>(\<exists>n' \<in> ids g. (g \<turnstile> n' \<simeq> ConstantExpr c) \<and> n \<noteq> n' \<and> stamp g n \<noteq> stamp g n')"
  assumes "maximal_sharing g"*)

lemma add_node_set_eq:
  assumes "k \<noteq> NoNode"
  assumes "n \<notin> ids g"
  shows "as_set (add_node n (k, s) g) = as_set g \<union> {(n, (k, s))}"
  using assms unfolding as_set_def add_node_def apply transfer apply simp
  by blast 

lemma add_node_as_set_eq:
  assumes "g' = add_node n (k, s) g"
  assumes "n \<notin> ids g"
  shows "({n} \<unlhd> as_set g') = as_set g"
  using assms unfolding domain_subtraction_def
  using add_node_set_eq 
  by (smt (z3) Collect_cong Rep_IRGraph_inverse UnCI UnE add_node.rep_eq as_set_def case_prodE2 case_prodI2 le_boolE le_boolI' mem_Collect_eq prod.sel(1) singletonD singletonI)

lemma true_ids_add_update:
  assumes "node \<noteq> NoNode"
  assumes "n \<notin> ids g"
  assumes "g' = add_node n (k, s) g"
  assumes "\<not>(is_RefNode k)"
  shows "true_ids g' = true_ids g \<union> {n}"
  using assms unfolding as_set_def add_node_def true_ids_def apply simp apply transfer sorry

lemma new_def:
  assumes "(new \<unlhd> as_set g') = as_set g"
  shows "n \<in> ids g \<longrightarrow> n \<notin> new"
  using assms
  by (smt (z3) as_set_def case_prodD domain_subtraction_def mem_Collect_eq)

lemma add_preserves_rep:
  assumes unchanged: "(new \<unlhd> as_set g') = as_set g"
  assumes closed: "wf_closed g"
  assumes existed: "n \<in> ids g"
  assumes "g' \<turnstile> n \<simeq> e"
  shows "g \<turnstile> n \<simeq> e"
proof (cases "n \<in> new")
  case True
  have "n \<notin> ids g"
    using unchanged True unfolding as_set_def domain_subtraction_def
    by blast
  then show ?thesis using existed by simp
next
  case False
  then have kind_eq: "\<forall> n' . n' \<notin> new \<longrightarrow> kind g n' = kind g' n'"
    \<comment>\<open>can be more general than stamp_eq because NoNode default is equal\<close>
    using unchanged not_excluded_keep_type
    by (smt (z3) case_prodE domain_subtraction_def ids_some mem_Collect_eq subsetI)
  from False have stamp_eq: "\<forall> n' \<in> ids g' . n' \<notin> new \<longrightarrow> stamp g n' = stamp g' n'"
    using unchanged not_excluded_keep_type
    by (metis equalityE)
  show ?thesis using assms(4) kind_eq stamp_eq False
  proof (induction n e rule: rep.induct)
    case (ConstantNode n c)
    then show ?case
      using rep.ConstantNode kind_eq by presburger
  next
    case (ParameterNode n i s)
    then show ?case
      using rep.ParameterNode
      by (metis no_encoding)
  next
    case (ConditionalNode n c t f ce te fe)
    have kind: "kind g n = ConditionalNode c t f"
      using ConditionalNode.hyps(1) ConditionalNode.prems(3) kind_eq by presburger
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{c, t, f} = inputs g n"
      using kind unfolding inputs.simps using inputs_of_ConditionalNode by simp
    have "c \<in> ids g \<and> t \<in> ids g \<and> f \<in> ids g"
      using closed unfolding wf_closed_def
      using isin inputs by blast
    then have "c \<notin> new \<and> t \<notin> new \<and> f \<notin> new"
      using new_def unchanged by blast
    then show ?case using ConditionalNode apply simp
      using rep.ConditionalNode by presburger
  next
    case (AbsNode n x xe)
    then have kind: "kind g n = AbsNode x"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x} = inputs g n"
      using kind unfolding inputs.simps by simp
    have "x \<in> ids g"
      using closed unfolding wf_closed_def
      using isin inputs by blast
    then have "x \<notin> new"
      using new_def unchanged by blast
    then show ?case
      using AbsNode
      using rep.AbsNode by presburger
  next
    case (NotNode n x xe)
    then have kind: "kind g n = NotNode x"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x} = inputs g n"
      using kind unfolding inputs.simps by simp
    have "x \<in> ids g"
      using closed unfolding wf_closed_def
      using isin inputs by blast
    then have "x \<notin> new"
      using new_def unchanged by blast
    then show ?case using NotNode
      using rep.NotNode by presburger
  next
    case (NegateNode n x xe)
    then show ?case sorry
  next
    case (LogicNegationNode n x xe)
    then show ?case sorry
  next
    case (AddNode n x y xe ye)
    then show ?case sorry
  next
    case (MulNode n x y xe ye)
    then show ?case sorry
  next
    case (SubNode n x y xe ye)
    then show ?case sorry
  next
    case (AndNode n x y xe ye)
    then show ?case sorry
  next
    case (OrNode n x y xe ye)
    then show ?case sorry
  next
    case (XorNode n x y xe ye)
    then show ?case sorry
  next
    case (LeftShiftNode n x y xe ye)
    then show ?case sorry
  next
    case (RightShiftNode n x y xe ye)
    then show ?case sorry
  next
    case (UnsignedRightShiftNode n x y xe ye)
    then show ?case sorry
  next
    case (IntegerBelowNode n x y xe ye)
    then show ?case sorry
  next
    case (IntegerEqualsNode n x y xe ye)
    then show ?case sorry
  next
    case (IntegerLessThanNode n x y xe ye)
    then show ?case sorry
  next
    case (NarrowNode n inputBits resultBits x xe)
    then show ?case sorry
  next
    case (SignExtendNode n inputBits resultBits x xe)
    then show ?case sorry
  next
    case (ZeroExtendNode n inputBits resultBits x xe)
    then show ?case sorry
  next
    case (LeafNode n s)
    then show ?case sorry
  next
    case (RefNode n n' e)
    then show ?case sorry
  qed 
qed

theorem unrep_maximal_sharing:
  assumes "maximal_sharing g"
  assumes "wf_closed g"
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "maximal_sharing g'"
  using assms(3,2,1)
  proof (induction g e "(g', n)" arbitrary: g' n)
    case (ConstantNodeSame g c n)
    then show ?case by blast
  next
    case (ConstantNodeNew g c n g')
    then have "kind g' n = ConstantNode c"
      using find_new_kind by blast
    then have repn: "g' \<turnstile> n \<simeq> ConstantExpr c"
      using rep.ConstantNode by simp
    from ConstantNodeNew have "\<not>(is_RefNode (ConstantNode c)) \<and> ConstantNode c \<noteq> NoNode"
      by simp
    then have dom: "true_ids g' = true_ids g \<union> {n}"
      using ConstantNodeNew.hyps(2) ConstantNodeNew.hyps(3) fresh_ids
      by (meson true_ids_add_update)
    have new: "n \<notin> ids g"
      using fresh_ids
      using ConstantNodeNew.hyps(2) by blast
    obtain new where "new = true_ids g' - true_ids g"
      by simp
    then have new_def: "new = {n}"
      by (metis (no_types, lifting) DiffE Diff_cancel IRGraph.true_ids_def Un_insert_right dom insert_Diff_if new sup_bot_right)
    then have unchanged: "(new \<unlhd> as_set g') = as_set g"
      using ConstantNodeNew(3) new add_node_as_set_eq
      by presburger
    then have kind_eq: "\<forall>n' . n' \<notin> new \<longrightarrow> kind g n' = kind g' n'"
      by (metis ConstantNodeNew.hyps(3) \<open>new = {n}\<close> add_node_as_set dual_order.eq_iff not_excluded_keep_type not_in_g)
    from unchanged have stamp_eq: "\<forall>n' \<in> ids g . n' \<notin> new \<longrightarrow> stamp g n' = stamp g' n'"
      using not_excluded_keep_type new_def new
      by (metis ConstantNodeNew.hyps(3) add_node_as_set)
    show ?case unfolding maximal_sharing apply (rule allI; rule allI; rule impI)
      using ConstantNodeNew(5) unfolding maximal_sharing apply auto
      (*using preserves dom*) proof -
      fix n\<^sub>1 n\<^sub>2 e
      assume 1: "\<forall>n\<^sub>1 n\<^sub>2.
          n\<^sub>1 \<in> true_ids g \<and> n\<^sub>2 \<in> true_ids g \<longrightarrow>
          (\<exists>e. (g \<turnstile> n\<^sub>1 \<simeq> e) \<and> (g \<turnstile> n\<^sub>2 \<simeq> e) \<and> stamp g n\<^sub>1 = stamp g n\<^sub>2) \<longrightarrow> n\<^sub>1 = n\<^sub>2"
      assume "n\<^sub>1 \<in> true_ids g'"
      assume "n\<^sub>2 \<in> true_ids g'"
      show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2" 
      proof (cases "n\<^sub>1 \<in> true_ids g")
        case n1: True
        then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
        proof (cases "n\<^sub>2 \<in> true_ids g")
          case n2: True
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have n1rep: "g \<turnstile> n\<^sub>1 \<simeq> e"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            using ConstantNodeNew.prems(1) IRGraph.true_ids_def n1 unchanged by auto
          have n2rep: "g \<turnstile> n\<^sub>2 \<simeq> e"
            using n2rep' kind_eq stamp_eq new_def add_preserves_rep
            using ConstantNodeNew.prems(1) IRGraph.true_ids_def n2 unchanged by auto
          have "stamp g n\<^sub>1 = stamp g n\<^sub>2"
            by (metis ConstantNodeNew.hyps(3) \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> fresh_node_subset n1rep n2rep new subset_stamp)
          then show ?thesis using 1
            using n1 n2
            using n1rep n2rep by blast
        next
          case False
          then show ?thesis sorry
        qed
      next
        case False
        then show ?thesis proof (cases "n\<^sub>2 \<in> true_ids g")
          case True
          then show ?thesis sorry
        next
          case False
          then show ?thesis sorry
        qed
      qed
  next
    case (ParameterNodeSame g i s n)
    then show ?case by blast
  next
    case (ParameterNodeNew g i s n g')
    moreover have "\<not>(is_RefNode (ParameterNode i)) \<and> ParameterNode i \<noteq> NoNode"
      by simp
    moreover have "n \<notin> ids g"
      using calculation(2) fresh_ids by blast
    ultimately show ?case using new_node_not_present true_ids_add_update
      maintain_maximal_sharing fresh_node_subset
      by (meson encodes_contains fresh_ids ids_some)
  next
    case (ConditionalNodeSame g ce g2 c te g3 t fe g4 f s' n)
    then show ?case by blast
  next
    case (ConditionalNodeNew g ce g2 c te g3 t fe g4 f s' n g')
    moreover have "\<not>(is_RefNode (ConditionalNode c t f)) \<and> ConditionalNode c t f \<noteq> NoNode"
      by simp
    moreover have "n \<notin> ids g4"
      using fresh_ids
      using calculation(9) by blast
    ultimately show ?case using new_node_not_present true_ids_add_update
      maintain_maximal_sharing fresh_node_subset
      by (meson encodes_contains fresh_ids ids_some)
  next
    case (UnaryNodeSame g xe g2 x s' op n)
    then show ?case by blast
  next
    case (UnaryNodeNew g xe g2 x s' op n g')
    moreover have "\<not>(is_RefNode (unary_node op x)) \<and> unary_node op x \<noteq> NoNode"
      by (cases op; auto)
    moreover have "n \<notin> ids g2"
      using fresh_ids
      using calculation(5) by blast
    ultimately show ?case using new_node_not_present true_ids_add_update
      maintain_maximal_sharing fresh_node_subset
      by (meson encodes_contains fresh_ids ids_some)
  next
    case (BinaryNodeSame g xe g2 x ye g3 y s' op n)
    then show ?case by blast
  next
    case (BinaryNodeNew g xe g2 x ye g3 y s' op n g')
    moreover have "\<not>(is_RefNode (bin_node op x y)) \<and> bin_node op x y \<noteq> NoNode"
      by (cases op; auto)
    moreover have "n \<notin> ids g3"
      using fresh_ids
      using calculation(7) by blast
    ultimately show ?case using new_node_not_present true_ids_add_update
      maintain_maximal_sharing fresh_node_subset
      by (meson encodes_contains fresh_ids ids_some)
  next
    case (AllLeafNodes g n s)
    then show ?case by blast
  qed
  done
*)

end