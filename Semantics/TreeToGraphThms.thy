subsection \<open>Tree to Graph Theorems\<close>

theory TreeToGraphThms
imports
  TreeToGraph
  IRTreeEvalThms
  "HOL-Eisbach.Eisbach"
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


method solve_det uses node =
  (match node in "kind _ _ = node _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ = node _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x. _ = node x \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>metis i e r\<close>\<close>\<close>\<close> |
   match node in "kind _ _ = node _ _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ _ = node _ _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x y. _ = node x y \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>metis i e r\<close>\<close>\<close>\<close> |
   match node in "kind _ _ = node _ _ _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ _ _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ _ _ = node _ _ _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x y z. _ = node x y z \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>metis i e r\<close>\<close>\<close>\<close> |
  match node in "kind _ _ = node _ _ _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ _ _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ _ _ = node _ _ _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x. _ = node _ _ x \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>metis i e r\<close>\<close>\<close>\<close>)

text \<open>Now we can prove that 'rep' and 'eval', and their list versions, are deterministic.
\<close>
lemma repDet:
  shows "(g \<turnstile> n \<simeq> e\<^sub>1) \<Longrightarrow> (g \<turnstile> n \<simeq> e\<^sub>2) \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
proof (induction arbitrary: e\<^sub>2 rule: "rep.induct")
  case (ConstantNode n c)
  then show ?case using rep_constant by auto
next
  case (ParameterNode n i s)
  then show ?case using rep_parameter by auto
next
  case (ConditionalNode n c t f ce te fe)
  then show ?case 
    by (solve_det node: ConditionalNode)
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
    by (metis IRNode.inject(28) NarrowNodeE rep_narrow)
next
  case (SignExtendNode n x xe)
  then show ?case
    using SignExtendNodeE rep_sign_extend IRNode.inject(39)
    by (metis IRNode.inject(39) rep_sign_extend)
next
  case (ZeroExtendNode n x xe)
  then show ?case
    by (metis IRNode.inject(50) ZeroExtendNodeE rep_zero_extend)
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

lemma encodeEvalDet:
  "[g,m,p] \<turnstile> e \<mapsto> v1 \<Longrightarrow> 
   [g,m,p] \<turnstile> e \<mapsto> v2 \<Longrightarrow>
   v1 = v2"
  by (metis encodeeval_def evalDet repDet)

lemma graphDet: "([g,m,p] \<turnstile> nid \<mapsto> v\<^sub>1) \<and> ([g,m,p] \<turnstile> nid \<mapsto> v\<^sub>2) \<Longrightarrow> v\<^sub>1 = v\<^sub>2"
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
  by (metis ConditionalNodeE IRNode.inject(6) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) mono_conditional repDet rep_conditional)

lemma mono_add:
  assumes "kind g1 n = AddNode x y \<and> kind g2 n = AddNode x y"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "(g1 \<turnstile> y \<simeq> ye1) \<and> (g2 \<turnstile> y \<simeq> ye2)"
  assumes "xe1 \<ge> xe2 \<and> ye1 \<ge> ye2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  using mono_binary assms
  by (metis AddNodeE IRNode.inject(2) repDet rep_add)

lemma mono_mul:
  assumes "kind g1 n = MulNode x y \<and> kind g2 n = MulNode x y"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "(g1 \<turnstile> y \<simeq> ye1) \<and> (g2 \<turnstile> y \<simeq> ye2)"
  assumes "xe1 \<ge> xe2 \<and> ye1 \<ge> ye2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  using mono_binary assms
  by (metis IRNode.inject(27) MulNodeE repDet rep_mul)


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

lemma subset_implies_evals:
  assumes "as_set g1 \<subseteq> as_set g2"
  shows "(g1 \<turnstile> n \<simeq> e) \<Longrightarrow> (g2 \<turnstile> n \<simeq> e)"
proof (induction e arbitrary: n)
  case (UnaryExpr op e)
  then have "n \<in> ids g1"
    using no_encoding by force
  then have "kind g1 n = kind g2 n"
    using assms unfolding as_set_def
    by blast
  then show ?case using UnaryExpr UnaryRepE
    by (smt (verit, ccfv_threshold) AbsNode LogicNegationNode NarrowNode NegateNode NotNode SignExtendNode ZeroExtendNode)
next
  case (BinaryExpr op e1 e2)
  then have "n \<in> ids g1"
    using no_encoding by force
  then have "kind g1 n = kind g2 n"
    using assms unfolding as_set_def
    by blast
  then show ?case using BinaryExpr BinaryRepE
    by (smt (verit, ccfv_threshold) AddNode MulNode SubNode AndNode OrNode XorNode IntegerBelowNode IntegerEqualsNode IntegerLessThanNode)
next
  case (ConditionalExpr e1 e2 e3)
  then have "n \<in> ids g1"
    using no_encoding by force
  then have "kind g1 n = kind g2 n"
    using assms unfolding as_set_def
    by blast
  then show ?case using ConditionalExpr ConditionalExprE
    by (smt (verit, best) ConditionalNode ConditionalNodeE)
next
  case (ConstantExpr x)
  then have "n \<in> ids g1"
    using no_encoding by force
  then have "kind g1 n = kind g2 n"
    using assms unfolding as_set_def
    by blast
  then show ?case using ConstantExpr ConstantExprE
    by (metis ConstantNode ConstantNodeE)
next
  case (ParameterExpr x1 x2)
  then have in_g1: "n \<in> ids g1"
    using no_encoding by force
  then have kinds: "kind g1 n = kind g2 n"
    using assms unfolding as_set_def
    by blast
  from in_g1 have stamps: "stamp g1 n = stamp g2 n"
    using assms unfolding as_set_def
    by blast
  from kinds stamps show ?case using ParameterExpr ParameterExprE
    by (metis ParameterNode ParameterNodeE)
next
  case (LeafExpr nid s)
  then have in_g1: "n \<in> ids g1"
    using no_encoding by force
  then have kinds: "kind g1 n = kind g2 n"
    using assms unfolding as_set_def
    by blast
  from in_g1 have stamps: "stamp g1 n = stamp g2 n"
    using assms unfolding as_set_def
    by blast
  from kinds stamps show ?case using LeafExpr LeafExprE LeafNode 
    by (smt (z3) IRExpr.distinct(29) IRExpr.simps(16) IRExpr.simps(28) rep.simps) (* slow *)
next
  case (ConstantVar x)
  then have in_g1: "n \<in> ids g1"
    using no_encoding by force
  then have kinds: "kind g1 n = kind g2 n"
    using assms unfolding as_set_def
    by blast
  from in_g1 have stamps: "stamp g1 n = stamp g2 n"
    using assms unfolding as_set_def
    by blast
  from kinds stamps show ?case using ConstantVar
    using rep.simps by blast
next 
  case (VariableExpr x s)
  then have in_g1: "n \<in> ids g1"
    using no_encoding by force
  then have kinds: "kind g1 n = kind g2 n"
    using assms unfolding as_set_def
    by blast
  from in_g1 have stamps: "stamp g1 n = stamp g2 n"
    using assms unfolding as_set_def
    by blast
  from kinds stamps show ?case using VariableExpr
    using rep.simps by blast
qed


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
  \<and> as_set g\<^sub>1 \<subseteq> as_set g\<^sub>2 \<and> maximal_sharing g\<^sub>1
  \<and> (g\<^sub>2 \<turnstile> n \<simeq> e\<^sub>2) \<and> maximal_sharing g\<^sub>2
  \<Longrightarrow> (g\<^sub>2 \<turnstile> n \<unlhd> e\<^sub>1) \<and> graph_refinement g\<^sub>1 g\<^sub>2"
  using subset_refines
  by (meson encodeeval_def graph_represents_expression_def le_expr_def)

end