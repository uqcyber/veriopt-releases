subsection \<open>Data-flow Tree Theorems\<close>

theory IRTreeEvalThms
  imports
    IRTreeEval
begin

subsubsection \<open>Deterministic Data-flow Evaluation\<close>

lemma evalDet:
  "[m,p] \<turnstile> e \<mapsto> v\<^sub>1 \<Longrightarrow> 
   [m,p] \<turnstile> e \<mapsto> v\<^sub>2 \<Longrightarrow>
   v\<^sub>1 = v\<^sub>2"
  apply (induction arbitrary: v\<^sub>2 rule: "evaltree.induct")
  by (elim EvalTreeE; auto)+

lemma evalAllDet:
  "[m,p] \<turnstile> e \<mapsto>\<^sub>L v1 \<Longrightarrow> 
   [m,p] \<turnstile> e \<mapsto>\<^sub>L v2 \<Longrightarrow>
   v1 = v2"
  apply (induction arbitrary: v2 rule: "evaltrees.induct")
   apply (elim EvalTreeE; auto)
  using evalDet by force


subsubsection \<open>Evaluation Results are Valid\<close>

text \<open>A valid value cannot be $UndefVal$.\<close>
lemma valid_not_undef:
  assumes a1: "valid_value val s"
  assumes a2: "s \<noteq> VoidStamp"
  shows "val \<noteq> UndefVal"
  apply (rule valid_value.elims(1)[of val s True])
  using a1 a2 by auto

(* Elimination rules for valid_value, for each kind of stamp. *)
lemma valid_VoidStamp[elim]:
  shows "valid_value val VoidStamp \<Longrightarrow>
      val = UndefVal"
  using valid_value.simps by metis

lemma valid_ObjStamp[elim]:
  shows "valid_value val (ObjectStamp klass exact nonNull alwaysNull) \<Longrightarrow>
      (\<exists>v. val = ObjRef v)"
  using valid_value.simps by (metis val_to_bool.cases)

lemma valid_int32[elim]:
  shows "valid_value val (IntegerStamp 32 l h) \<Longrightarrow>
      (\<exists>v. val = IntVal32 v)"
  apply (rule val_to_bool.cases[of val])
  using Value.distinct by simp+
                    
lemma valid_int64[elim]:
  shows "valid_value val (IntegerStamp 64 l h) \<Longrightarrow>
      (\<exists>v. val = IntVal64 v)"
  apply (rule val_to_bool.cases[of val])
  using Value.distinct by simp+

lemmas valid_value_elims =
  valid_VoidStamp
  valid_ObjStamp
  valid_int32
  valid_int64


lemma evaltree_not_undef:
  fixes m p e v
  shows "([m,p] \<turnstile> e \<mapsto> v) \<Longrightarrow> v \<noteq> UndefVal"
  apply (induction rule: "evaltree.induct")
  using valid_not_undef by auto


lemma leafint32:
  assumes ev: "[m,p] \<turnstile> LeafExpr i (IntegerStamp 32 lo hi) \<mapsto> val"
  shows "\<exists>v. val = (IntVal32 v)"
(* Note: we could also add: ...\<and> lo \<le> sint v \<and> sint v \<le> hi *)
proof - 
  have "valid_value val (IntegerStamp 32 lo hi)"
    using ev by (rule LeafExprE; simp)
  then show ?thesis by auto
qed


lemma leafint64:
  assumes ev: "[m,p] \<turnstile> LeafExpr i (IntegerStamp 64 lo hi) \<mapsto> val"
  shows "\<exists>v. val = (IntVal64 v)"
(* Note: we could also add: ...\<and> lo \<le> sint v \<and> sint v \<le> hi *)
proof -
  have "valid_value val (IntegerStamp 64 lo hi)"
    using ev by (rule LeafExprE; simp)
  then show ?thesis by auto
qed

lemma default_stamp [simp]: "default_stamp = IntegerStamp 32 (-2147483648) 2147483647"
  using default_stamp_def by auto

lemma valid32 [simp]:
  assumes "valid_value val (IntegerStamp 32 lo hi)"
  shows "\<exists>v. (val = (IntVal32 v) \<and> lo \<le> sint v \<and> sint v \<le> hi)"
  using assms valid_int32 by force 

lemma valid64 [simp]:
  assumes "valid_value val (IntegerStamp 64 lo hi)"
  shows "\<exists>v. (val = (IntVal64 v) \<and> lo \<le> sint v \<and> sint v \<le> hi)"
  using assms valid_int64 by force

lemma valid32or64:
  assumes "valid_value x (IntegerStamp b lo hi)"
  shows "(\<exists> v1. (x = IntVal32 v1)) \<or> (\<exists> v2. (x = IntVal64 v2))"
  using valid32 valid64 assms valid_value.elims(2) by blast

lemma valid32or64_both:
  assumes "valid_value x (IntegerStamp b lox hix)"
  and "valid_value y (IntegerStamp b loy hiy)"
  shows "(\<exists> v1 v2. x = IntVal32 v1 \<and> y = IntVal32 v2) \<or> (\<exists> v3 v4. x = IntVal64 v3 \<and> y = IntVal64 v4)"
  using assms valid32or64 valid32 valid_value.elims(2) valid_value.simps(1) by metis


subsubsection \<open>Example Data-flow Optimisations\<close>

(* An example refinement: a + 0 = a *)
lemma a0a_helper [simp]:
  assumes a: "valid_value v (IntegerStamp 32 lo hi)"
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
  assumes "valid_value x (IntegerStamp 32 lox hix)"
  assumes "valid_value y (IntegerStamp 32 loy hiy)"
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



subsubsection \<open>Monotonicity of Expression Refinement\<close>

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

lemma never_void:
  assumes "[m, p] \<turnstile> x \<mapsto> xv"
  assumes "valid_value xv (stamp_expr xe)"
  shows "stamp_expr xe \<noteq> VoidStamp"
  using valid_value.simps
  using assms(2) by force

lemma stamp32:
  "\<exists>v . xv = IntVal32 v \<longleftrightarrow> valid_value xv (IntegerStamp 32 lo hi)"
  using valid_int32
  by (metis (full_types) Value.inject(1) zero_neq_one)

lemma stamp64:
  "\<exists>v . xv = IntVal64 v \<longleftrightarrow> valid_value xv (IntegerStamp 64 lo hi)"
  using valid_int64
  by (metis (full_types) Value.inject(2) zero_neq_one)

lemma stamprange:
  "valid_value v s \<longrightarrow> (\<exists>b lo hi. (s = IntegerStamp b lo hi) \<and> (b = 32 \<or> b = 64))"
  using valid_value.elims stamp32 stamp64
  by (smt (verit, del_insts))

lemma compatible_trans:
  "compatible x y \<and> compatible y z \<Longrightarrow> compatible x z"
  by (smt (verit, best) compatible.elims(2) compatible.simps(1))

lemma compatible_refl:
  "compatible x y \<Longrightarrow> compatible y x"
  using compatible.elims(2) by fastforce

(*
lemma tmp:
  assumes "[m, p] \<turnstile> xe \<mapsto> xv"
  shows "valid_value xv (stamp_expr xe)"
  sorry (* proved later *)

lemma helping:
  assumes "[m, p] \<turnstile> xe \<mapsto> xv"
  assumes "\<forall>m p v. ([m,p] \<turnstile> xe \<mapsto> v) \<longrightarrow> [m,p] \<turnstile> ye \<mapsto> v"
  shows "compatible (stamp_expr xe) (stamp_expr ye)"
proof -
  have "[m, p] \<turnstile> ye \<mapsto> xv"
    using assms(1,2)
    by blast
  then have "valid_value xv (stamp_expr ye)"
    using tmp by simp
  then show ?thesis using stamprange
      apply (cases "\<exists>v. xv = IntVal32 v")
    using assms(2) valid_value.elims(2)
    using assms(1) tmp apply fastforce
    by (smt (verit, del_insts) assms(1) compatible.simps(1) tmp valid_value.elims(2))
qed
*)

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
  (*have co: "compatible (stamp_expr te) (stamp_expr fe)"
    using a by auto*)
  define branch  where b:  "branch  = (if val_to_bool cond then te else fe)"
  define branch' where b': "branch' = (if val_to_bool cond then te' else fe')"
  then have beval: "[m,p] \<turnstile> branch \<mapsto> v" using a b ce evalDet by blast 
  (*then have "compatible (stamp_expr branch) (stamp_expr branch')"
      using helping
      using assms(2) assms(3) b b' by force
  then have compatible: "compatible (stamp_expr te') (stamp_expr fe')"
    using compatible_trans co compatible_refl
    proof (cases "val_to_bool cond")
      case True
      then have "branch = te"
        using b by simp
      from True have "branch' = te'"
        using b' by simp
      then have "compatible (stamp_expr te) (stamp_expr te')"
        using \<open>branch = te\<close> \<open>compatible (stamp_expr branch) (stamp_expr branch')\<close> by blast
      then have "compatible (stamp_expr fe) (stamp_expr fe')"
        using co compatible_trans compatible_refl sorry
      then show ?thesis
        using \<open>compatible (stamp_expr te) (stamp_expr te')\<close> co compatible_refl compatible_trans by blast
    next
      case False
      then show ?thesis sorry
    qed*)
  from beval have "[m,p] \<turnstile> branch' \<mapsto> v" using assms b b' by auto
  then show "[m,p] \<turnstile> ConditionalExpr ce' te' fe' \<mapsto> v"
    using ConditionalExpr ce' b'
    using a by blast
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

