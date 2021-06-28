section \<open>Data-flow Expression-Tree Theorems\<close>

theory IRTreeEvalThms
  imports
    Semantics.IRTreeEval
begin



(* Reverse form of evaltree.LeafExpr, because evaltree is deterministic. *)
lemma LeafExprRev: 
  "([m,p] \<turnstile> LeafExpr nid s \<mapsto> val)
   \<Longrightarrow> (val = m nid \<and>
        valid_value s val)"
  by auto


text \<open>Extraction and Evaluation of expression trees is deterministic.\<close>

(* TODO: prove that rep is deterministic? 
lemma repDet:
  fixes g n e1
  shows "(g \<turnstile> n \<triangleright> e1) \<Longrightarrow> 
         (\<forall> e2. ((g \<turnstile> n \<triangleright> e2) \<longrightarrow> e1 = e2))"
  apply (rule allI; rule impI)
  apply (contradiction "e1 \<noteq> e2")
    apply (induction rule: "rep.induct")
  apply (rule allI; rule impI)+
  apply (smt (z3) ConstantNodeE IRNode.disc IRNode.discI(7) IRNode.sel(62) rep.simps) 
                apply (rule allI; rule impI)
  using ParameterNodeE 
*)             

(* apply (rule allI; rule impI)+; elim RepE; auto*) 

lemma evalDet:
  fixes m p e v1
  shows "([m,p] \<turnstile> e \<mapsto> v1) \<Longrightarrow> 
         (\<forall> v2. (([m,p] \<turnstile> e \<mapsto> v2) \<longrightarrow> v1 = v2))"
  apply (induction rule: "evaltree.induct")
  by (rule allI; rule impI; elim EvalTreeE; auto)+

lemma evalAllDet:
  fixes m p e v1
  shows "([m,p] \<turnstile> e \<mapsto>\<^sub>L v1) \<Longrightarrow> 
         (\<forall> v2. (([m,p] \<turnstile> e \<mapsto>\<^sub>L v2) \<longrightarrow> v1 = v2))"
  apply (induction rule: "evaltrees.induct")
   apply (rule allI; rule impI)+
  using evaltrees.cases apply blast
  by (metis evalDet evaltrees.cases list.discI list.inject)


text \<open>A valid value cannot be $UndefVal$.\<close>
lemma valid_not_undef:
  assumes a1: "valid_value s val"
  assumes a2: "s \<noteq> VoidStamp"
  shows "val \<noteq> UndefVal"
  apply (rule valid_value.elims(1)[of s val True])
  using a1 a2 by auto


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
  then show ?thesis
    using "valid_value.cases"
    by (metis valid_value.elims(2) valid_value.simps(14)) 
qed

lemma default_stamp [simp]: "default_stamp = IntegerStamp 32 (- 2147483648) 2147483647"
  using default_stamp_def by auto

lemma valid32 [simp]:
  assumes a: "valid_value (IntegerStamp 32 lo hi) val"
  shows "\<exists>v. (val = (IntVal32 v) \<and> lo \<le> sint v \<and> sint v \<le> hi)"
 using a "valid_value.cases"
  by (metis Stamp.distinct(1) valid_value.elims(2) valid_value.simps(1))



subsection \<open>Example Data-flow Optimisations\<close>

(* An example refinement: a + 0 \<le> a *)
lemma a0a_helper [simp]:
  assumes a: "valid_value (IntegerStamp 32 lo hi) v"
  shows "intval_add v (IntVal32 0) = v"
proof -
  obtain v32 :: int32 where "v = (IntVal32 v32)" using a valid32 by blast
  then show ?thesis by simp 
qed

lemma a0a: "(BinaryExpr BinAdd (LeafExpr 1 default_stamp) (ConstantExpr (IntVal32 0)))
              \<le> (LeafExpr 1 default_stamp)" (is "?L \<le> ?R")
  by (auto simp add: evaltree.LeafExpr)


(* Another example refinement: x + (y - x) \<le> y *)
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
   \<le> (LeafExpr y (IntegerStamp 32 loy hiy))"
  by (auto simp add: LeafExpr)



subsection \<open>Monotonicity of Optimizing Expressions\<close>

text \<open>We prove that each subexpression position is monotonic.
That is, optimizing a subexpression anywhere deep inside a top-level expression
also optimizes that top-level expression.\<close>


lemma mono_unary: 
  assumes "e \<le> e'"
  shows "(UnaryExpr op e) \<le> (UnaryExpr op e')"
  using UnaryExpr assms by auto

lemma mono_binary: 
  assumes "x \<le> x'"
  assumes "y \<le> y'"
  shows "(BinaryExpr op x y) \<le> (BinaryExpr op x' y')"
  using BinaryExpr assms by auto 

lemma mono_conditional: 
  assumes "ce \<le> ce'"
  assumes "te \<le> te'"
  assumes "fe \<le> fe'"
  shows "(ConditionalExpr ce te fe) \<le> (ConditionalExpr ce' te' fe')"
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
  assumes "e1 \<le> e2"
  assumes "g \<triangleleft> e1 \<leadsto> (g1, x1)"
  assumes "g \<triangleleft> e2 \<leadsto> (g2, x2)"
  shows "\<forall> m m' h h'. (g \<turnstile> (x1, m, h) \<rightarrow> (nid, m', h'))
                  \<longrightarrow> (g \<turnstile> (x2, m, h) \<rightarrow> (nid, m', h'))"
*)
end

