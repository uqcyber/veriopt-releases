subsection \<open>AddNode Phase\<close>

theory AddPhase
  imports
    Common
begin

phase AddNode 
  terminating size
begin

lemma binadd_commute:
  assumes "bin_eval BinAdd x y \<noteq> UndefVal"
  shows "bin_eval BinAdd x y = bin_eval BinAdd y x"
  by (simp add: intval_add_sym)

(* horrible backward proof - needs improving *)
optimization AddShiftConstantRight: "((const v) + y) \<longmapsto> y + (const v) when \<not>(is_ConstantExpr y)"
  apply (metis add_2_eq_Suc' less_Suc_eq plus_1_eq_Suc size.simps(11) size_non_add)
  using le_expr_def binadd_commute by blast

optimization AddShiftConstantRight2: "((const v) + y) \<longmapsto> y + (const v) when \<not>(is_ConstantExpr y)"
  using AddShiftConstantRight by auto

(* TODO: define is_neutral and then lemmas like this: 
lemma simp_neutral:
  assumes n: "is_neutral op (IntVal32 n)" 
  shows "bin_eval op x (IntVal32 n) = x"
  apply (induction op)
  unfolding is_neutral.simps 
  using n apply auto
*)

(* poor-mans is_neutral lemma *)
lemma is_neutral_0 [simp]:
  assumes "val[(IntVal b x) + (IntVal b 0)] \<noteq> UndefVal"
  shows "val[(IntVal b x) + (IntVal b 0)] = (new_int b x)"
  by simp

optimization AddNeutral: "(e + (const (IntVal 32 0))) \<longmapsto> e"
  apply auto
  by (smt (verit) add_cancel_left_right intval_add.elims val_to_bool.simps(1) eval_unused_bits_zero
      le_expr_def)

ML_val \<open>@{term \<open>x = y\<close>}\<close>

lemma NeutralLeftSubVal:
  assumes "e1 = new_int b ival"
  shows "val[(e1 - e2) + e2] \<approx> e1"
  using assms by (cases e1; cases e2; auto)
  
optimization RedundantSubAdd: "((e\<^sub>1 - e\<^sub>2) + e\<^sub>2) \<longmapsto> e\<^sub>1"
  apply auto
  by (smt (verit) evalDet intval_sub.elims new_int.elims well_formed_equal_defn NeutralLeftSubVal
      eval_unused_bits_zero)

(* a little helper lemma for using universal quantified assumptions *)
lemma allE2: "(\<forall>x y. P x y) \<Longrightarrow> (P a b \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma just_goal2: 
  assumes "(\<forall> a b. (val[(a - b) + b] \<noteq> UndefVal \<and> a \<noteq> UndefVal \<longrightarrow>
                    val[(a - b) + b] = a))"
  shows "(exp[(e\<^sub>1 - e\<^sub>2) + e\<^sub>2]) \<ge> e\<^sub>1"
  unfolding le_expr_def unfold_binary bin_eval.simps by (metis assms evalDet evaltree_not_undef)

optimization RedundantSubAdd2: "e\<^sub>2 + (e\<^sub>1 - e\<^sub>2) \<longmapsto> e\<^sub>1"
  using size_binary_rhs_a apply simp 
  by (smt (verit, del_insts) BinaryExpr BinaryExprE RedundantSubAdd(1) binadd_commute le_expr_def 
      rewrite_preservation.simps(1) size.simps(4) add_2_eq_Suc')

(* Demonstration of our FOUR levels of expression rewrites:
   =======================================================
  level 1 (Java-like): "-e + y \<longmapsto> y - e"
  level 2 (expr trees): "rewrite_preservation
     (BinaryExpr BinAdd (UnaryExpr UnaryNeg e) y \<longmapsto> BinaryExpr BinSub y e) &&&
    rewrite_termination
     (BinaryExpr BinAdd (UnaryExpr UnaryNeg e) y \<longmapsto> BinaryExpr BinSub y e)
     Common.size"
  level 2b: "BinaryExpr BinAdd (UnaryExpr UnaryNeg e) y \<le> BinaryExpr BinSub y e"
  level 2c: "\<forall>m p v. ([m,p] \<turnstile> BinaryExpr BinAdd (UnaryExpr UnaryNeg e) y \<mapsto> v)
                   \<longrightarrow> ([m,p] \<turnstile> BinaryExpr BinSub y e \<mapsto> v)"
  level 3 (intval ops): "\<And>m p xa ya.
       [m,p] \<turnstile> e \<mapsto> xa \<Longrightarrow>
       [m,p] \<turnstile> y \<mapsto> ya \<Longrightarrow>
       intval_negate xa \<noteq> UndefVal \<Longrightarrow>
       intval_add (intval_negate xa) ya \<noteq> UndefVal \<Longrightarrow>
       \<exists>x. ([m,p] \<turnstile> y \<mapsto> x) \<and>
           (\<exists>y. ([m,p] \<turnstile> e \<mapsto> y) \<and>
                intval_add (intval_negate xa) ya =
                intval_sub x y)"
  level 3b: "\<forall>m p v.
       (\<exists>x ya.
           (\<exists>xa. ([m,p] \<turnstile> e \<mapsto> xa) \<and>
                 x = intval_negate xa \<and> x \<noteq> UndefVal) \<and>
                 ([m,p] \<turnstile> y \<mapsto> ya) \<and>
                 v = intval_add x ya \<and> v \<noteq> UndefVal) \<longrightarrow>
       (\<exists>x ya.
           ([m,p] \<turnstile> y \<mapsto> x) \<and>
           ([m,p] \<turnstile> e \<mapsto> ya) \<and>
            v = intval_sub x ya \<and> v \<noteq> UndefVal)"
  level 4 (Word library): "-ev + yv = yv - ev" (twice, for 32-bit and 64-bit)
*)


(* The LowLevel version, intval_*, of this helper lemma is much easier
   to prove than the bin_eval level.  And equally easy to use in AddToSub.
 *)
lemma AddToSubHelperLowLevel:
  shows "val[-e + y] = val[y - e]" (is "?x = ?y")
  by (induction y; induction e; auto)

print_phases

(* -----  Starts here -----  *)

(* 
 AddNode has 8 optimisations total
 Currently *6* optimisations are verified.

 -- Already verified above --

 - AddShiftRightConst
 - RedundantSubAdd
 - AddNeutral (32-bit only)

 -- Verified below --
 
 - RedundantAddSub
 - AddRightNegateToSub
 - AddLeftNegateToSub 

 -- Left to go --
 - MergeSignExtendAdd
 - MergeZeroExtendAdd

*)

(* Value level proofs *)
lemma val_redundant_add_sub:
  assumes "a = new_int bb ival"
  assumes "val[b + a] \<noteq> UndefVal"
  shows "val[(b + a) - b] = a"
  using assms apply (cases a; cases b; auto) by presburger

lemma val_add_right_negate_to_sub:
  assumes "val[x + e] \<noteq> UndefVal"
  shows "val[x + (-e)] = val[x - e]"
  by (cases x; cases e; auto simp: assms)

(* Exp level proofs *)
lemma exp_add_left_negate_to_sub:
  "exp[-e + y] \<ge> exp[y - e]"
  by (cases e; cases y; auto simp: AddToSubHelperLowLevel)

text \<open>Optimisations\<close>

optimization RedundantAddSub: "(b + a) - b \<longmapsto> a"
  apply auto
  by (smt (verit) evalDet intval_add.elims new_int.elims val_redundant_add_sub 
      eval_unused_bits_zero)

optimization AddRightNegateToSub: "x + -e \<longmapsto> x - e"
  apply (metis Nat.add_0_right add_2_eq_Suc' add_less_mono1 add_mono_thms_linordered_field(2) 
         less_SucI not_less_less_Suc_eq size_binary_const size_non_add size_pos)
  using AddToSubHelperLowLevel intval_add_sym by auto

optimization AddLeftNegateToSub: "-e + y \<longmapsto> y - e"
  apply (smt (verit, best) One_nat_def add.commute add_Suc_right is_ConstantExpr_def less_add_Suc2 
         numeral_2_eq_2 plus_1_eq_Suc size.simps(1) size.simps(11) size_binary_const size_non_add)
  using exp_add_left_negate_to_sub by simp

(* ----- Ends here ----- *)

end

(* Isabelle Isar Questions:
 Why doesn't subgoal handle \forall and \<longrightarrow> ?
 Then this pattern might become just a single subgoal?
  subgoal premises p1
    apply ((rule allI)+; rule impI)
    subgoal premises p2 for m p v
*)
end