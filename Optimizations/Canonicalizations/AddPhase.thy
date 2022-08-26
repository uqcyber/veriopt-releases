theory AddPhase
  imports
    Common
begin

section \<open>Optimizations for Add Nodes\<close>

phase SnipPhase 
  terminating size
begin

optimization BinaryFoldConstant: "BinaryExpr op (const v1) (const v2) \<longmapsto> ConstantExpr (bin_eval op v1 v2)"
  apply (cases op; simp)
  unfolding le_expr_def
  apply (rule allI impI)+
  subgoal premises bin for m p v
    print_facts
    apply (rule BinaryExprE[OF bin])
    subgoal premises prems for x y
      print_facts
(* backward refinement:
      apply (subgoal_tac "x = v1 \<and> y = v2")
        using prems apply auto
      apply (rule ConstantExpr)
      apply (rule validIntConst)
      using bin_eval_int int_stamp_both by auto
*)
(* or forward proof: *)
    proof -
      have x: "x = v1" using prems by auto
      have y: "y = v2" using prems by auto
      have xy: "v = bin_eval op x y" using prems x y by simp
      have int: "\<exists> b vv . v = new_int b vv" using bin_eval_new_int prems by auto
      show ?thesis
        unfolding prems x y xy (* get it in form: ConstantExpr c \<longmapsto> c *)
        apply (rule ConstantExpr)
        apply (rule validDefIntConst)
        using prems x y xy int sorry
      qed
    done
  done

print_facts

lemma binadd_commute:
  assumes "bin_eval BinAdd x y \<noteq> UndefVal"
  shows "bin_eval BinAdd x y = bin_eval BinAdd y x"
  using assms intval_add_sym by simp


(* horrible backward proof - needs improving *)
optimization AddShiftConstantRight: "((const v) + y) \<longmapsto> y + (const v) when \<not>(is_ConstantExpr y)"
  using size_non_const apply fastforce
  unfolding le_expr_def
  apply (rule impI)
  subgoal premises 1
    apply (rule allI impI)+
    (* apply auto  -- unfolds premise eval, but not concl. *)
    subgoal premises 2 for m p va
      apply (rule BinaryExprE[OF 2])  (* go forward from v+y *)
      subgoal premises 3 for x ya
        apply (rule BinaryExpr)       (* go backward from y+v *)
        using 3 apply simp
        using 3 apply simp
        using 3 binadd_commute apply auto
        done
      done
    done
  done


optimization AddShiftConstantRight2: "((const v) + y) \<longmapsto> y + (const v) when \<not>(is_ConstantExpr y)"
  unfolding le_expr_def
   apply (auto simp: intval_add_sym)
  (* termination proof *)
  using size_non_const by fastforce


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
  assumes 1: "intval_add (IntVal b x) (IntVal b 0) \<noteq> UndefVal"
  shows "intval_add (IntVal b x) (IntVal b 0) = (new_int b x)"
  using 1 by auto

optimization AddNeutral: "(e + (const (IntVal 32 0))) \<longmapsto> e"
  unfolding le_expr_def apply auto
  using is_neutral_0 eval_unused_bits_zero
  by (smt (verit) add_cancel_left_right intval_add.elims val_to_bool.simps(1))


ML_val \<open>@{term \<open>x = y\<close>}\<close>

lemma NeutralLeftSubVal:
  assumes "e1 = new_int b ival"
  shows "val[(e1 - e2) + e2] \<approx> e1"
  apply simp using assms by (cases e1; cases e2; auto)
  

optimization NeutralLeftSub: "((e\<^sub>1 - e\<^sub>2) + e\<^sub>2) \<longmapsto> e\<^sub>1"
  apply auto using eval_unused_bits_zero NeutralLeftSubVal
  unfolding well_formed_equal_defn
  by (smt (verit) evalDet intval_sub.elims new_int.elims)

(* a little helper lemma for using universal quantified assumptions *)
lemma allE2: "(\<forall>x y. P x y) \<Longrightarrow> (P a b \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma just_goal2: 
  assumes 1: "(\<forall> a b. (intval_add (intval_sub a b) b \<noteq> UndefVal \<and> a \<noteq> UndefVal \<longrightarrow>
    intval_add (intval_sub a b) b = a))"
  shows "(BinaryExpr BinAdd (BinaryExpr BinSub e\<^sub>1 e\<^sub>2) e\<^sub>2) \<ge> e\<^sub>1"
  unfolding le_expr_def unfold_binary bin_eval.simps
  by (metis 1 evalDet evaltree_not_undef)


optimization NeutralRightSub: " e\<^sub>2 + (e\<^sub>1 - e\<^sub>2) \<longmapsto> e\<^sub>1"
  by (smt (verit, del_insts) BinaryExpr BinaryExprE NeutralLeftSub(1) binadd_commute le_expr_def rewrite_preservation.simps(1))

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
  shows "intval_add (intval_negate e) y = intval_sub y e" (is "?x = ?y")
  by (induction y; induction e; auto)


optimization AddToSub: "-e + y \<longmapsto> y - e"
  using AddToSubHelperLowLevel by auto
  

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
 - mergeSignExtendAdd
 - mergeZeroExtendAdd

*)

(* Value level proofs *)
lemma val_redundant_add_sub:
  assumes "a = new_int bb ival"
  assumes "val[b + a] \<noteq> UndefVal"
  shows "val[(b + a) - b] = a"
  using assms apply (cases a; cases b; auto)
  by presburger

lemma val_add_right_negate_to_sub:
  assumes "val[x + e]\<noteq> UndefVal"
  shows "val[x + (-e)] = val[x - e]"
  using assms by (cases x; cases e; auto)

(* Exp level proofs *)
lemma exp_add_left_negate_to_sub:
 "exp[-e + y] \<ge> exp[y - e]"
  apply (cases e; cases y; auto)
  using AddToSubHelperLowLevel by auto+

(* Optimizations *)
optimization opt_redundant_sub_add: "(b + a) - b \<longmapsto> a"
   apply auto using val_redundant_add_sub eval_unused_bits_zero
  by (smt (verit) evalDet intval_add.elims new_int.elims)

optimization opt_add_right_negate_to_sub: "(x + (-e)) \<longmapsto> x - e"
   using AddToSubHelperLowLevel intval_add_sym by auto 

optimization opt_add_left_negate_to_sub: "-x + y \<longmapsto> y - x"
  using exp_add_left_negate_to_sub by blast

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