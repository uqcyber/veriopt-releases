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
      have int: "is_IntVal v" using bin_eval_int prems by auto
      show ?thesis
        unfolding prems x y xy (* get it in form: ConstantExpr c \<longmapsto> c *)
        apply (rule ConstantExpr)
        apply (rule validIntConst)
        using prems x y xy int by auto+
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
  assumes 1: "intval_add x (IntVal32 0) \<noteq> UndefVal"
  shows "intval_add x (IntVal32 0) = x"
  using 1 by (induction x; simp)


optimization AddNeutral: "(e + (const (IntVal32 0))) \<longmapsto> e"
  unfolding le_expr_def apply auto
  unfolding is_neutral_0 apply auto
  done


ML_val \<open>@{term \<open>x = y\<close>}\<close>

optimization NeutralLeftSub[intval]: "((e\<^sub>1 - e\<^sub>2) + e\<^sub>2) \<longmapsto> e\<^sub>1"
   prefer 3 unfolding intval.simps
(* NOTE: this unfolds to three goals, but the first one is not easy to instantiate.
         Maybe it needs to be universally quantified like 'just_goal2' below.
 1. intval_add (intval_sub e\<^sub>1' e\<^sub>2') e\<^sub>2' \<noteq> UndefVal \<and>
    e\<^sub>1' \<noteq> UndefVal \<longrightarrow>
    intval_add (intval_sub e\<^sub>1' e\<^sub>2') e\<^sub>2' = e\<^sub>1'
 2. intval_add (intval_sub e\<^sub>1' e\<^sub>2') e\<^sub>2' \<noteq> UndefVal \<and>
    e\<^sub>1' \<noteq> UndefVal \<longrightarrow>
    intval_add (intval_sub e\<^sub>1' e\<^sub>2') e\<^sub>2' = e\<^sub>1' \<Longrightarrow>
    BinaryExpr BinAdd (BinaryExpr BinSub e\<^sub>1 e\<^sub>2) e\<^sub>2 \<sqsupseteq> e\<^sub>1
 3. Common.size e\<^sub>1
    < Common.size
       (BinaryExpr BinAdd (BinaryExpr BinSub e\<^sub>1 e\<^sub>2) e\<^sub>2)
*)
   using intval_add.simps intval_sub.simps
    apply (metis (no_types, lifting) diff_add_cancel val_to_bool.cases)
  unfolding le_expr_def unfold_binary unfold_const unfold_valid32 bin_eval.simps
(*  subgoal premises
   apply (auto)
    subgoal premises p2 for m p x y ya
    print_facts
    thm evalDet[of m p e\<^sub>2 ya y]
    (* use evalDet to deduce ya=y and rewrite ya to y *)
    using p2 apply (simp add: evalDet[of m p e\<^sub>2 ya y])
    apply (subgoal_tac "intval_add (intval_sub x y) y = x")
    apply simp
*)

  subgoal premises p1
    apply ((rule allI)+; rule impI)
    subgoal premises p2 for m p v
      print_facts
    proof -
      obtain x y xa where xa: "[m,p] \<turnstile> e\<^sub>1 \<mapsto> xa" and "xa \<noteq> UndefVal"
        and y: "[m,p] \<turnstile> e\<^sub>2 \<mapsto> y"      and "y \<noteq> UndefVal"
        and x: "x = intval_sub xa y" and "x \<noteq> UndefVal"
        and v: "v = intval_add x y"  and "v \<noteq> UndefVal"
        by (metis evalDet p2 evaltree_not_undef)
      then have "v = intval_add (intval_sub xa y) y" by auto
      then have "v = xa"
        print_facts
        using p1 p2 apply simp
        by (smt (z3) Value.distinct(9) Value.inject(1) Value.inject(2) \<open>v \<noteq> UndefVal\<close> x \<open>x \<noteq> UndefVal\<close> diff_add_cancel intval_add.elims intval_sub.elims) 
      then show "[m,p] \<turnstile> e\<^sub>1 \<mapsto> v"
        by (simp add: xa)
      thm intval_add.elims
    qed
    done
  using size_non_const by fastforce


(* a little helper lemma for using universal quantified assumptions *)
lemma allE2: "(\<forall>x y. P x y) \<Longrightarrow> (P a b \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma just_goal2: 
  assumes 1: "(\<forall> a b. (intval_add (intval_sub a b) b \<noteq> UndefVal \<and> a \<noteq> UndefVal \<longrightarrow>
    intval_add (intval_sub a b) b = a))"
  shows "(BinaryExpr BinAdd (BinaryExpr BinSub e\<^sub>1 e\<^sub>2) e\<^sub>2) \<ge> e\<^sub>1"
(* without unfold_binary: but can this be done better?  
  unfolding le_expr_def 
  apply (auto)
  subgoal premises 2 for m p y xa ya
  print_facts
  thm evalDet[of m p e2 y ya]
  apply (simp add:evalDet[OF 2(1) 2(4)])
  thm allE2[of _ xa ya]
  using 1 apply (rule allE2[of _ xa ya])
  using 2 by (metis evalDet evaltree_not_undef) 
  done
*)
(*  using unfold_binary: *)
  unfolding le_expr_def unfold_binary bin_eval.simps
  by (metis 1 evalDet evaltree_not_undef)


optimization NeutralRightSub[intval]: " e\<^sub>2 + (e\<^sub>1 - e\<^sub>2) \<longmapsto> e\<^sub>1"
  using NeutralLeftSub(1) intval_add_sym apply auto[1]
  oops

(* these are the three proof obligations it should generate? *)
lemma NeutralRightSub_1: "intval_add a (intval_sub b a) \<noteq> UndefVal \<and>
    b \<noteq> UndefVal \<longrightarrow>
    intval_add a (intval_sub b a) = b" (is "?U1 \<and> ?U2 \<longrightarrow> ?C")
proof 
  assume "?U1 \<and> ?U2"
  (* split into 32 and 64 bit cases: *)
  then have i: "(is_IntVal32 a \<and> is_IntVal32 b) \<or> (is_IntVal64 a \<and> is_IntVal64 b)" (is "?I32 \<or> ?I64")
    by (metis Value.exhaust_disc intval_add.simps(10) intval_add.simps(15) intval_add.simps(16) intval_add_sym intval_sub.simps(12) intval_sub.simps(5) intval_sub.simps(8) intval_sub.simps(9) is_IntVal32_def is_IntVal64_def is_ObjRef_def is_ObjStr_def)
  then show ?C
  proof (rule disjE)
    assume i32: ?I32
    show ?C using i32 add.commute is_IntVal32_def by auto
  next
    assume i64: ?I64
    show ?C using i64 add.commute is_IntVal64_def by auto
  qed
qed

(* An experiment to see if the generated assumption is useful? *)
lemma NeutralRightSub_2:
  (* does not use the assms because uses NeutralRightSub_1 instead *)
  "(( intval_add a (intval_sub b a) \<noteq> UndefVal \<and> b \<noteq> UndefVal
      \<longrightarrow> intval_add a (intval_sub b a) = b)
    \<Longrightarrow> BinaryExpr BinAdd e\<^sub>2 (BinaryExpr BinSub e\<^sub>1 e\<^sub>2) \<ge> e\<^sub>1)"
  unfolding le_expr_def unfold_binary
  subgoal premises 1
    apply (rule allI)+
    subgoal for m p v
      apply auto
      subgoal premises 2 for a b c
        thm evalDet[OF 2(1) 2(5)] (* show that a and c are the same *)
        unfolding evalDet[OF 2(1) 2(5)]
        using "2"(2) "2"(4) NeutralRightSub_1 \<open>a = c\<close> by fastforce 
      done
    done
  done

lemma NeutralRightSub_3:
  "(size e\<^sub>1 < size (BinaryExpr BinAdd e\<^sub>2 (BinaryExpr BinSub e\<^sub>1 e\<^sub>2)))"
  using size_non_const by fastforce



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

*)

(* Value level proofs *)
lemma val_redundant_add_sub:
  assumes "b \<noteq> UndefVal \<and> a \<noteq> UndefVal \<and> intval_add b a \<noteq> UndefVal"
  shows "val[(b + a) - b] = val[a]"
  using assms apply (cases a; cases b; auto)
  done

lemma val_add_right_negate_to_sub:
  assumes "x \<noteq> UndefVal \<and> e \<noteq> UndefVal \<and> intval_add x e \<noteq> UndefVal"
  shows "val[x + (-e)] = val[x - e]"
  using assms apply (cases x; cases e; auto)
  done

(* Exp level proofs *)
lemma exp_add_left_negate_to_sub:
 "exp[-e + y] \<ge> exp[y - e]"
  apply (cases e; cases y; auto)
  using AddToSubHelperLowLevel apply auto+
  done

(* Optimizations *)
optimization opt_redundant_sub_add: "(b + a) - b \<longmapsto> a"
   apply unfold_optimization apply simp_all apply auto using val_redundant_add_sub 
   apply (metis evalDet intval_add.simps(10) intval_sub.simps(10))
  done

optimization opt_add_right_negate_to_sub: "(x + (-e)) \<longmapsto> x - e"
   apply unfold_optimization apply simp_all apply auto using AddToSubHelperLowLevel intval_add_sym 
   apply auto
  done

optimization opt_add_left_negate_to_sub: "-x + y \<longmapsto> y - x"
  using exp_add_left_negate_to_sub rewrite_preservation.simps(1) apply blast apply simp_all
  done
  


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