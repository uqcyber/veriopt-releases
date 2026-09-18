subsection \<open>AddNode Phase\<close>

theory AddPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase AddNode
  terminating size
begin

lemma binadd_commute:
  assumes "bin_eval BinAdd x y \<noteq> UndefVal"
  shows "bin_eval BinAdd x y = bin_eval BinAdd y x"
  by (simp add: intval_add_sym)

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

lemma AddNeutral_Exp:
  assumes "stamp_expr e = IntegerStamp b lo hi"
  assumes "wf_stamp e"
  shows "exp[e + (const (new_int b 0))] \<ge> exp[e]"
  apply auto
  subgoal premises p for m p x
  proof -
    obtain ev where ev: "[m,p] \<turnstile> e \<mapsto> ev"
      using p by auto
    obtain evv where evv: "ev = IntVal b evv"
      by (metis assms(1,2) valid_int wf_stamp_def ev)
    have "[m,p] \<turnstile> exp[e + (const (new_int b 0))] \<mapsto> val[ev + (new_int b 0)]"
      using ev evalDet p(1,2,3) by fastforce
    then show ?thesis
      by (metis ev evalDet eval_int_implies_truncated evv is_neutral_0 new_int_truncated_eq p(1,2))
  qed
  done

ML_val \<open>@{term \<open>x = y\<close>}\<close>

lemma NeutralLeftSubVal:
  assumes "e1 = new_int b ival"
  shows "val[(e1 - e2) + e2] \<approx> e1"
  using assms by (cases e1; cases e2; auto)

lemma RedundantSubAdd_Exp:
  shows "exp[(a - b) + b] \<ge> a"
  apply auto
  subgoal premises p for m p y xa ya
  proof -
    obtain bv where bv: "[m,p] \<turnstile> b \<mapsto> bv"
      using p(1) by auto
    obtain av where av: "[m,p] \<turnstile> a \<mapsto> av"
      using p(3) by auto
    then have subNotUndef: "val[av - bv] \<noteq> UndefVal"
      by (metis bv evalDet p(3,4,5))
    then obtain bb bvv where bInt: "bv = IntVal bb bvv"
      by (metis bv evaltree_not_undef intval_logic_negation.cases intval_sub.simps(7,8,9))
    obtain ba avv where aInt: "av = IntVal ba avv"
      by (metis evaltree_not_undef intval_logic_negation.cases intval_sub.simps(3,4,5) subNotUndef
          av)
    then have widthSame: "bb = ba"
      using bInt new_int_bin_def_width_iff subNotUndef by force
    have "val[(av - bv) + bv] = av"
      using aInt av eval_unused_bits_zero widthSame bInt by simp
    then show ?thesis
      by (metis av bv evalDet p(1,3,4))
  qed
  done

(* a little helper lemma for using universal quantified assumptions *)
lemma allE2: "(\<forall>x y. P x y) \<Longrightarrow> (P a b \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma just_goal2: 
  assumes "(\<forall> a b. (val[(a - b) + b] \<noteq> UndefVal \<and> a \<noteq> UndefVal \<longrightarrow>
                    val[(a - b) + b] = a))"
  shows "(exp[(e\<^sub>1 - e\<^sub>2) + e\<^sub>2]) \<ge> e\<^sub>1"
  unfolding le_expr_def unfold_binary bin_eval.simps by (metis assms evalDet evaltree_not_undef)

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

lemma exp_add_right_negate_to_sub:
  shows "exp[x + -y] \<ge> exp[x - y]"
  by (meson dual_order.trans exp_add_commutative exp_add_left_negate_to_sub)

lemma RedundantAddSub_Exp:
  shows "exp[(b + a) - b] \<ge> a"
  apply auto
    subgoal premises p for m p y xa ya
  proof -
    obtain bv where bv: "[m,p] \<turnstile> b \<mapsto> bv"
      using p(1) by auto
    obtain av where av: "[m,p] \<turnstile> a \<mapsto> av"
      using p(4) by auto
    then have addNotUndef: "val[av + bv] \<noteq> UndefVal"
      by (metis bv evalDet intval_add_sym intval_sub.simps(2) p(2,3,4))
    obtain bb bvv where bInt: "bv = IntVal bb bvv"
      by (metis bv evalDet evaltree_not_undef intval_add.simps(3,5) intval_logic_negation.cases
          intval_sub.simps(8) p(1,2,3,5))
    obtain ba avv where aInt: "av = IntVal ba avv"
      by (metis addNotUndef intval_add.simps(2,3,4,5) intval_logic_negation.cases)
    then have widthSame: "bb = ba"
      by (metis addNotUndef bInt intval_add.simps(1))
    have "val[(bv + av) - bv] = val[av]"
      using aInt av eval_unused_bits_zero widthSame bInt by simp
    then show ?thesis
      by (metis av bv evalDet p(1,3,4))
  qed
  done

lemma AddNotExp:
  assumes "stamp_expr n = IntegerStamp b l h"
  assumes "wf_stamp n"
  shows "exp[n + (~n)] \<ge> exp[(const (new_int b (not 0)))]"
  apply auto
  subgoal premises p for m p x xa
  proof -
    have xaDef: "[m,p] \<turnstile> n \<mapsto> xa"
      by (simp add: p)
    then have xaDef2: "[m,p] \<turnstile> n \<mapsto> x"
      by (simp add: p)
    then have xaEq: "xa = x"
      using p by (simp add: evalDet)
    then obtain xv where xv: "xa = new_int b xv"
      by (metis assms eval_int_implies_truncated new_int_truncated_eq valid_int wf_stamp_def xaDef)
    have wfInt: "wf_value (new_int b (not 0))"
      using eval_new_int_wf_value_const xaDef xv by blast
    have toValRHS: "[m,p] \<turnstile> exp[const (new_int b (not 0))] \<mapsto> new_int b (not 0)"
      using wfInt by blast
    have "val[xa + (~xa)] = new_int b (not 0)"
      by (simp add: xv)
    then show ?thesis
      using toValRHS by (simp add: xaEq)
    qed
    done

text \<open>Optimisations\<close>

optimization AddShiftConstantRight: "(const v) + y \<longmapsto> y + (const v) when \<not>(is_ConstantExpr y)"
  using exp_add_commutative by blast

optimization RedundantSubAdd: "(e\<^sub>1 - e\<^sub>2) + e\<^sub>2 \<longmapsto> e\<^sub>1"
  using RedundantSubAdd_Exp by blast

optimization RedundantAddSub: "e\<^sub>2 + (e\<^sub>1 - e\<^sub>2) \<longmapsto> e\<^sub>1"
  apply (simp add: less_SucI size_bin_lhs trans_less_add2)
  using RedundantSubAdd_Exp exp_add_commutative order.trans by blast

optimization AddNeutral: "e + (const (new_int b 0)) \<longmapsto> e
                          when (stamp_expr e = IntegerStamp b lo hi \<and> wf_stamp e)"
  using AddNeutral_Exp by fastforce

optimization AddLeftNegateToSub: "-e + y \<longmapsto> y - e"
  using exp_add_left_negate_to_sub by auto

optimization AddRightNegateToSub: "x + -e \<longmapsto> x - e"
  using less_Suc_eq size_bin_cycle1_lt_succ_sum exp_add_right_negate_to_sub by auto

optimization AddNot: "n + (~n) \<longmapsto> const (new_int b (not 0))
                      when (stamp_expr n = IntegerStamp b l h \<and> wf_stamp n)"
  using AddNotExp by force

optimization AddNot2: "(~n) + n \<longmapsto> const (new_int b (not 0))
                       when (stamp_expr n = IntegerStamp b l h \<and> wf_stamp n)"
  using AddNotExp exp_add_commutative by force

(* ----- Ends here ----- *)

end (* End of AddPhase *)

(* Isabelle Isar Questions:
 Why doesn't subgoal handle \forall and \<longrightarrow> ?
 Then this pattern might become just a single subgoal?
  subgoal premises p1
    apply ((rule allI)+; rule impI)
    subgoal premises p2 for m p v
*)

end (* End of file *)