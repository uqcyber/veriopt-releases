theory AddPhase
  imports
    Common
    Semantics.IRTreeEvalThms
begin
(*
lemma eval_not_undef:
  "([m,p] \<turnstile> e \<mapsto> v) \<longrightarrow> v \<noteq> UndefVal"
  by (induction e; auto)
*)
section \<open>Typing Properties for Integer Values\<close>

text \<open>We use three simple typing properties on integer values: 
   is_IntVal32, is_IntVal64 and the more general is_IntVal.\<close>

definition is_IntVal :: "Value \<Rightarrow> bool" where
  "is_IntVal v = (is_IntVal32 v \<or> is_IntVal64 v)"

lemma unary_eval_int:
  assumes def: "unary_eval op x \<noteq> UndefVal"
  shows "is_IntVal (unary_eval op x)"
  apply (cases op; cases x)
  unfolding is_IntVal_def using def by auto

lemma bin_eval_int:
  assumes def: "bin_eval op x y \<noteq> UndefVal"
  shows "is_IntVal (bin_eval op x y)"
  apply (cases op; cases x; cases y)  (* 300 cases! *)
  unfolding is_IntVal_def using def apply auto (* prove the 294 easy cases *)
  by (metis (full_types) bool_to_val.simps is_IntVal32_def)+

lemma int_stamp32:
  assumes i: "is_IntVal32 v"
  shows "is_IntegerStamp (constantAsStamp v)"
  using i unfolding is_IntegerStamp_def is_IntVal32_def by auto

lemma int_stamp64:
  assumes i: "is_IntVal64 v"
  shows "is_IntegerStamp (constantAsStamp v)"
  using i unfolding is_IntegerStamp_def is_IntVal64_def by auto

lemma int_stamp_both:
  assumes i: "is_IntVal v"
  shows "is_IntegerStamp (constantAsStamp v)"
  using i unfolding is_IntVal_def is_IntegerStamp_def
  using int_stamp32 int_stamp64 is_IntegerStamp_def by auto 

lemma validDefIntConst:
  assumes "v \<noteq> UndefVal"
  assumes "is_IntegerStamp (constantAsStamp v)"
  shows "valid_value v (constantAsStamp v)"
  using assms by (cases v; auto)

lemma validIntConst:
  assumes i: "is_IntVal v"
  shows "valid_value v (constantAsStamp v)"
  using i int_stamp_both is_IntVal_def validDefIntConst by auto 


section \<open>Optimizations for Add Nodes\<close>

phase SnipPhase 
  terminating size
begin

optimization BinaryFoldConstant: "BinaryExpr op (const v1) (const v2) \<longmapsto> ConstantExpr (bin_eval op v1 v2)"
   apply unfold_optimization
   defer apply (cases op; simp)
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


thm BinaryFoldConstant(1)
thm BinaryFoldConstant(2)
thm BinaryFoldConstant
value "BinaryFoldConstant_code (ConstantExpr (IntVal32 0))"

lemma size_pos[simp]: "0 < size y"
  apply (induction y; auto?)
  subgoal premises prems for op a b
    using prems by (induction op; auto)
  done

lemma size_non_add: "op \<noteq> BinAdd \<Longrightarrow> size (BinaryExpr op a b) = size a + size b"
  by (induction op; auto)

lemma size_non_const:
  "\<not> is_ConstantExpr y \<Longrightarrow> 1 < size y"
  using size_pos apply (induction y; auto)
  subgoal premises prems for op a b
    apply (cases "op = BinAdd")
    using size_non_add size_pos apply auto
    by (simp add: Suc_lessI one_is_add)+
  done         

lemma binadd_commute:
  assumes "bin_eval BinAdd x y \<noteq> UndefVal"
  shows "bin_eval BinAdd x y = bin_eval BinAdd y x"
  using assms intval_add_sym by simp


(* horrible backward proof - needs improving *)
optimization AddShiftConstantRight: "((const v) + y) \<longmapsto> y + (const v) when \<not>(is_ConstantExpr y)"
  apply unfold_optimization
   defer using size_non_const apply fastforce
  print_facts
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

subsection \<open>Take 2: Unfold eval quadruples down to bin-eval level\<close>

lemma unfold_bin:
  assumes ok: "val \<noteq> UndefVal"
  shows "([m,p] \<turnstile> BinaryExpr op xe ye \<mapsto> val) = (\<exists> x y.
          (([m,p] \<turnstile> xe \<mapsto> x) \<and>
           ([m,p] \<turnstile> ye \<mapsto> y) \<and>
           (val = bin_eval op x y)
        ))" (is "?L = ?R")  (* (\<exists> x y. (?R1 \<and> ?R2 \<and> ?R3))" *)
  apply (unfold iff_conv_conj_imp; rule conjI; rule impI)
proof (goal_cases)
  case 1
  assume 3: ?L
  show ?R by (rule evaltree.cases[OF 3]; blast+)
next
  case 2
  assume ?R
  then obtain x y where "[m,p] \<turnstile> xe \<mapsto> x" and "[m,p] \<turnstile> ye \<mapsto> y" and "val = bin_eval op x y"
    by auto
  then show ?L
    using ok by (rule BinaryExpr)
qed

lemma unfold_const:
  shows "([m,p] \<turnstile> ConstantExpr c \<mapsto> v) = (valid_value v (constantAsStamp c) \<and> c = v)"
  by blast 

lemma unfold_valid32 [simp]:
  "valid_value y (constantAsStamp (IntVal32 v)) = (y = IntVal32 v)"
  by (induction y; auto dest: signed_word_eqI)

lemma unfold_valid64 [simp]:
  "valid_value y (constantAsStamp (IntVal64 v)) = (y = IntVal64 v)"
  by (induction y; auto dest: signed_word_eqI)


lemma unfold_bin2:
  shows "([m,p] \<turnstile> BinaryExpr op xe ye \<mapsto> val) = (\<exists> x y.
          (([m,p] \<turnstile> xe \<mapsto> x) \<and>
           ([m,p] \<turnstile> ye \<mapsto> y) \<and>
           (val = bin_eval op x y) \<and>
           (val \<noteq> UndefVal)
        ))" (is "?L = ?R")  (* (\<exists> x y. (?R1 \<and> ?R2 \<and> ?R3))" *)
  apply (unfold iff_conv_conj_imp; rule conjI; rule impI)
proof (goal_cases)
  case 1
  assume 3: ?L
  show ?R by (rule evaltree.cases[OF 3]; blast+)
next
  case 2
  assume ?R
  then obtain x y where "[m,p] \<turnstile> xe \<mapsto> x"
        and "[m,p] \<turnstile> ye \<mapsto> y"
        and "val = bin_eval op x y"
        and "val \<noteq> UndefVal"
    by auto
  then show ?L
     by (rule BinaryExpr)
qed


optimization AddShiftConstantRight2: "((const v) + y) \<longmapsto> y + (const v) when \<not>(is_ConstantExpr y)"
  apply unfold_optimization
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
   apply unfold_optimization
  unfolding le_expr_def apply auto
  unfolding is_neutral_0 apply auto
  done


ML_val \<open>@{term \<open>x = y\<close>}\<close>

optimization NeutralLeftSub[intval]: "((e\<^sub>1 - e\<^sub>2) + e\<^sub>2) \<longmapsto> e\<^sub>1"
    apply unfold_optimization unfolding intval.simps
(* NOTE: this unfolds to three goals, but the first one assumes e1 e2 are values?
 1. intval_add (intval_sub e\<^sub>1 e\<^sub>2) e\<^sub>2 \<noteq> UndefVal \<and>
    e\<^sub>1 \<noteq> UndefVal \<longrightarrow>
    intval_add (intval_sub e\<^sub>1 e\<^sub>2) e\<^sub>2 = e\<^sub>1
 2. intval_add (intval_sub e\<^sub>1 e\<^sub>2) e\<^sub>2 \<noteq> UndefVal \<and>
    e\<^sub>1 \<noteq> UndefVal \<longrightarrow>
    intval_add (intval_sub e\<^sub>1 e\<^sub>2) e\<^sub>2 = e\<^sub>1 \<Longrightarrow>
    BinaryExpr BinAdd (BinaryExpr BinSub e\<^sub>1 e\<^sub>2) e\<^sub>2 \<sqsupseteq> e\<^sub>1
 3. Common.size e\<^sub>1
    < Common.size
       (BinaryExpr BinAdd (BinaryExpr BinSub e\<^sub>1 e\<^sub>2) e\<^sub>2)
*)
   using intval_add.simps intval_sub.simps
    apply (metis (no_types, lifting) diff_add_cancel val_to_bool.cases)
  unfolding le_expr_def unfold_bin2 unfold_const unfold_valid32
  subgoal premises p1
    unfolding bin_eval.simps
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
(* without unfold_bin2: but can this be done better?  *)
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
  
(* using unfold_bin2:
  unfolding le_expr_def unfold_bin2 
  apply simp
  by (metis 1 evalDet evaltree_not_undef) 
*)

optimization NeutralRightSub[intval]: " e\<^sub>2 + (e\<^sub>1 - e\<^sub>2) \<longmapsto> e\<^sub>1"
  apply unfold_optimization
  using NeutralLeftSub(1) intval_add_sym apply auto[1]
  sorry

optimization AddToSub: "-e + y \<longmapsto> y - e"
  apply unfold_optimization
  sorry

print_context
end

print_phases

end