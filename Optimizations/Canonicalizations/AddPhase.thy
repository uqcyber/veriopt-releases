theory AddPhase
  imports
    Common
    Semantics.IRTreeEvalThms
begin

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

optimization BinaryFoldConstant: "BinaryExpr op (const v1) (const v2) \<mapsto> ConstantExpr (bin_eval op v1 v2)"
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
        unfolding prems x y xy (* get it in form: ConstantExpr c \<mapsto> c *)
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
optimization AddShiftConstantRight: "((const v) + y) \<mapsto> y + (const v) when \<not>(is_ConstantExpr y)"
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

(* take 2 - want to unfold to bin_eval etc... *)
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


optimization AddShiftConstantRight2: "((const v) + y) \<mapsto> y + (const v) when \<not>(is_ConstantExpr y)"
  apply unfold_optimization
  unfolding le_expr_def unfold_bin2 unfold_const
  apply auto
  subgoal for m p ya
    apply (rule exI[of _ "ya"])
    by (simp add: intval_add_sym)
  (* termination proof *)
  using size_non_const by fastforce


optimization AddNeutral: "(e + (const (IntVal32 0))) \<mapsto> e"
  apply unfold_optimization
  unfolding le_expr_def unfold_bin2 unfold_const unfold_valid32
   apply (metis bin_eval.simps(1) is_neutral_0)
  using size_non_const by fastforce


ML_val \<open>@{term \<open>x = y\<close>}\<close>

optimization NeutralLeftSub[intval]: "((e\<^sub>1 - e\<^sub>2) + e\<^sub>2) \<mapsto> e\<^sub>1"
    apply unfold_optimization unfolding intval.simps
  using intval_add.simps intval_sub.simps
    apply (metis (no_types, lifting) diff_add_cancel val_to_bool.cases)
  sorry

optimization NeutralRightSub[intval]: " e\<^sub>2 + (e\<^sub>1 - e\<^sub>2) \<mapsto> e\<^sub>1"
  apply unfold_optimization
  using NeutralLeftSub(1) intval_add_sym apply auto[1]
  sorry

optimization AddToSub: "-e + y \<mapsto> y - e"
  apply unfold_optimization
  sorry

print_context
end

print_phases

end