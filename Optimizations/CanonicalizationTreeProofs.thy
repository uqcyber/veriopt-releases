section \<open>Canonicalization Phase\<close>

theory CanonicalizationTreeProofs
  imports
    CanonicalizationTree
    Semantics.IRTreeEvalThms
begin

lemma mul_rewrite_helper:
  shows "valid_value (IntegerStamp 32 lo hi) x \<Longrightarrow> intval_mul x (IntVal32 (-1)) = intval_negate x" 
  and "valid_value (IntegerStamp 64 lo hi) x \<Longrightarrow> intval_mul x (IntVal64 (-1)) = intval_negate x" 
  using valid32or64_both  by fastforce+ 

lemma CanonicalizeMulProof:
  assumes "CanonicalizeMul before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeMul.induct)
  case (mul_negate32 y x lo hi)
  then show ?case 
    using ConstantExprE BinaryExprE bin_eval.simps evalDet mul_rewrite_helper 
      int_stamp_implies_valid_value 
    by (auto; metis)
next
  case (mul_negate64 y x lo hi)
  then show ?case 
    using ConstantExprE BinaryExprE bin_eval.simps evalDet mul_rewrite_helper 
      int_stamp_implies_valid_value
    by (auto; metis)
qed

(* (x - y) + y \<Rightarrow> x *)
(*  x + (y - x) \<Rightarrow> y *)
(* (-x + y) \<Rightarrow> (y - x) *)
(* (x + (-y)) \<Rightarrow> (x - y) *)
lemma add_rewrites_helper:
  assumes "valid_value (IntegerStamp b lox hix) x"
  and     "valid_value (IntegerStamp b loy hiy) y"

  shows "intval_add (intval_sub x y) y = x"
  and   "intval_add x (intval_sub y x) = y"
  and   "intval_add (intval_negate x) y = intval_sub y x" 
  and   "intval_add x (intval_negate y) = intval_sub x y"
  using valid32or64_both assms by fastforce+

lemma CanonicalizeAddProof:
  assumes "CanonicalizeAdd before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeAdd.induct)
  case (add_xsub x a y stampa stampy)
  then show ?case 
    by (metis BinaryExprE Stamp.collapse(1) bin_eval.simps(1) bin_eval.simps(3) 
        evalDet int_stamp_implies_valid_value intval_add_sym add_rewrites_helper(1))
next
  case (add_ysub y a x stampa stampx)
  then show ?case 
    by (metis is_IntegerStamp_def add_ysub.hyps add_ysub.prems evalDet BinaryExprE Stamp.sel(1) 
        bin_eval.simps(1) bin_eval.simps(3) int_stamp_implies_valid_value intval_add_sym add_rewrites_helper(2))
next
  case (add_xnegate nx x stampx stampy y)
  then show ?case 
    by (smt (verit, del_insts) BinaryExprE Stamp.sel(1) UnaryExprE add_rewrites_helper(4) 
        bin_eval.simps(1) bin_eval.simps(3) evalDet int_stamp_implies_valid_value intval_add_sym is_IntegerStamp_def unary_eval.simps(2))
next
  case (add_ynegate ny y stampx x stampy)
  then show ?case 
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE add_rewrites_helper(4) bin_eval.simps(1) 
        bin_eval.simps(3) evalDet int_stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(2))
qed

(* (x + y) - y \<Rightarrow> x *)
(* (x + y) - x \<Rightarrow> y *)
(* (x - y) - x \<Rightarrow> (-y) *)
(* x - (x + y) \<Rightarrow> (-y) *)
(* y - (x + y) \<Rightarrow> (-x) *)
(* x - (x - y) \<Rightarrow> y *)
(* x - (-y) \<Rightarrow> x + y *)
lemma sub_rewrites_helper:
  assumes "valid_value (IntegerStamp b lox hix) x"
  and     "valid_value (IntegerStamp b loy hiy) y"

  shows "intval_sub (intval_add x y) y  = x"
  and   "intval_sub (intval_add x y) x  = y" 
  and   "intval_sub (intval_sub x y) x  = intval_negate y" 
  and   "intval_sub x (intval_add x y)  = intval_negate y"
  and   "intval_sub y (intval_add x y)  = intval_negate x" 
  and   "intval_sub x (intval_sub x y)  = y"
  and   "intval_sub x (intval_negate y) = intval_add x y"
  using valid32or64_both assms by fastforce+

(* x - x \<Rightarrow> 0 *)
(* 0 - x \<Rightarrow> -x *)
lemma sub_single_rewrites_helper:
  assumes "valid_value (IntegerStamp b lox hix) x"
  shows   "b = 32 \<Longrightarrow> intval_sub x x = IntVal32 0" 
  and     "b = 64 \<Longrightarrow> intval_sub x x = IntVal64 0"
  and     "b = 32 \<Longrightarrow> intval_sub (IntVal32 0) x = intval_negate x" 
  and     "b = 64 \<Longrightarrow> intval_sub (IntVal64 0) x = intval_negate x"
  using valid32or64_both assms by fastforce+

lemma CanonicalizeSubProof:
  assumes "CanonicalizeSub before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeSub.induct)
  case (sub_same32 stampx x lo hi)
  show ?case     
    using ConstantExprE BinaryExprE  bin_eval.simps evalDet sub_same32.prems sub_single_rewrites_helper 
      int_stamp_implies_valid_value sub_same32.hyps(1) sub_same32.hyps(2)
    by (auto; metis)
next
  case (sub_same64 stampx x lo hi)
  show ?case     
    using ConstantExprE BinaryExprE  bin_eval.simps evalDet sub_same64.prems sub_single_rewrites_helper 
      int_stamp_implies_valid_value sub_same64.hyps(1) sub_same64.hyps(2)
    by (auto; metis)
next
  case (sub_left_add1 x a b stampa stampb)
  then show ?case
    by (metis BinaryExprE Stamp.collapse(1) bin_eval.simps(1) bin_eval.simps(3) evalDet 
        int_stamp_implies_valid_value sub_rewrites_helper(1))
next
  case (sub_left_add2 x a b stampa stampb)
  then show ?case
    by (metis BinaryExprE Stamp.collapse(1) bin_eval.simps(1) bin_eval.simps(3) evalDet 
        int_stamp_implies_valid_value sub_rewrites_helper(2))
next
  case (sub_left_sub x a b stampa stampb)
  then show ?case
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(3) evalDet
        int_stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(3) unary_eval.simps(2))
next
  case (sub_right_add1 y a b stampa stampb)
  then show ?case
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(1) bin_eval.simps(3) evalDet
        int_stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(4) unary_eval.simps(2))
next
  case (sub_right_add2 y a b stampa stampb)
  then show ?case
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(1) bin_eval.simps(3) evalDet
        int_stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(5) unary_eval.simps(2))
next
  case (sub_right_sub y a b stampa stampb)
  then show ?case
    by (metis BinaryExprE Stamp.sel(1) bin_eval.simps(3) evalDet
        int_stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(6))
next
  case (sub_xzero32 stampx x lo hi)
  then show ?case     
    using ConstantExprE BinaryExprE  bin_eval.simps evalDet sub_xzero32.prems sub_single_rewrites_helper 
      int_stamp_implies_valid_value sub_xzero32.hyps(1) sub_xzero32.hyps(2)
    by (auto; metis)
next
  case (sub_xzero64 stampx x lo hi)
  then show ?case     
    using ConstantExprE BinaryExprE  bin_eval.simps evalDet sub_xzero64.prems sub_single_rewrites_helper 
      int_stamp_implies_valid_value sub_xzero64.hyps(1) sub_xzero64.hyps(2)
    by (auto; metis)
next
  case (sub_y_negate nb b stampa a stampb)
  then show ?case
    by (smt (verit, best) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(1) bin_eval.simps(3) evalDet
        int_stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(7) unary_eval.simps(2))
qed

(* -(x-y) = (x-y) *)
lemma negate_xsuby_helper:
  assumes "valid_value (IntegerStamp b lox hix) x"
  and "valid_value (IntegerStamp b loy hiy) y"
  shows "intval_negate (intval_sub x y) = intval_sub y x"
  using valid32or64_both assms by fastforce
(* -(-x) = x *)
lemma negate_negate_helper:
  assumes "valid_value (IntegerStamp b lox hix) x"
  shows "intval_negate (intval_negate x) = x" 
  using valid32or64 assms by fastforce

lemma CanonicalizeNegateProof:
  assumes "CanonicalizeNegate before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeNegate.induct)
  case (negate_negate nx x)
  thus ?case 
    by (metis UnaryExprE evalDet int_stamp_implies_valid_value is_IntegerStamp_def negate_negate_helper unary_eval.simps(2))
next
  case (negate_sub e x y stampx stampy)
  thus ?case
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(3) evalDet int_stamp_implies_valid_value
        is_IntegerStamp_def negate_xsuby_helper unary_eval.simps(2))
qed

(* TODO: move to values? and prove it somehow :\ *)
lemma abs_helper:
  assumes "\<exists> v1. x = IntVal32 (v1)"
  shows "v1 <s 0 \<Longrightarrow> intval_abs x = IntVal32 (-v1)" 
  and   "\<not>(v1 <s 0) \<Longrightarrow> intval_abs x = IntVal32 (v1)" 
  using assms
  sorry
lemma abs_helper2:
  assumes "\<exists> v1. x = IntVal64 (v1)"
  shows "v1 <s 0 \<Longrightarrow> intval_abs x = IntVal64 (-v1)" 
  and   "\<not>(v1 <s 0) \<Longrightarrow> intval_abs x = IntVal64 (v1)" 
  using assms
  sorry

(* abs(-x) = abs(x) *)
(* abs(abs(x)) = abs(x) *)
lemma abs_rewrite_helper:
  assumes "valid_value (IntegerStamp b lox hix) x"
  shows "intval_abs (intval_negate x) = intval_abs x"
  and "intval_abs (intval_abs x) = intval_abs x"
  apply (metis (no_types, hide_lams) valid32or64 assms abs_helper abs_helper2
      intval_negate.simps(1) intval_negate.simps(2))
  by (metis valid32or64 assms abs_helper abs_helper2)

lemma CanonicalizeAbsProof:
  assumes "CanonicalizeAbs before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeAbs.induct)
  case (abs_abs ax x)
  then show ?case
    by (metis UnaryExprE abs_rewrite_helper(2) evalDet int_stamp_implies_valid_value is_IntegerStamp_def
        unary_eval.simps(1))
next
  case (abs_neg nx x)
  then show ?case
    by (metis UnaryExprE abs_rewrite_helper(1) evalDet int_stamp_implies_valid_value is_IntegerStamp_def
        unary_eval.simps(1) unary_eval.simps(2))
qed

(* ~(~x) = x *)
lemma not_rewrite_helper:
  assumes "valid_value (IntegerStamp b lox hix) x"
  shows "intval_not (intval_not x) = x"
  using valid32or64 assms by fastforce+

lemma CanonicalizeNotProof:
  assumes "CanonicalizeNot before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeNot.induct)
  case (not_not nx x)
  then show ?case
    by (metis UnaryExprE evalDet is_IntegerStamp_def not_rewrite_helper
        int_stamp_implies_valid_value unary_eval.simps(3))
qed

lemma demorgans_rewrites_helper:
  assumes "valid_value (IntegerStamp b lox hix) x"
  and     "valid_value (IntegerStamp b loy hiy) y"

  shows "intval_and (intval_not x) (intval_not y) = intval_not (intval_or x y)"
  and   "intval_or (intval_not x) (intval_not y) = intval_not (intval_and x y)"
  and   "x = y \<Longrightarrow> intval_and x y = x"
  and   "x = y \<Longrightarrow> intval_or x y = x"
  using valid32or64_both assms by fastforce+

lemma CanonicalizeAndProof:
  assumes "CanonicalizeAnd before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeAnd.induct)
  case (and_same x)
  then show ?case
    by (metis BinaryExprE bin_eval.simps(4) demorgans_rewrites_helper(3) evalDet
        int_stamp_implies_valid_value is_IntegerStamp_def)
next
  case (and_demorgans nx x ny y stampx stampy)
  then show ?case
    by (smt (z3) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(4) bin_eval.simps(5) 
        demorgans_rewrites_helper(1) evalDet int_stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(3))
qed

lemma CanonicalizeOrProof:
  assumes "CanonicalizeOr before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeOr.induct)
  case (or_same x)
  then show ?case
    by (metis BinaryExprE bin_eval.simps(5) demorgans_rewrites_helper(4) evalDet
        int_stamp_implies_valid_value is_IntegerStamp_def)
next
  case (or_demorgans nx x ny y stampx stampy)
  then show ?case
    by (smt (z3) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(4) bin_eval.simps(5) demorgans_rewrites_helper(2)
        evalDet int_stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(3))
qed

lemma CanonicalizeConditionalProof:
  assumes "CanonicalizeConditional before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeConditional.induct)
case (eq_branches t f c)
  then show ?case using evalDet by auto
next
  case (cond_eq c x y stampx stampy)
  then show ?case using evalDet sorry
next
  case (condition_bounds_x c x y stamp_x stamp_y)
  then show ?case sorry
next
  case (condition_bounds_y c x y stamp_x stamp_y)
  then show ?case sorry
next
  case (negate_condition nc c stampc lo hi x y)
  then show ?case sorry
next
  case (const_true c val t f)
  then show ?case using evalDet by auto
next
  case (const_false c val t f)
  then show ?case using evalDet by auto
qed

end