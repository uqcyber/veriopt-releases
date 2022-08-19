theory AbsPhase
  imports
    Common
(*
    Optimizations.CanonicalizationTreeProofs
    Optimizations.CanonicalizationTree
    Semantics.IRTreeEvalThms*)
begin

section \<open>Optimizations for Abs Nodes\<close>

phase AbsPhase
  terminating size
begin


(* Marks' lemmas *)

lemma abs_pos:
  fixes v :: "('a :: len word)"
  assumes "0 \<le>s v"
  shows "(if v <s 0 then - v else v) = v"
  by (simp add: assms signed.leD)

lemma abs_neg:
  fixes v :: "('a :: len word)"
  assumes "v <s 0"
  assumes "-(2 ^ (Word.size_word_inst.size_word v - 1)) <s v" (* changed size func used*)
  shows "(if v <s 0 then - v else v) = - v \<and> 0 <s -v"
  by (smt (verit, ccfv_SIG) assms(1) assms(2) signed_take_bit_int_greater_eq_minus_exp 
     signed_take_bit_int_greater_eq_self_iff sint_0 sint_word_ariths(4) word_sless_alt)
 
lemma abs_max_neg:
  fixes v :: "('a :: len word)"
  assumes "v <s 0"
  assumes "- (2 ^ (Word.size_word_inst.size_word v - 1)) = v" (* changed size func used *)
  shows "-v = v"
  by (metis One_nat_def add.inverse_neutral assms(2) double_eq_zero_iff mult_minus_right 
            wsst_TYs(3))


lemma final_abs:
  fixes v :: "('a :: len word)"
  assumes "- (2 ^ (Word.size_word_inst.size_word v - 1)) \<noteq> v" (* changed size func used *)
  shows "0 \<le>s (if v <s 0 then -v else v)"
 
proof (cases "v <s 0")
  case True
  then show ?thesis
  proof (cases "v = - (2 ^ (Word.size_word_inst.size_word v - 1))") (* changed size func used *)
    case True
    then show ?thesis using abs_max_neg
      using assms by presburger
  next
    case False
    then have "- (2 ^ (Word.size_word_inst.size_word v - 1)) <s v" (* changed size func used *)
      by (smt (verit, best) One_nat_def diff_less double_eq_zero_iff len_gt_0 lessI linorder_not_le
          mult_minus_right neg_equal_0_iff_equal order_le_less 
          signed_take_bit_int_greater_eq_self_iff signed_take_bit_int_greater_self_iff 
          signed_word_eqI sint_0 sint_range_size sint_word_ariths(4) unsigned_0 word_2p_lem 
          word_sless_alt wsst_TYs(3))
    then show ?thesis
      using abs_neg abs_pos signed.nless_le by auto
  qed
next
  case False
  then show ?thesis using abs_pos by auto
qed 

(* end *)

lemma wf_abs: "(is_IntVal32 x \<or> is_IntVal64 x) \<Longrightarrow> intval_abs x \<noteq> UndefVal"
  by (metis Value.disc(1) Value.disc(6) intval_abs.simps(1) intval_abs.simps(2) is_IntVal32_def 
      is_IntVal64_def)

fun bin_abs :: "'a ::len word \<Rightarrow> 'a ::len word" where
  "bin_abs v = (if (v <s 0) then (- v) else v)"


(* Helpers - Value level *)
(* 32 *)
lemma val_abs_zero_32:
  "intval_abs (IntVal32 0) = IntVal32 0"
  by simp

lemma val_abs_pos_32:
  assumes "is_IntVal32 x \<and> val_to_bool(val[(IntVal32 0) < x])"
  shows "intval_abs x = x" 
  using assms apply (cases x; auto)
  by (metis bool_to_val.elims signed.less_asym val_to_bool.simps(1))

lemma val_abs_neg_32:
  assumes "is_IntVal32 x \<and> val_to_bool(val[x < (IntVal32 0)])"
  shows "intval_abs x = intval_negate x" 
   using assms 
  by (cases x; auto)
  

(* 64 *)
lemma abs_zero_64:
  "intval_abs (IntVal64 0) = IntVal64 0"
  by simp

lemma val_abs_pos_64:
  assumes "is_IntVal64 x \<and> val_to_bool(val[(IntVal64 0) < x])"
  shows "intval_abs x = x" 
  using assms apply (cases x; auto)
  by (metis bool_to_val.elims signed.less_asym val_to_bool.simps(1))

lemma val_abs_neg_64:
  assumes "is_IntVal64 x \<and> val_to_bool(val[x < (IntVal64 0)])"
  shows "intval_abs x = intval_negate x" 
   using assms 
  by (cases x; auto)


(* Value level proofs *)
lemma val_abs_idem:
  assumes "x \<noteq> UndefVal \<and> intval_abs x \<noteq> UndefVal \<and> intval_abs(intval_abs(x)) \<noteq> UndefVal"
  shows "intval_abs(intval_abs(x)) = intval_abs x"
   using assms apply (cases x; auto)
   using final_abs using abs_max_neg 
  by fastforce+
  

lemma val_abs_negate:
  assumes "x \<noteq> UndefVal \<and> intval_negate x \<noteq> UndefVal \<and> intval_abs(intval_negate x) \<noteq> UndefVal"
  shows "intval_abs (intval_negate x) = intval_abs x"
  using assms apply (cases x; auto) 
  using final_abs abs_max_neg apply fastforce defer 
  using final_abs abs_max_neg apply fastforce
  using final_abs abs_max_neg abs_pos abs_neg val_abs_neg_64 val_abs_neg_32 wf_abs
  sorry


(* Optimisations *)
optimization abs_idempotence: "abs(abs(x)) \<longmapsto>  abs(x)"
   apply auto 
  by (metis UnaryExpr intval_abs.simps(3) unary_eval.simps(1) val_abs_idem)

(* Need to prove val_abs_negate *)
optimization abs_negate: "(abs(-x)) \<longmapsto>  abs(x)"
    apply auto
  by (metis UnaryExpr intval_negate.simps(3) unary_eval.simps(1) val_abs_negate)

end (* End of AbsPhase *)

end (* End of file *)