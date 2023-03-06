theory TacticSolving
  imports Common
begin

fun size :: "IRExpr \<Rightarrow> nat" where
  "size (UnaryExpr op e) = (size e) * 2" |
  "size (BinaryExpr BinAdd x y) = (size x) + ((size y) * 2)" |
  "size (BinaryExpr op x y) = (size x) + (size y)" |
  "size (ConditionalExpr cond t f) = (size cond) + (size t) + (size f) + 2" |
  "size (ConstantExpr c) = 1" |
  "size (ParameterExpr ind s) = 2" |
  "size (LeafExpr nid s) = 2" |
  "size (ConstantVar c) = 2" |
  "size (VariableExpr x s) = 2"

lemma size_pos[simp]: "0 < size y"
  apply (induction y; auto?)
  subgoal premises prems for op a b
    using prems by (induction op; auto)
  done

phase TacticSolving
  terminating size
begin

subsection \<open>AddNode\<close>
(*lemma val_add_left_negate_to_sub:
  "val[-x + y] \<approx> val[y - x]"
  apply simp by (cases x; cases y; auto)

lemma exp_add_left_negate_to_sub:
  "exp[-x + y] \<ge> exp[y - x]"
  using val_add_left_negate_to_sub by auto*)

lemma value_approx_implies_refinement:
  assumes "lhs \<approx> rhs"
  assumes "\<forall>m p v. ([m, p] \<turnstile> elhs \<mapsto> v) \<longrightarrow> v = lhs"
  assumes "\<forall>m p v. ([m, p] \<turnstile> erhs \<mapsto> v) \<longrightarrow> v = rhs"
  assumes "\<forall>m p v1 v2. ([m, p] \<turnstile> elhs \<mapsto> v1) \<longrightarrow> ([m, p] \<turnstile> erhs \<mapsto> v2)"
  shows "elhs \<ge> erhs"
  by (metis assms(4) le_expr_def evaltree_not_undef)

method explore_cases for x y :: Value =
  (cases x; cases y; auto)

method explore_cases_bin for x :: IRExpr =
  (cases x; auto)

method obtain_approx_eq for lhs rhs x y :: Value =
  (rule meta_mp[where P="lhs \<approx> rhs"], defer_tac, explore_cases x y)

method obtain_eval for exp::IRExpr and val::Value =
  (rule meta_mp[where P="\<And>m p v. ([m, p] \<turnstile> exp \<mapsto> v) \<Longrightarrow> v = val"], defer_tac)

method solve for lhs rhs x y :: Value =
  (match conclusion in "size _ < size _" \<Rightarrow> \<open>simp\<close>)?,
  (match conclusion in "(elhs::IRExpr) \<ge> (erhs::IRExpr)" for elhs erhs \<Rightarrow> \<open>
    (obtain_approx_eq lhs rhs x y)?\<close>)

print_methods
(*
    (simp del: well_formed_equal_def le_expr_def)?;
    ((rule allI)+)?\<close>)*)
thm BinaryExprE
optimization opt_add_left_negate_to_sub:
  "-x + y \<longmapsto> y - x"
  (*defer apply simp apply (rule allI)+ apply (rule impI)
   apply (subgoal_tac "\<forall>x1. [m, p] \<turnstile> exp[-x + y] \<mapsto> x1") defer
  *)
   apply (solve "val[-x1 + y1]" "val[y1 - x1]" x1 y1)
  apply simp apply auto using evaltree_not_undef sorry
(*
  apply (obtain_eval "exp[-x + y]" "val[-x1 + y1]")
  

  apply (rule BinaryExprE)
  apply (rule allI)+ sorry
  apply (auto simp: unfold_evaltree) sorry*)
  (*
   defer apply (test "val[-x1 + y1]" "val[y1 - x1]" x1 y1)
   apply (rule meta_mp[where P="val[-x1 + y1] \<approx> val[y1 - x1]"])
    prefer 2 apply (cases x1; cases y1; auto)
   apply (subgoal_tac "val[-x1 + y1] \<approx> val[y1 - x1]")
    apply (cases x1; cases y1; auto)
  using exp_add_left_negate_to_sub apply simp
  unfolding size.simps by simp*)

subsection \<open>NegateNode\<close>

lemma val_distribute_sub: 
 "val[-(x-y)] \<approx> val[y-x]" 
  by (cases x; cases y; auto) 

optimization distribute_sub: "-(x-y) \<longmapsto> (y-x)" 
  using val_distribute_sub unfold_binary unfold_unary by auto

lemma val_xor_self_is_false:
  assumes "x = IntVal 32 v"
  shows "val[x \<oplus> x] \<approx> val[false]"
  by (cases x; auto simp: assms)

definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

lemma exp_xor_self_is_false: 
  assumes "stamp_expr x = IntegerStamp 32 l h"
  assumes "wf_stamp x"
  shows "exp[x \<oplus> x] >= exp[false]"
  by (smt (z3) wf_value_def bin_eval.simps(6) bin_eval_new_int constantAsStamp.simps(1) evalDet 
      int_signed_value_bounds new_int.simps new_int_take_bits unfold_binary unfold_const valid_int 
      valid_stamp.simps(1) valid_value.simps(1) well_formed_equal_defn val_xor_self_is_false 
      le_expr_def assms wf_stamp_def)

lemma val_or_commute[simp]:
   "val[x | y] = val[y | x]"
  by (cases x; cases y; auto simp: or.commute)

lemma val_xor_commute[simp]:
   "val[x \<oplus> y] = val[y \<oplus> x]"
  by (cases x; cases y; auto simp: word_bw_comms(3))

lemma val_and_commute[simp]:
   "val[x & y] = val[y & x]"
  by (cases x; cases y; auto simp: word_bw_comms(1))

lemma exp_or_commutative:
  "exp[x | y] \<ge> exp[y | x]"
  by auto 

lemma exp_xor_commutative:
  "exp[x \<oplus> y] \<ge> exp[y \<oplus> x]"
  by auto 

lemma exp_and_commutative:
  "exp[x & y] \<ge> exp[y & x]"
  by auto 

(* 32-bit proofs of new optimisations *)
lemma OrInverseVal:
  assumes "n = IntVal 32 v"
  shows "val[n | ~n] \<approx> new_int 32 (-1)"
  apply (auto simp: assms)
  by (metis bit.disj_cancel_right mask_eq_take_bit_minus_one take_bit_or)

optimization OrInverse: "exp[n | ~n] \<longmapsto> (const (new_int 32 (not 0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
   apply (auto simp: Suc_lessI)
  by (smt (verit) wf_value_def constantAsStamp.simps(1) evalDet int_signed_value_bounds unfold_const
      mask_eq_take_bit_minus_one new_int.elims new_int_take_bits valid_int well_formed_equal_defn
      valid_stamp.simps(1) valid_value.simps(1) OrInverseVal wf_stamp_def size.simps)

optimization OrInverse2: "exp[~n | n] \<longmapsto> (const (new_int 32 (not 0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
   using OrInverse exp_or_commutative by auto

lemma XorInverseVal:
  assumes "n = IntVal 32 v"
  shows "val[n \<oplus> ~n] \<approx> new_int 32 (-1)"
  apply (auto simp: assms)
  by (metis (no_types, opaque_lifting) bit.compl_zero bit.xor_compl_right bit.xor_self take_bit_xor
      mask_eq_take_bit_minus_one)

optimization XorInverse: "exp[n \<oplus> ~n] \<longmapsto> (const (new_int 32 (not 0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
  apply (auto simp: Suc_lessI)
  by (smt (verit) wf_value_def constantAsStamp.simps(1) evalDet int_signed_value_bounds size.simps
      intval_xor.elims mask_eq_take_bit_minus_one new_int.elims new_int_take_bits unfold_const 
      valid_stamp.simps(1) valid_value.simps(1) well_formed_equal_defn wf_stamp_def XorInverseVal)

optimization XorInverse2: "exp[(~n) \<oplus> n] \<longmapsto> (const (new_int 32 (not 0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
   using XorInverse exp_xor_commutative by auto

(* --- New optimisations --- *)
lemma AndSelfVal:
  assumes "n = IntVal 32 v"
  shows "val[~n & n] = new_int 32 0"
  apply (auto simp: assms) 
  by (metis take_bit_and take_bit_of_0 word_and_not)

optimization AndSelf: "exp[(~n) & n] \<longmapsto> (const (new_int 32 (0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
  apply (auto simp: Suc_lessI) unfolding size.simps
  by (metis (no_types) val_and_commute ConstantExpr IntVal0 Value.inject(1) evalDet wf_stamp_def
      eval_bits_1_64 new_int.simps validDefIntConst valid_int wf_value_def AndSelfVal)

optimization AndSelf2: "exp[n & (~n)] \<longmapsto> (const (new_int 32 (0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
  using AndSelf exp_and_commutative by auto

lemma NotXorToXorVal:
  assumes "x = IntVal 32 xv"
  assumes "y = IntVal 32 yv"
  shows "val[(~x) \<oplus> (~y)] = val[x \<oplus> y]" 
  apply (auto simp: assms) 
  by (metis (no_types, opaque_lifting) bit.xor_compl_left bit.xor_compl_right take_bit_xor 
      word_not_not) 

lemma NotXorToXorExp:
  assumes "stamp_expr x = IntegerStamp 32 lx hx"
  assumes "wf_stamp x"
  assumes "stamp_expr y = IntegerStamp 32 ly hy"
  assumes "wf_stamp y"
  shows "exp[(~x) \<oplus> (~y)] \<ge> exp[x \<oplus> y]" 
  apply auto 
  subgoal premises p for m p xa xb
    proof -
      obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
        using p by blast
      obtain xb where xb: "[m,p] \<turnstile> y \<mapsto> xb"
        using p by blast
      have toVal: "[m,p] \<turnstile> exp[x \<oplus> y] \<mapsto> val[xa \<oplus> xb]"
        by (smt (verit) NotXorToXorVal evalDet p(1,2,4) valid_int wf_stamp_def xa bin_eval.simps(6)
            evaltree.BinaryExpr xb assms)
      then have a: "val[(~xa) \<oplus> (~xb)] = val[xa \<oplus> xb]" 
        by (metis assms valid_int wf_stamp_def xa xb NotXorToXorVal)
      then show ?thesis
        by (metis a evalDet p(2,4) toVal xa xb)
    qed 
  done

optimization NotXorToXor: "exp[(~x) \<oplus> (~y)] \<longmapsto> (x \<oplus> y)
                        when (stamp_expr x = IntegerStamp 32 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 32 ly hy \<and> wf_stamp y)"
  using NotXorToXorExp by auto

(* Proving new optimisations *)
(* Add
   x + ~x \<mapsto> -1 
*)

lemma constEvalIsConst: 
  assumes "wf_value n"
  shows "[m,p] \<turnstile> exp[(const (n))] \<mapsto> n"  
  by (simp add: assms IRTreeEval.evaltree.ConstantExpr)

lemma ExpAddCommute:
  "exp[x + y] \<ge> exp[y + x]"
  by (auto simp add: Values.intval_add_sym)

lemma AddNotVal:
  assumes "n = IntVal bv v"
  shows "val[n + (~n)] = new_int bv (not 0)"
  by (auto simp: assms)

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
    then have "xa = x" 
      using p by (simp add: evalDet)
    then obtain xv where xv: "xa = IntVal b xv"
      by (metis valid_int wf_stamp_def xaDef2 assms)
    have toVal: "[m,p] \<turnstile> exp[n + (~n)] \<mapsto> val[xa + (~xa)]"
      by (metis UnaryExpr bin_eval.simps(1) evalDet p unary_eval.simps(3) unfold_binary xaDef)
    have wfInt: "wf_value (new_int b (not 0))"
      using validDefIntConst xaDef by (simp add: eval_bits_1_64 xv wf_value_def) 
    have toValRHS: "[m,p] \<turnstile> exp[(const (new_int b (not 0)))] \<mapsto> new_int b (not 0)"
      using wfInt by (simp add: constEvalIsConst)
    have isNeg1: "val[xa + (~xa)] = new_int b (not 0)"
      by (simp add: xv)
    then show ?thesis
      using toValRHS by (simp add: \<open>(xa::Value) = (x::Value)\<close>)
    qed 
    done

optimization AddNot: "exp[n + (~n)] \<longmapsto> (const (new_int b (not 0)))
                        when (stamp_expr n = IntegerStamp b l h \<and> wf_stamp n)"
   apply (simp add: Suc_lessI) using AddNotExp by force

optimization AddNot2: "exp[(~n) + n] \<longmapsto> (const (new_int b (not 0)))
                        when (stamp_expr n = IntegerStamp b l h \<and> wf_stamp n)"
  apply (simp add: Suc_lessI) using AddNot ExpAddCommute by simp

end

end