theory TacticSolving
  imports
    Common
    Proofs.StampEvalThms
begin

(*
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
*)

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
 "val[-(x - y)] \<approx> val[y - x]"
  by (cases x; cases y; auto)

optimization distribute_sub: "-(x - y) \<longmapsto> (y - x)"
  apply (simp add: less_SucI size_bin_lt_succ)
  using val_distribute_sub unfold_binary unfold_unary by auto

lemma val_xor_self_is_false:
  assumes "x = IntVal 32 v"
  shows "val[x \<oplus> x] \<approx> val[false]"
  by (cases x; auto simp: assms)

lemma exp_xor_self_is_false:
  assumes "stamp_expr x = IntegerStamp 32 l h"
  assumes "wf_stamp x"
  shows "exp[x \<oplus> x] \<ge> exp[false]"
  using assms apply auto
  by (metis (no_types, opaque_lifting) ExpIntBecomesIntVal evalDet false_always_evals val_xor_self
      wf_stamp_def)

text \<open>--- New Optimisations ---\<close>

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
      then have "val[(~xa) \<oplus> (~xb)] = val[xa \<oplus> xb]"
        by (metis assms valid_int wf_stamp_def xa xb NotXorToXorVal)
      then show ?thesis
        by (metis BinaryExpr bin_eval.simps(8) evalDet p(1,2,4) xa xb)
    qed
  done

optimization NotXorToXor: "exp[(~x) \<oplus> (~y)] \<longmapsto> (x \<oplus> y)
                           when (stamp_expr x = IntegerStamp 32 lx hx \<and> wf_stamp x) \<and>
                                (stamp_expr y = IntegerStamp 32 ly hy \<and> wf_stamp y)"
  apply (simp add: less_SucI size_bin_cycle1_lt_succ_sum) using NotXorToXorExp by simp

end

context stamp_mask
begin

(* Extension to old Or optimisation 
   x | y \<mapsto> -1 when (downMask x | downMask y == -1)
*)

lemma OrGeneralization:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "stamp_expr exp[x | y] = IntegerStamp b el eh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  assumes "wf_stamp exp[x | y]"
  assumes "(or (\<down>x) (\<down>y)) = not 0"
  shows "exp[x | y] \<ge> exp[(const (new_int b (not 0)))]"
  using assms apply auto
  subgoal premises p for m p xvv yvv
  proof -
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      by (metis p(1,3,9) valid_int wf_stamp_def)
    obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      by (metis p(2,4,10) valid_int wf_stamp_def)
    then have rhsWf: "wf_value (new_int b (not 0))"
      by (metis eval_bits_1_64 new_int.simps new_int_take_bits validDefIntConst wf_value_def)
    then have rhs: "(new_int b (not 0)) = val[IntVal b xv | IntVal b yv]" 
      using assms word_ao_absorbs(1)
      by (metis (no_types, opaque_lifting) bit.de_Morgan_conj word_bw_comms(2) xv down_spec
          word_not_not yv bit.disj_conj_distrib intval_or.simps(1) new_int_bin.simps ucast_id
          or.right_neutral)
    then have "new_int b (not 0) = new_int b (mask b)"
      by auto
    then show ?thesis 
      by (metis neg_one.elims neg_one_value p(9,10) rhsWf unfold_const evalDet xv yv rhs)
    qed
    done
end

phase TacticSolving
  terminating size
begin

(* 
  ~e == e \<mapsto> false
 *)

lemma TakeBitNotSelf:
  assumes "b \<ge> 1"
  shows "(take_bit b (not e) = e) = False"
  by (metis assms takeBitNot take_bit_not_take_bit)

lemma ValNeverEqNotSelf:
  assumes "e = IntVal 32 ev"
  shows "val[(\<not>e) eq e] = val[false]"
  by (simp add: TakeBitNotSelf assms)

lemma ExpNeverNotSelf:
  assumes "stamp_expr x = IntegerStamp 32 xl xh"
  assumes "wf_stamp x"
  shows "exp[(\<not>x) eq x] \<ge> exp[false]"
  using assms apply auto
  subgoal premises p for m p xa xaa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(5) by auto
    then obtain xv where xv: "xa = IntVal 32 xv"
      by (metis p(1,2) valid_int wf_stamp_def)
    then have rhsVal: "[m,p] \<turnstile> exp[false] \<mapsto> val[false]"
      by auto
    then have "val[(\<not>xa) eq xa] = val[false]"
      using ValNeverEqNotSelf by (simp add: xv)
    then show ?thesis
      by (metis bool_to_val.simps(2) evalDet p(3,5) rhsVal xa)
   qed
  done

optimization NeverEqNotSelf: "((\<not>x) eq x) \<longmapsto> false
                              when (stamp_expr x = IntegerStamp 32 xl xh \<and> wf_stamp x)"
  using ExpNeverNotSelf by force

(* 
  (x ^ y) == x \<mapsto> y == 0
  x == (x ^ y) \<mapsto> y == 0 
  (x ^ y) == y \<mapsto> x == 0 
  y == (x ^ y) \<mapsto> x == 0
 *)
lemma BinXorFallThrough:
  shows "bin[(x \<oplus> y) = x] \<longleftrightarrow> bin[y = 0]"
  by (metis xor.assoc xor.left_neutral xor_self_eq)

lemma valNeutral:
  assumes "x = new_int b xv"
  assumes "val[x \<oplus> (new_int b 0)] \<noteq> UndefVal"
  shows "val[x \<oplus> (new_int b 0)] = val[x]"
  using assms by (auto; meson)

lemma ValXorFallThrough:
  assumes "x = new_int b xv"
  assumes "y = new_int b yv"
  shows "val[(x \<oplus> y) eq x] = val[y eq (new_int b 0)]"
  by (simp add: assms BinXorFallThrough)

lemma ExpXorFallThrough:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  shows "exp[(x \<oplus> y) eq x] \<ge> exp[y eq (const (new_int b 0))]"
  using assms apply auto
  subgoal premises p for m p xa xaa ya
  proof -
    obtain b xv where xa: "[m,p] \<turnstile> x \<mapsto> new_int b xv"
      by (metis new_int.simps eval_unused_bits_zero p(1,3,5) wf_stamp_def valid_int)
    obtain yv where ya: "[m,p] \<turnstile> y \<mapsto> new_int b yv"
      by (metis Value.inject(1) wf_stamp_def p(1,2,3,4,8) eval_unused_bits_zero xa new_int.simps
          valid_int)
    then have wfVal: "wf_value (new_int b 0)"
      by (metis eval_bits_1_64 new_int.simps new_int_take_bits validDefIntConst wf_value_def xa)
    then have "[m,p] \<turnstile> exp[y eq (const (new_int b 0))] \<mapsto> val[(xa \<oplus> ya) eq xa]"
      by (metis (no_types, lifting) ValXorFallThrough ConstantExpr bin_eval.simps(13) evalDet xa ya
          p(5,6,7,8) unfold_binary)
    then show ?thesis
      by (metis evalDet new_int.elims p(1,3,5,7) take_bit_of_0 valid_value.simps(1) wf_stamp_def xa)
   qed 
  done

lemma ExpXorFallThrough2:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  shows "exp[(x \<oplus> y) eq y] \<ge> exp[x eq (const (new_int b 0))]"
  by (meson ExpXorFallThrough assms mono_binary order_refl order_trans exp_xor_commutative
      exp_eq_commutative)

optimization XorFallThrough1: "((x \<oplus> y) eq x) \<longmapsto> (y eq (const (new_int b 0)))
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  apply (meson less_trans_Suc not_less_eq size_bin_lhs_succ size_bin_rhs_succ)
  using ExpXorFallThrough by force

optimization XorFallThrough2: "(x eq (x \<oplus> y)) \<longmapsto> (y eq (const (new_int b 0)))
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  using ExpXorFallThrough exp_eq_commutative by force

optimization XorFallThrough3: "((x \<oplus> y) eq y) \<longmapsto> (x eq (const (new_int b 0)))
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  apply (metis Suc_lessI less_trans_Suc size_bin_lhs size_bin_lhs_succ)
  using ExpXorFallThrough2 by force

optimization XorFallThrough4: "(y eq (x \<oplus> y)) \<longmapsto> (x eq (const (new_int b 0)))
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  using ExpXorFallThrough2 exp_eq_commutative by force

end

context stamp_mask
begin

(* Ian's optimisation, and it's Or equivalent
    x & y \<mapsto> x when x.up \<in> y.Down
    x | y \<mapsto> y when x.up \<in> y.Down

    x.up \<in> y.Down means (x.up & y.Down = x.up), 
               equiv to (x.up | y.Down = y.Down)
*)

lemma inEquivalence:
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  shows "(and (\<up>x) yv) = (\<up>x) \<longleftrightarrow> (or (\<up>x) yv) = yv"
  by (metis word_ao_absorbs(3) word_ao_absorbs(4))

lemma inEquivalence2:
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  shows "(and (\<up>x) (\<down>y)) = (\<up>x) \<longleftrightarrow> (or (\<up>x) (\<down>y)) = (\<down>y)"
  by (metis word_ao_absorbs(3) word_ao_absorbs(4))

(* x | y \<mapsto> y when x.up \<in> y.Down *)
lemma RemoveLHSOrMask:
  assumes "(and (\<up>x) (\<down>y)) = (\<up>x)"
  assumes "(or (\<up>x) (\<down>y)) = (\<down>y)"
  shows "exp[x | y] \<ge> exp[y]"
  using assms apply auto
  subgoal premises p for m p v
  proof -
    obtain b ev where exp: "[m, p] \<turnstile> exp[x | y] \<mapsto> IntVal b ev"
      by (metis BinaryExpr bin_eval.simps(7) p(3,4,5) bin_eval_new_int new_int.simps)
    from exp obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      apply (subst (asm) unfold_binary_width) by force+
    from exp obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      apply (subst (asm) unfold_binary_width) by force+
    then have "yv = (or xv yv)"
      using assms yv xv apply auto
      by (metis (no_types, opaque_lifting) down_spec ucast_id up_spec word_ao_absorbs(1) word_or_not
          word_ao_equiv word_log_esimps(3) word_oa_dist word_oa_dist2)
    then have "(IntVal b yv) = val[(IntVal b xv) | (IntVal b yv)]"
      apply auto using eval_unused_bits_zero yv by presburger
    then show ?thesis
      by (metis p(3,4) evalDet xv yv)
  qed
  done

(* x & y \<mapsto> x when x.up \<in> y.Down *)
lemma RemoveRHSAndMask:
  assumes "(and (\<up>x) (\<down>y)) = (\<up>x)"
  assumes "(or (\<up>x) (\<down>y)) = (\<down>y)"
  shows "exp[x & y] \<ge> exp[x]"
  using assms apply auto
  subgoal premises p for m p v
  proof -
    obtain b ev where exp: "[m, p] \<turnstile> exp[x & y] \<mapsto> IntVal b ev"
      by (metis BinaryExpr bin_eval.simps(6) p(3,4,5) new_int.simps bin_eval_new_int)
    from exp obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      apply (subst (asm) unfold_binary_width) by force+
    from exp obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      apply (subst (asm) unfold_binary_width) by force+
    then have "IntVal b xv = val[(IntVal b xv) & (IntVal b yv)]"
      apply auto
      by (smt (verit, ccfv_threshold) or.right_neutral not_down_up_mask_and_zero_implies_zero p(1)
          bit.conj_cancel_right word_bw_comms(1) eval_unused_bits_zero yv word_bw_assocs(1)
          word_ao_absorbs(4) or_eq_not_not_and)
    then show ?thesis
      by (metis p(3,4) yv xv evalDet)
   qed
  done

(* Ian's new And optimisation
    x & y \<mapsto> 0 when x.up & y.up = 0
*)
lemma ReturnZeroAndMask:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "stamp_expr exp[x & y] = IntegerStamp b el eh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  assumes "wf_stamp exp[x & y]"
  assumes "(and (\<up>x) (\<up>y)) = 0"
  shows "exp[x & y] \<ge> exp[const (new_int b 0)]"
  using assms apply auto
  subgoal premises p for m p v
  proof -
    obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      by (metis valid_int wf_stamp_def assms(2,5) p(2,4,10) wf_stamp_def)
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      by (metis valid_int wf_stamp_def assms(1,4) p(3,9) wf_stamp_def)
    obtain ev where exp: "[m, p] \<turnstile> exp[x & y] \<mapsto> IntVal b ev"
      by (metis BinaryExpr bin_eval.simps(6) p(5,9,10,11) assms(3) valid_int wf_stamp_def)
    then have wfVal: "wf_value (new_int b 0)"
      by (metis eval_bits_1_64 new_int.simps new_int_take_bits validDefIntConst wf_value_def)
    then have lhsEq: "IntVal b ev = val[(IntVal b xv) & (IntVal b yv)]"
      by (metis bin_eval.simps(6) yv xv evalDet exp unfold_binary)
    then have newIntEquiv: "new_int b 0 = IntVal b ev"
      apply auto by (smt (z3) p(6) eval_unused_bits_zero xv yv up_mask_and_zero_implies_zero)
    then have isZero: "ev = 0"
      by auto
    then show ?thesis
      by (metis evalDet lhsEq newIntEquiv p(9,10) unfold_const wfVal xv yv)
   qed
   done

end

phase TacticSolving
  terminating size
begin

(* 
 (x ^ y) == (x ^ z) \<mapsto> y == z
 (x ^ y) == (z ^ x) \<mapsto> y == z
 (y ^ x) == (x ^ z) \<mapsto> y == z
 (y ^ x) == (z ^ x) \<mapsto> y == z
 *)

lemma binXorIsEqual:
  "bin[((x \<oplus> y) = (x \<oplus> z))] \<longleftrightarrow> bin[(y = z)]"
  by (metis (no_types, opaque_lifting) BinXorFallThrough xor.left_commute xor_self_eq)

lemma binXorIsDeterministic:
  assumes "y \<noteq> z"
  shows "bin[x \<oplus> y] \<noteq> bin[x \<oplus> z]"
  by (auto simp add: binXorIsEqual assms)

lemma XorZeroIsSelf64:
  assumes "x = IntVal 64 xv"
  assumes "val[x \<oplus> (IntVal 64 0)] \<noteq> UndefVal"
  shows  "val[x \<oplus> (IntVal 64 0)] = x"
  using assms by (cases x; auto)

lemma ValXorElimSelf64:
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  assumes "val[x \<oplus> y] \<noteq> UndefVal"
  assumes "val[y \<oplus> y] \<noteq> UndefVal"
  shows "val[x \<oplus> (y \<oplus> y)] = x"
  proof -
    have removeRhs: "val[x \<oplus> (y \<oplus> y)] = val[x \<oplus> (IntVal 64 0)]"
      by (simp add: assms(2))
    then have "val[x \<oplus> (IntVal 64 0)] = x"
      using XorZeroIsSelf64 by (simp add: assms(1))
    then show ?thesis
      by (simp add: removeRhs)
  qed

lemma ValXorIsReverse64:
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  assumes "z = IntVal 64 zv"
  assumes "z = val[x \<oplus> y]"
  assumes "val[x \<oplus> y] \<noteq> UndefVal"
  assumes "val[z \<oplus> y] \<noteq> UndefVal"
  shows "val[z \<oplus> y] = x"
  using val_xor_associative val_xor_self XorZeroIsSelf64 assms(1,2,4,6) by presburger

lemma valXorIsEqual_64:
  assumes "x = IntVal 64 xv"
  assumes "val[x \<oplus> y] \<noteq> UndefVal"
  assumes "val[x \<oplus> z] \<noteq> UndefVal"
  shows "val[(x \<oplus> y) eq (x \<oplus> z)] = val[y eq z]"
  using assms val_eq_commutative apply (cases x; cases y; cases z; auto)
  subgoal premises p for yv zv apply (cases "(yv = zv)"; simp)
  subgoal premises p
  proof -
    have isFalse: "bool_to_val (yv = zv) = bool_to_val False"
      by (simp add: p)
    then have unfoldTakebityv: "take_bit LENGTH(64) yv = yv"
      using take_bit_length_eq by blast
    then have unfoldTakebitzv: "take_bit LENGTH(64) zv = zv"
      using take_bit_length_eq by blast
    then have unfoldTakebitxv: "take_bit LENGTH(64) xv = xv"
      using take_bit_length_eq by blast
    then have notEq: "(xor (take_bit LENGTH(64) yv) (take_bit LENGTH(64) xv) =
                       xor (take_bit LENGTH(64) zv) (take_bit LENGTH(64) xv)) = False"
      unfolding unfoldTakebityv unfoldTakebitzv unfoldTakebitxv
      by (simp add: binXorIsEqual word_bw_comms(3) p)
    then show ?thesis
      proof -
        obtain l0 where l0: "l0 = (lowestOneBit (0::64 word))"
          by simp
        have "xor (take_bit l0 zv) (take_bit l0 xv) \<noteq> xor (take_bit l0 yv) (take_bit l0 xv)"
          using notEq lowestOneBit_bot take_bit_size_eq64 l0 by presburger
        then have "xor (take_bit l0 xv) (take_bit l0 yv) \<noteq> xor (take_bit l0 xv) (take_bit l0 zv)"
          by (simp add: xor.commute)
        then show ?thesis
          using lowestOneBit_bot l0 by force
      qed
    qed
   done
  done

lemma ValXorIsDeterministic_64:
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  assumes "z = IntVal 64 zv"
  assumes "val[x \<oplus> y] \<noteq> UndefVal"
  assumes "val[x \<oplus> z] \<noteq> UndefVal"
  assumes "yv \<noteq> zv"
  shows "val[x \<oplus> y] \<noteq> val[x \<oplus> z]"
  by (smt (z3) ValXorElimSelf64 val_xor_associative val_xor_self Value.distinct(1) Value.inject(1)
      assms val_xor_commutative lowestOneBit_bot)

lemma expXorIsEqual_64:
  assumes "stamp_expr x = IntegerStamp 64 xl xh"
  assumes "stamp_expr y = IntegerStamp 64 yl yh"
  assumes "stamp_expr z = IntegerStamp 64 zl zh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  assumes "wf_stamp z"
    shows "exp[(x \<oplus> y) eq (x \<oplus> z)] \<ge> exp[y eq z]"
  using assms apply auto
  subgoal premises p for m p x1 y1 x2 z1
  proof -
    obtain xVal where xVal: "[m,p] \<turnstile> x \<mapsto> xVal"
      using p(8) by simp
    obtain yVal where yVal: "[m,p] \<turnstile> y \<mapsto> yVal"
      using p(9) by simp
    obtain zVal where zVal: "[m,p] \<turnstile> z \<mapsto> zVal"
      using p(12) by simp
    obtain xv where xv: "xVal = IntVal 64 xv"
      by (metis p(1) p(4) wf_stamp_def xVal ExpIntBecomesIntVal)
    then have "[m,p] \<turnstile> exp[y eq z] \<mapsto> val[yVal eq zVal]"
      by (metis BinaryExpr bin_eval.simps(13) evalDet p(7,8,9,10,11,12,13) valXorIsEqual_64 xVal 
          yVal zVal)
    then show ?thesis
      by (metis xv evalDet p(8,9,10,11,12,13) valXorIsEqual_64 xVal yVal zVal)
  qed
  done

(* 64 bit versions *)
optimization XorIsEqual_64_1: "((x \<oplus> y) eq (x \<oplus> z)) \<longmapsto> (y eq z)
                        when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y) \<and>
                             (stamp_expr z = IntegerStamp 64 zl zh \<and> wf_stamp z)"
  using expXorIsEqual_64 by force

optimization XorIsEqual_64_2: "((x \<oplus> y) eq (z \<oplus> x)) \<longmapsto> (y eq z)
                        when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y) \<and>
                             (stamp_expr z = IntegerStamp 64 zl zh \<and> wf_stamp z)"
  using less_Suc_eq size_bin_cycle1_lt_succ_bin_sum apply fastforce
  by (meson dual_order.trans mono_binary exp_xor_commutative expXorIsEqual_64)

optimization XorIsEqual_64_3: "((y \<oplus> x) eq (x \<oplus> z)) \<longmapsto> (y eq z)
                        when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y) \<and>
                             (stamp_expr z = IntegerStamp 64 zl zh \<and> wf_stamp z)"
  apply (simp add: less_SucI size_bin_cycle1_lt_succ_bin_sum_lhs)
  by (meson dual_order.trans mono_binary exp_xor_commutative expXorIsEqual_64)

optimization XorIsEqual_64_4: "((y \<oplus> x) eq (z \<oplus> x)) \<longmapsto> (y eq z)
                        when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y) \<and>
                             (stamp_expr z = IntegerStamp 64 zl zh \<and> wf_stamp z)"
  by (meson dual_order.trans mono_binary exp_xor_commutative expXorIsEqual_64)

(*
XorEqZero
  (x ^ y) == 0 \<mapsto> (x == y)
 *)

lemma xorZeroIsEq:
  "bin[(xor xv yv) = 0] = bin[xv = yv]"
  by (metis binXorIsEqual xor_self_eq)

lemma valXorEqZero_64:
  assumes "val[(x \<oplus> y)] \<noteq> UndefVal"
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  shows "val[(x \<oplus> y) eq (IntVal 64 0)] = val[x eq y]"
  using assms apply (cases x; cases y; auto)
  unfolding bool_to_val_unwrap take_bit_size_eq64 Word.take_bit_length_eq by (simp add: xorZeroIsEq)

lemma expXorEqZero_64:
  assumes "stamp_expr x = IntegerStamp 64 xl xh"
  assumes "stamp_expr y = IntegerStamp 64 yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
    shows "exp[(x \<oplus> y) eq (const (IntVal 64 0))] \<ge> exp[x eq y]"
  using assms apply auto
  subgoal premises p for m p x1 y1
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p by blast
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p by fast
    obtain xvv where xvv: "xv = IntVal 64 xvv"
      by (metis p(1,3) wf_stamp_def xv ExpIntBecomesIntVal)
    obtain yvv where yvv: "yv = IntVal 64 yvv"
      by (metis p(2,4) wf_stamp_def yv ExpIntBecomesIntVal)
    have "[m,p] \<turnstile> exp[x eq y] \<mapsto> val[xv eq yv]"
      by (smt (z3) BinaryExpr val_eq_commutative val_xor_self Value.distinct(1) valXorIsEqual_64 xvv
          bin_eval.simps(13) evalDet p(5,6,7,8) xv yv)
    then show ?thesis
      by (metis evalDet p(6,7,8) valXorEqZero_64 xv xvv yv yvv)
  qed
  done

optimization XorEqZero_64: "((x \<oplus> y) eq (const (IntVal 64 0))) \<longmapsto> (x eq y)
                            when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and>
                                 (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y)"
  apply (metis add_2_eq_Suc bin_cycles.simps(17,5) less_add_Suc2 size_bin_eq_cycles_eq_iff)
  using expXorEqZero_64 by fast

lemma xorNeg1IsEq:
  "bin[(xor xv yv) = (not 0)] = bin[xv = not yv]"
  using xorZeroIsEq by fastforce

lemma valXorEqNeg1_64:
  assumes "val[(x \<oplus> y)] \<noteq> UndefVal"
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  shows "val[(x \<oplus> y) eq (IntVal 64 (not 0))] = val[x eq (\<not>y)]"
  using assms apply (cases x; cases y; auto)
  unfolding bool_to_val_unwrap take_bit_size_eq64 Word.take_bit_length_eq using xorNeg1IsEq by auto

lemma expXorEqNeg1_64:
  assumes "stamp_expr x = IntegerStamp 64 xl xh"
  assumes "stamp_expr y = IntegerStamp 64 yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
    shows "exp[(x \<oplus> y) eq (const (IntVal 64 (not 0)))] \<ge> exp[x eq (\<not>y)]"
  using assms apply auto
  subgoal premises p for m p x1 y1
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p by blast
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p by fast
    obtain xvv where xvv: "xv = IntVal 64 xvv"
      by (metis p(1,3) wf_stamp_def xv ExpIntBecomesIntVal)
    obtain yvv where yvv: "yv = IntVal 64 yvv"
      by (metis p(2,4) wf_stamp_def yv ExpIntBecomesIntVal)
    obtain nyv where nyv: "[m,p] \<turnstile> exp[(\<not>y)] \<mapsto> nyv"
      by (metis Value.distinct(1) intval_equals.simps(2) intval_not.elims intval_xor.simps(2,7,8,9)
          new_int.simps p(5,7) unary_eval.simps(3) unfold_unary val_xor_commutative)
    then have nyvEq: "val[\<not>yv] = nyv"
      using evalDet yv by fastforce
    obtain nyvv where nyvv: "nyv = IntVal 64 nyvv"
      using nyvEq intval_not.simps yvv by force
    have notUndef: "val[xv eq (\<not>yv)] \<noteq> UndefVal"
      using bool_to_val.elims nyvEq nyvv xvv by auto
    have "[m,p] \<turnstile> exp[x eq (\<not>y)] \<mapsto> val[xv eq (\<not>yv)]"
      by (metis BinaryExpr bin_eval.simps(13) notUndef nyv nyvEq xv)
    then show ?thesis
      by (metis bit.compl_zero evalDet p(6,7,8) valXorEqNeg1_64 xvv yvv xv yv)
  qed
  done

optimization XorEqNeg1_64: "((x \<oplus> y) eq (const (IntVal 64 (not 0)))) \<longmapsto> (x eq (\<not>y))
                            when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and>
                                 (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y)"
  using expXorEqNeg1_64 apply auto (* termination proof *) sorry

(* Definitions and lemmas for primitives *)
fun forPrimitive :: "Stamp \<Rightarrow> int64 \<Rightarrow> IRExpr" where
  "forPrimitive (IntegerStamp b lo hi) v =
      ConstantExpr (if take_bit b v = v then (IntVal b v) else UndefVal)" |
  "forPrimitive _ _ = ConstantExpr UndefVal"

lemma unfold_forPrimitive:
  "forPrimitive s v =
    ConstantExpr (if is_IntegerStamp s \<and> take_bit (stp_bits s) v = v
                  then (IntVal (stp_bits s) v)
                  else UndefVal)"
  by (cases s; auto)

lemma forPrimitive_size[size_simps]: "size (forPrimitive s v) = 1"
  by (cases s; auto)

optimization opt_optimise_integer_test_2:
     "(((x & (const val[true])) eq (const val[false])) ? (const val[false]) : (const val[true]))
         \<longmapsto> x
         when (x = ConstantExpr val[false] | (x = ConstantExpr val[true]))" .

end

end