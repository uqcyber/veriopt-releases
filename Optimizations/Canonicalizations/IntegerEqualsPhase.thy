subsection \<open>IntegerEqualsNode Phase\<close>

theory IntegerEqualsPhase
  imports
    Common
begin

phase IntegerEqualsNode
  terminating size
begin

(* Helpers *)

definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

lemma val_and_commute:
  assumes "x \<noteq> UndefVal"
  assumes "y \<noteq> UndefVal"
  shows "val[x & y] = val[y & x]"
  using assms apply (cases x; cases y; auto) by (simp add: word_bw_comms(1))

lemma exp_and_commute:
  shows "exp[x & y] \<ge> exp[y & x]"
  apply auto by (simp add: BinaryExpr evaltree_not_undef val_and_commute)

lemma val_or_commute:
  assumes "x \<noteq> UndefVal"
  assumes "y \<noteq> UndefVal"
  shows "val[x | y] = val[y | x]"
  using assms apply (cases x; cases y; auto) by (simp add: or.commute)

lemma exp_or_commute:
  shows "exp[x | y] \<ge> exp[y | x]"
  apply auto by (simp add: BinaryExpr evaltree_not_undef val_or_commute)

lemma val_equals_commute:
  assumes "x \<noteq> UndefVal"
  assumes "y \<noteq> UndefVal"
  shows "val[intval_equals x y] = val[intval_equals y x]"
  using assms apply (cases x; cases y; auto) by (smt (verit, best))

lemma exp_equals_commute:
  shows "exp[BinaryExpr BinIntegerEquals x y] \<ge> exp[BinaryExpr BinIntegerEquals y x]"
  apply auto by (simp add: BinaryExpr evaltree_not_undef val_equals_commute)

(* AndOrEquals
  (x & y) == (x | y) \<mapsto> (x == y) 
*)

lemma val_and_or_eq_64:
  assumes "val[intval_equals (x & y) (x | y)] \<noteq> UndefVal"
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  shows "val[intval_equals (x & y) (x | y)] = val[intval_equals x y]"
  using assms apply (cases x; cases y; auto)
  subgoal premises p
    proof -
      have unfold_x: "take_bit 64 xv = take_bit (LENGTH(64)) xv"
        by simp
      have unfold_y: "take_bit 64 yv = take_bit (LENGTH(64)) yv"
        by auto
      then show ?thesis
        unfolding unfold_x unfold_y take_bit_length_eq
        by (smt (verit, ccfv_SIG) and.idem word_ao_absorbs(5) word_ao_equiv word_bw_assocs(1))
    qed
  done

lemma exp_and_or_eq_64:
  assumes "stamp_expr x = IntegerStamp 64 xl xh"
  assumes "stamp_expr y = IntegerStamp 64 yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  shows "exp[BinaryExpr BinIntegerEquals (x & y) (x | y)] \<ge> 
         exp[BinaryExpr BinIntegerEquals x y]"
  apply auto
  subgoal premises p for m p x1 y1 x2 y2
    proof -
      obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
        using p(2) by auto
      obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
        using p(3) by auto
      obtain xw where xw: "xv = IntVal 64 xw"
        by (metis assms(1,3) valid_int wf_stamp_def xv)
      have val: "val[intval_equals (xv & yv) (xv | yv) = intval_equals xv yv]"
        by (metis assms(2,4) evalDet p(1,2,3,5,6) val_and_or_eq_64 valid_int wf_stamp_def xv xw yv)
      then show ?thesis
        by (metis bin_eval.simps(13) evalDet p(1,2,3,5,6) unfold_binary xv yv)
    qed
  done

(* XorNotFallThrough
  (x \<oplus> y) == \<not>x \<mapsto> (y == -1) 
*)

lemma val_xor_not_fall_through:
  assumes "x = new_int b xv"
  assumes "y = new_int b yv"
  shows "val[intval_equals (x \<oplus> y) (\<not>x)] = val[intval_equals y (new_int b (not 0))]"
  using assms apply auto 
  by (smt (verit, ccfv_SIG) bit.xor_cancel_right bit.xor_left_self mask_eq_take_bit_minus_one
      take_bit_not_take_bit take_bit_xor)

lemma exp_xor_not_fall_through:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  shows "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) (\<not>x)] \<ge>
         exp[BinaryExpr BinIntegerEquals y (const (new_int b (not 0)))]"
  using assms apply auto 
  subgoal premises p for m p xa ya xaa
  proof -
    obtain b xv where xa: "[m,p] \<turnstile> x \<mapsto> new_int b xv"
      by (metis eval_unused_bits_zero intval_not.elims new_int.elims p(9,10))
    obtain yv where ya: "[m,p] \<turnstile> y \<mapsto> new_int b yv"
      by (metis new_int.elims p(1,2,3,4,7) valid_int valid_value.simps(1) wf_stamp_def xa)
    have yaEval: "[m,p] \<turnstile> y \<mapsto> ya" 
      by (simp add: p(7))
    have xaaEquiv: "xaa = xa"
      using evalDet p(6,9) by auto
    then have wfVal: "wf_value (new_int b (not 0))"
      by (metis eval_bits_1_64 new_int.simps new_int_take_bits validDefIntConst wf_value_def xa)
    have rhs: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals y (const (new_int b (not 0)))] \<mapsto>
                       val[intval_equals ya (new_int b (not 0))]" 
      by (metis (no_types, lifting) yaEval bin_eval.simps(13) val_xor_not_fall_through evalDet wfVal
          p(5,6) unfold_binary unfold_const  xa xaaEquiv ya)
    have eval: "val[intval_equals (xa \<oplus> ya) (\<not>xa)] = val[intval_equals ya (new_int b (not 0))]"
      by (metis val_xor_not_fall_through evalDet p(6,7) xa ya)
    then show ?thesis
      by (metis bit.compl_zero mask_eq_take_bit_minus_one new_int.elims p(2,4) xaaEquiv wf_stamp_def
          valid_value.simps(1) rhs ya)
   qed 
  done

(* Optimizations *)

optimization AndOrEquals1: "exp[BinaryExpr BinIntegerEquals (x & y) (x | y)] \<longmapsto>
                        exp[BinaryExpr BinIntegerEquals x y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
   apply (metis less_SucI less_add_Suc1 size_binary_const size_non_add)
   using exp_and_or_eq_64 by blast

optimization AndOrEquals2: "exp[BinaryExpr BinIntegerEquals (x & y) (y | x)] \<longmapsto>
                        exp[BinaryExpr BinIntegerEquals x y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
   apply (metis less_SucI less_add_Suc1 size_binary_const size_non_add)
   using AndOrEquals1 apply simp by (meson exp_or_commute le_expr_def mono_binary)

optimization AndOrEquals3: "exp[BinaryExpr BinIntegerEquals (y & x) (x | y)] \<longmapsto>
                        exp[BinaryExpr BinIntegerEquals x y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis less_SucI less_add_Suc2 size_binary_const size_non_add)
  by (meson dual_order.refl dual_order.trans exp_and_commute mono_binary exp_and_or_eq_64)

optimization AndOrEquals4: "exp[BinaryExpr BinIntegerEquals (y & x) (y | x)] \<longmapsto>
                        exp[BinaryExpr BinIntegerEquals x y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (smt (verit, del_insts) ab_semigroup_add_class.add_ac(1) add_2_eq_Suc' add_less_mono
         add_mono_thms_linordered_field(3) size_binary_lhs size_binary_rhs verit_comp_simplify1(2)
         size_non_add size_binary_const less_add_Suc2)
  by (meson dual_order.trans exp_and_commute exp_or_commute mono_binary exp_and_or_eq_64)

optimization AndOrEquals5: "exp[BinaryExpr BinIntegerEquals (x | y) (x & y)] \<longmapsto>
                        exp[BinaryExpr BinIntegerEquals x y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis less_SucI less_add_Suc1 size_binary_const size_non_add)
  by (meson exp_equals_commute order.trans exp_and_or_eq_64)

optimization AndOrEquals6: "exp[BinaryExpr BinIntegerEquals (x | y) (y & x)] \<longmapsto>
                        exp[BinaryExpr BinIntegerEquals x y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis less_SucI less_add_Suc1 size_binary_const size_non_add)
  using AndOrEquals5 apply simp by (meson exp_and_commute le_expr_def mono_binary)

optimization AndOrEquals7: "exp[BinaryExpr BinIntegerEquals (y | x) (x & y)] \<longmapsto>
                        exp[BinaryExpr BinIntegerEquals x y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (metis add_Suc_right lessI less_SucI size_binary_const size_non_add trans_less_add2)
  using AndOrEquals6 apply simp by (meson exp_equals_commute le_expr_def) 

optimization AndOrEquals8: "exp[BinaryExpr BinIntegerEquals (y | x) (y & x)] \<longmapsto>
                        exp[BinaryExpr BinIntegerEquals x y]
                        when (stamp_expr x = IntegerStamp 64 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 64 ly hy \<and> wf_stamp y)"
  apply (smt (verit, ccfv_SIG) not_less_eq trans_less_add2  Canonicalization.const_size Suc_eq_plus1
         ab_semigroup_add_class.add_ac(1) add.commute is_ConstantExpr_def size_non_add
         size_binary_const)
  by (meson exp_and_or_eq_64 order.trans exp_equals_commute)

optimization XorNotFallThrough: "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) (\<not>x)] \<longmapsto> 
                                 exp[BinaryExpr BinIntegerEquals y (const (new_int b (not 0)))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  apply (simp add: less_SucI size_binary_rhs trans_less_add1)
  using exp_xor_not_fall_through by force

end (* End of IntegerEqualsPhase *)

end (* End of file *)