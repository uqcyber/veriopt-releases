theory NegatePhase
  imports
    Common
begin

section \<open>Optimizations for Negate Nodes\<close>

phase NegateNode
  terminating size
begin

(* Word level proofs *)
lemma bin_negative_cancel:
 "-1 * (-1 * ((x::('a::len) word))) = x"
  by auto

(* Value level proofs *)
lemma val_negative_cancel:
  assumes "intval_negate (new_int b v) \<noteq> UndefVal"
  shows "val[-(-(new_int b v))] = val[new_int b v]"
  using assms by simp

lemma val_distribute_sub:
  assumes "x \<noteq> UndefVal \<and> y \<noteq> UndefVal"
  shows "val[-(x - y)] = val[y - x]"
  using assms by (cases x; cases y; auto)

(* Exp level proofs *)
lemma exp_distribute_sub:
  shows "exp[-(x - y)] \<ge> exp[y - x]"
  using val_distribute_sub apply auto
  using evaltree_not_undef by auto

lemma exp_negative_cancel:
  shows "exp[-(-x)] \<ge> exp[x]"
  using val_negative_cancel apply auto 
  subgoal premises p for m p vb
    proof -
      have 2: "[m,p] \<turnstile> x \<mapsto> vb"
        by (simp add: p(2))
      then have "val[-(-vb)] \<noteq> UndefVal"
        by (simp add: p(1))
      then have "val[-(-vb)] = vb"
        apply (cases vb; auto) using "2" eval_unused_bits_zero by auto
      then have "[m,p] \<turnstile> x \<mapsto> val[-(-vb)]"
        by (simp add: "2")
      then show ?thesis
        by auto
    qed
  done

lemma exp_negative_shift: 
  assumes "stamp_expr x = IntegerStamp b' lo hi" 
  and     "unat y = (b' - 1)"
  shows   "exp[-(x >> (const (new_int b y)))] \<ge> exp[x >>> (const (new_int b y))]"
  apply auto
  subgoal premises p for m p xa
  proof - 
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(2) by auto
    then have 1: "intval_negate (intval_right_shift xa (IntVal b (take_bit b y))) \<noteq> UndefVal"
      using evalDet p(1) p(2) by blast
    then have 2: "intval_right_shift xa (IntVal b (take_bit b y)) \<noteq> UndefVal"
      by auto
    then have 3: "- ((2::int) ^ b div (2::int)) \<sqsubseteq> sint (signed_take_bit (b - Suc (0::nat)) (take_bit b y))"
      by (simp add: p(6))
    then have 4: "sint (signed_take_bit (b - Suc (0::nat)) (take_bit b y)) < (2::int) ^ b div (2::int)"
      using p(7) by blast
    then have 5: "(0::nat) < b"
      by (simp add: p(4))
    then have 6: "b \<sqsubseteq> (64::nat)"
      by (simp add: p(5))
    then have 7: "[m,p] \<turnstile> BinaryExpr BinURightShift x
                 (ConstantExpr (IntVal b (take_bit b y))) \<mapsto> 
                  intval_negate (intval_right_shift xa (IntVal b (take_bit b y)))"
      apply (cases y; auto)

      subgoal premises p for n
        proof - 
          have sg1: "y = word_of_nat n"
            by (simp add: p(1))
          then have sg2: "n < (18446744073709551616::nat)"
            by (simp add: p(2))
          then have sg3: "b \<sqsubseteq> (64::nat)"
            by (simp add: "6")
          then have sg4: "[m,p] \<turnstile> BinaryExpr BinURightShift x
                 (ConstantExpr (IntVal b (take_bit b (word_of_nat n)))) \<mapsto> 
                  intval_negate (intval_right_shift xa (IntVal b (take_bit b (word_of_nat n))))"
             sorry
          then show ?thesis
            by simp
        qed 
      done
    then show ?thesis
      by (metis evalDet p(2) xa)
  qed 
  done

text \<open>Optimisations\<close>
optimization NegateCancel: "-(-(x)) \<longmapsto> x"
  using val_negative_cancel exp_negative_cancel by blast 

(* FloatStamp condition is omitted. Not 100% sure. *)
optimization DistributeSubtraction: "-(x - y) \<longmapsto> (y - x)" 
  using exp_distribute_sub by simp

(* Need to prove exp_negative_shift *)
optimization NegativeShift: "-(x >> (const (new_int b y))) \<longmapsto> x >>> (const (new_int b y))
                                   when (stamp_expr x = IntegerStamp b' lo hi \<and> unat y = (b' - 1))"
  using exp_negative_shift by simp 


end (* End of NegatePhase *)

end (* End of file *)
