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

(* --- New Optimisations - submitted and added into Graal --- *)
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
  using NotXorToXorExp by simp

(* --- New optimisations - submitted, not added into Graal yet --- *)
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

(* 
  ~e == e \<mapsto> false
 *)

lemma TakeBitNotSelf:
  "(take_bit 32 (not e) = e) = False"
  by (metis even_not_iff even_take_bit_eq zero_neq_numeral)

lemma ValNeverEqNotSelf:
  assumes "e = IntVal 32 ev"
  shows "val[intval_equals (\<not>e) e] = val[bool_to_val False]"
  by (simp add: TakeBitNotSelf assms)

lemma ExpIntBecomesIntVal:
  assumes "stamp_expr x = IntegerStamp 32 xl xh"
  assumes "wf_stamp x"
  assumes "valid_value v (IntegerStamp 32 xl xh)"
  assumes "[m,p] \<turnstile> x \<mapsto> v"
  shows "\<exists>xv. v = IntVal 32 xv"
  using assms by (simp add: IRTreeEvalThms.valid_value_elims(3)) 

lemma ExpNeverNotSelf:
  assumes "stamp_expr x = IntegerStamp 32 xl xh"
  assumes "wf_stamp x"
  shows "exp[BinaryExpr BinIntegerEquals (\<not>x) x] \<ge>
         exp[(const (bool_to_val False))]" 
  using assms apply auto
  subgoal premises p for m p xa xaa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(5) by auto
    then obtain xv where xv: "xa = IntVal 32 xv"
      by (metis p(1,2) valid_int wf_stamp_def)
    then have lhsVal: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals (\<not>x) x] \<mapsto> 
                               val[intval_equals (\<not>xa) xa]" 
      by (metis p(3,4,5,6) unary_eval.simps(3) evaltree.BinaryExpr bin_eval.simps(11) xa UnaryExpr 
          evalDet)
    have wfVal: "wf_value (IntVal 32 0)" 
      using wf_value_def apply rule 
      by (metis IntVal0 intval_word.simps nat_le_linear new_int.simps numeral_le_iff wf_value_def
          semiring_norm(71,76) validDefIntConst verit_comp_simplify1(3) zero_less_numeral)
    then have rhsVal: "[m,p] \<turnstile> exp[(const (bool_to_val False))] \<mapsto> val[bool_to_val False]"
      by auto
    then have valEq: "val[intval_equals (\<not>xa) xa] = val[bool_to_val False]" 
      using ValNeverEqNotSelf by (simp add: xv)
    then show ?thesis
      by (metis bool_to_val.simps(2) evalDet p(3,5) rhsVal xa)
   qed
  done

optimization NeverEqNotSelf: "exp[BinaryExpr BinIntegerEquals (\<not>x) x] \<longmapsto> 
                              exp[(const (bool_to_val False))]
                        when (stamp_expr x = IntegerStamp 32 xl xh \<and> wf_stamp x)"
  apply (simp add: Suc_lessI) using ExpNeverNotSelf by force

(* --- New optimisations - not submitted / added into Graal yet --- *)
(* 
  (x ^ y) == x \<mapsto> y == 0
  x == (x ^ y) \<mapsto> y == 0 
  (x ^ y) == y \<mapsto> x == 0 
  y == (x ^ y) \<mapsto> x == 0
 *)
lemma BinXorFallThrough:
  shows "bin[(x \<oplus> y) = x] \<longleftrightarrow> bin[y = 0]"
  by (metis xor.assoc xor.left_neutral xor_self_eq)

lemma valXorEqual:
  assumes "x = new_int 32 xv"
  assumes "val[x \<oplus> x] \<noteq> UndefVal"
  shows "val[x \<oplus> x] = val[new_int 32 0]"
  using assms by (cases x; auto)

lemma valXorAssoc:
  assumes "x = new_int b xv"
  assumes "y = new_int b yv"
  assumes "z = new_int b zv"
  assumes "val[(x \<oplus> y) \<oplus> z] \<noteq> UndefVal"
  assumes "val[x \<oplus> (y \<oplus> z)] \<noteq> UndefVal"
  shows "val[(x \<oplus> y) \<oplus> z] = val[x \<oplus> (y \<oplus> z)]"
  by (simp add: xor.commute xor.left_commute assms)

lemma valNeutral:
  assumes "x = new_int b xv"
  assumes "val[x \<oplus> (new_int b 0)] \<noteq> UndefVal"
  shows "val[x \<oplus> (new_int b 0)] = val[x]"
  using assms by (auto; meson)

lemma ValXorFallThrough:
  assumes "x = new_int b xv"
  assumes "y = new_int b yv"
  shows "val[intval_equals (x \<oplus> y) x] = val[intval_equals y (new_int b 0)]"
  by (simp add: assms BinXorFallThrough)

lemma ValEqAssoc:
  "val[intval_equals x y] = val[intval_equals y x]"
  apply (cases x; cases y; auto) by (smt (verit, best))

lemma ExpEqAssoc:
  "exp[BinaryExpr BinIntegerEquals x y] \<ge> exp[BinaryExpr BinIntegerEquals y x]"
  by (auto simp add: ValEqAssoc)

lemma ExpXorBinEqCommute:
  "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) y] \<ge> exp[BinaryExpr BinIntegerEquals (y \<oplus> x) y]"
  using exp_xor_commutative mono_binary by blast

lemma ExpXorFallThrough:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  shows "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) x] \<ge>
         exp[BinaryExpr BinIntegerEquals y (const (new_int b 0))]"
  using assms apply auto 
  subgoal premises p for m p xa xaa ya
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(5) by auto
    obtain ya where ya: "[m,p] \<turnstile> y \<mapsto> ya"
      using p(8) by auto
    obtain b xv where xv0: "xa = IntVal b xv" 
      by (smt (verit) evalDet intval_equals.elims p(5,6) xa)
    then have xv: "xa = new_int b xv"  
      by (metis eval_unused_bits_zero new_int.elims xa) 
    obtain yv where yv0: "ya = IntVal b yv" 
      by (metis Value.inject(1) valid_int wf_stamp_def xa xv0 p(1,2,3,4) ya)
    then have yv: "ya = new_int b yv"
      by (metis eval_unused_bits_zero new_int.simps ya yv0) 
    then have lhsVal: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals (x \<oplus> y) x] \<mapsto> 
                               val[intval_equals (xa \<oplus> ya) xa]"
      by (smt (z3) bin_eval.simps(6,11) evalDet p(5,6,7,8,9) evaltree.BinaryExpr ya xa)
    then have wfVal: "wf_value (new_int b 0)"
      by (metis eval_bits_1_64 new_int.simps new_int_take_bits validDefIntConst wf_value_def xa xv0)
    then have evalConst: "[m,p] \<turnstile> exp[(const (new_int b 0))] \<mapsto> (new_int b 0)" 
      by (simp add: constEvalIsConst)
    then have rhsVal: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals y (const (new_int b 0))] \<mapsto> 
                               val[intval_equals ya (new_int b 0)]"      
      by (metis ValXorFallThrough lhsVal evaltree.BinaryExpr yv ya bin_eval.simps(11) BinaryExprE 
          xv)
    then have valEquiv: "val[intval_equals (xa \<oplus> ya) xa] = val[intval_equals ya (new_int b 0)]"
      using ValXorFallThrough by (simp add: yv xv)
    then have eval: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals y (const (new_int b 0))] \<mapsto> 
                             val[intval_equals (xa \<oplus> ya) xa]" 
      using rhsVal by simp
    then show ?thesis
      by (metis evalDet new_int.elims p(1,3,5,7,8) take_bit_of_0 valid_value.simps(1) wf_stamp_def 
          ya xa xv0)
   qed 
  done

lemma ExpXorFallThrough2:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  shows "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) y] \<ge>
         exp[BinaryExpr BinIntegerEquals x (const (new_int b 0))]"
  by (meson assms dual_order.trans ExpXorBinEqCommute ExpXorFallThrough)

optimization XorFallThrough1: "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) x] \<longmapsto> 
                               exp[BinaryExpr BinIntegerEquals y (const (new_int b 0))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  using ExpXorFallThrough by force

optimization XorFallThrough2: "exp[BinaryExpr BinIntegerEquals x (x \<oplus> y)] \<longmapsto> 
                               exp[BinaryExpr BinIntegerEquals y (const (new_int b 0))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  using ExpXorFallThrough ExpEqAssoc by force

optimization XorFallThrough3: "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) y] \<longmapsto> 
                               exp[BinaryExpr BinIntegerEquals x (const (new_int b 0))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  using ExpXorFallThrough2 by force

optimization XorFallThrough4: "exp[BinaryExpr BinIntegerEquals y (x \<oplus> y)] \<longmapsto> 
                               exp[BinaryExpr BinIntegerEquals x (const (new_int b 0))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  using ExpXorFallThrough2 ExpEqAssoc by force

end

context stamp_mask
begin

(* Generalization of old Or optimisation 
   x | y \<mapsto> -1 when (downMask x | downMask y == -1)
*)

lemma ExpIntBecomesIntValArbitrary:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "wf_stamp x"
  assumes "valid_value v (IntegerStamp b xl xh)"
  assumes "[m,p] \<turnstile> x \<mapsto> v"
  shows "\<exists>xv. v = IntVal b xv"
  using assms by (simp add: IRTreeEvalThms.valid_value_elims(3)) 

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
    obtain evv where ev: "[m, p] \<turnstile> exp[x | y] \<mapsto> IntVal b evv"
      by (metis BinaryExpr bin_eval.simps(5) unfold_binary p(5,9,10,11) valid_int wf_stamp_def
          assms(3))
    then have rhsWf: "wf_value (new_int b (not 0))"
      by (metis eval_bits_1_64 new_int.simps new_int_take_bits validDefIntConst wf_value_def)
    then have rhs: "(new_int b (not 0)) = val[IntVal b xv | IntVal b yv]" 
      by (smt (verit) bit.de_Morgan_conj word_bw_comms(2) word_not_not yv bit.disj_conj_distrib xv
          down_spec assms(5,7) intval_or.simps(1) new_int_bin.simps or.right_neutral ucast_id
          word_ao_absorbs(1))
    then have notMaskEq: "(new_int b (not 0)) = (new_int b (mask b))"
      by auto
    then show ?thesis 
      by (metis neg_one.elims neg_one_value p(9,10) rhsWf unfold_const evalDet xv yv rhs)
    qed
   done

end

end