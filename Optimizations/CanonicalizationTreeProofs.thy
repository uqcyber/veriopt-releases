section \<open>Canonicalization Phase\<close>

theory CanonicalizationTreeProofs
  imports
    CanonicalizationTree
    Semantics.TreeToGraph
    Semantics.IRTreeEvalThms
begin

lemma neutral_rewrite_helper:
  shows "valid_value (IntegerStamp 32 lo hi) x \<Longrightarrow> intval_mul x (IntVal32 (1)) = x"
  and   "valid_value (IntegerStamp 64 lo hi) x \<Longrightarrow> intval_mul x (IntVal64 (1)) = x"

  and   "valid_value (IntegerStamp 32 lo hi) x \<Longrightarrow> intval_add x (IntVal32 (0)) = x"
  and   "valid_value (IntegerStamp 64 lo hi) x \<Longrightarrow> intval_add x (IntVal64 (0)) = x"

  and   "valid_value (IntegerStamp 32 lo hi) x \<Longrightarrow> intval_sub x (IntVal32 (0)) = x"
  and   "valid_value (IntegerStamp 64 lo hi) x \<Longrightarrow> intval_sub x (IntVal64 (0)) = x"

  and   "valid_value (IntegerStamp 32 lo hi) x \<Longrightarrow> intval_xor x (IntVal32 (0)) = x"
  and   "valid_value (IntegerStamp 64 lo hi) x \<Longrightarrow> intval_xor x (IntVal64 (0)) = x"

  and   "valid_value (IntegerStamp 32 lo hi) x \<Longrightarrow> intval_or x (IntVal32 (0)) = x"
  and   "valid_value (IntegerStamp 64 lo hi) x \<Longrightarrow> intval_or x (IntVal64 (0)) = x"
  using valid32or64_both by fastforce+

lemma annihilator_rewrite_helper:
  shows "valid_value (IntegerStamp 32 lo hi) x \<Longrightarrow> intval_mul x (IntVal32 0) = IntVal32 0"
  and   "valid_value (IntegerStamp 64 lo hi) x \<Longrightarrow> intval_mul x (IntVal64 0) = IntVal64 0"

  and   "valid_value (IntegerStamp 32 lo hi) x \<Longrightarrow> intval_and x (IntVal32 0) = IntVal32 0"
  and   "valid_value (IntegerStamp 64 lo hi) x \<Longrightarrow> intval_and x (IntVal64 0) = IntVal64 0"

  and   "valid_value (IntegerStamp 32 lo hi) x \<Longrightarrow> intval_or x (IntVal32 (-1)) = IntVal32 (-1)"
  and   "valid_value (IntegerStamp 64 lo hi) x \<Longrightarrow> intval_or x (IntVal64 (-1)) = IntVal64 (-1)"
  using valid32or64_both
  apply auto
  apply (metis intval_mul.simps(1) mult_zero_right valid32)
  by fastforce+

lemma idempotent_rewrite_helper:
  shows "valid_value (IntegerStamp 32 lo hi) x \<Longrightarrow> intval_and x x = x"
  and   "valid_value (IntegerStamp 64 lo hi) x \<Longrightarrow> intval_and x x = x"

  and   "valid_value (IntegerStamp 32 lo hi) x \<Longrightarrow> intval_or x x = x"
  and   "valid_value (IntegerStamp 64 lo hi) x \<Longrightarrow> intval_or x x = x"
  using valid32or64_both
  apply auto 
  by fastforce+

value "size (v::32 word)"

lemma signed_int_bottom32: "-(((2::int) ^ 31)) \<le> sint (v::int32)"
proof -
  have "size v = 32" apply (cases v; auto) sorry (* weird *)
  then show ?thesis
    using sint_range_size sorry (* it says proof found... *)
qed

lemma signed_int_top32: "(2 ^ 31) - 1 \<ge> sint (v::int32)"
proof -
  have "size v = 32" sorry (* weird *)
  then show ?thesis
    using sint_range_size sorry (* it says proof found... *)
qed

lemma lower_bounds_equiv32: "-(((2::int) ^ 31)) = (2::int) ^ 32 div 2 * - 1"
  by fastforce

lemma upper_bounds_equiv32: "(2::int) ^ 31 = (2::int) ^ 32 div 2"
  by simp

lemma bit_bounds_min32: "((fst (bit_bounds 32))) \<le> (sint (v::int32))"
  unfolding bit_bounds.simps fst_def using signed_int_bottom32 lower_bounds_equiv32
  by auto

lemma bit_bounds_max32: "((snd (bit_bounds 32))) \<ge> (sint (v::int32))"
  unfolding bit_bounds.simps fst_def using signed_int_top32 upper_bounds_equiv32
  by auto

value "size (v::64 word)"

lemma signed_int_bottom64: "-(((2::int) ^ 63)) \<le> sint (v::int64)"
proof -
  have "size v = 64" apply (cases v; auto) sorry (* weird *)
  then show ?thesis
    using sint_range_size sorry (* it says proof found... *)
qed

lemma signed_int_top64: "(2 ^ 63) - 1 \<ge> sint (v::int64)"
proof -
  have "size v = 32" sorry (* weird *)
  then show ?thesis
    using sint_range_size sorry (* it says proof found... *)
qed

lemma lower_bounds_equiv64: "-(((2::int) ^ 63)) = (2::int) ^ 64 div 2 * - 1"
  by fastforce

lemma upper_bounds_equiv64: "(2::int) ^ 63 = (2::int) ^ 64 div 2"
  by simp

lemma bit_bounds_min64: "((fst (bit_bounds 64))) \<le> (sint (v::int64))"
  unfolding bit_bounds.simps fst_def using signed_int_bottom64 lower_bounds_equiv64
  by auto

lemma bit_bounds_max64: "((snd (bit_bounds 64))) \<ge> (sint (v::int64))"
  unfolding bit_bounds.simps fst_def using signed_int_top64 upper_bounds_equiv64
  by auto

lemma unrestricted_32bit_always_valid:
  "valid_value (unrestricted_stamp (IntegerStamp 32 lo hi)) (IntVal32 v)"
  using valid_value.simps(1) bit_bounds_min32 bit_bounds_max32
  using unrestricted_stamp.simps(2) by presburger

lemma unrestricted_64bit_always_valid:
  "valid_value (unrestricted_stamp (IntegerStamp 64 lo hi)) (IntVal64 v)"
  using valid_value.simps(2) bit_bounds_min64 bit_bounds_max64
  using unrestricted_stamp.simps(2) by presburger

lemma unary_undef: "val = UndefVal \<Longrightarrow> unary_eval op val = UndefVal"
  by (cases op; auto)

lemma unary_obj: "val = ObjRef x \<Longrightarrow> unary_eval op val = UndefVal"
  by (cases op; auto)

lemma unary_eval_implies_valud_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value (stamp_expr expr) val"
  shows "valid_value (stamp_expr (UnaryExpr op expr)) result"
proof -
  have is_IntVal: "\<exists> x y. result = IntVal32 x \<or> result = IntVal64 y"
    using assms(2,3) apply (cases op; auto; cases val; auto)
    by metis
  then have "is_IntegerStamp (stamp_expr expr)"
    using assms(2,3,4) apply (cases "(stamp_expr expr)"; auto) 
    using valid_VoidStamp unary_undef apply simp
    using valid_VoidStamp unary_undef apply simp
    using valid_ObjStamp unary_obj apply fastforce
    using valid_ObjStamp unary_obj by fastforce
  then obtain b lo hi where stamp_expr_def: "stamp_expr expr = (IntegerStamp b lo hi)"
    using is_IntegerStamp_def by auto
  then have "stamp_expr (UnaryExpr op expr) = unrestricted_stamp (IntegerStamp b lo hi)"
    using stamp_expr.simps(1) stamp_unary.simps(1) by presburger
  from stamp_expr_def have bit32: "b = 32 \<Longrightarrow> \<exists> x. result = IntVal32 x"
    using assms(2,3,4) by (cases op; auto; cases val; auto) 
  from stamp_expr_def have bit64: "b = 64 \<Longrightarrow> \<exists> x. result = IntVal64 x" 
    using assms(2,3,4) by (cases op; auto; cases val; auto) 

  show ?thesis using valid_value.simps(1,2)
    unrestricted_32bit_always_valid unrestricted_64bit_always_valid stamp_expr_def
    bit32 bit64
    by (metis \<open>stamp_expr (UnaryExpr op expr) = unrestricted_stamp (IntegerStamp b lo hi)\<close> assms(4) valid32or64_both)
qed

lemma binary_undef: "v1 = UndefVal \<or> v2 = UndefVal \<Longrightarrow> bin_eval op v1 v2 = UndefVal"
  by (cases op; auto)

lemma binary_obj: "v1 = ObjRef x \<or> v2 = ObjRef y \<Longrightarrow> bin_eval op v1 v2 = UndefVal"
  by (cases op; auto)

lemma binary_eval_bits_equal:
  assumes "result = bin_eval op val1 val2"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value (IntegerStamp b1 lo1 hi1) val1"
  assumes "valid_value (IntegerStamp b2 lo2 hi2) val2"
  shows "b1 = b2"
  using assms 
  by (cases op; cases val1; cases val2; auto) (*slow*)

lemma binary_eval_values:
  assumes "\<exists>x y. result = IntVal32 x \<or> result = IntVal64 y"
  assumes "result = bin_eval op val1 val2"
  shows" \<exists>x32 x64 y32 y64. val1 = IntVal32 x32 \<and> val2 = IntVal32 y32 \<or> val1 = IntVal64 x64 \<and> val2 = IntVal64 y64"
  using assms apply (cases result)
      apply simp apply (cases op; cases val1; cases val2; auto)
    apply (cases op; cases val1; cases val2; auto) by auto+

lemma binary_eval_implies_valud_value:
  assumes "[m,p] \<turnstile> expr1 \<mapsto> val1"
  assumes "[m,p] \<turnstile> expr2 \<mapsto> val2"
  assumes "result = bin_eval op val1 val2"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value (stamp_expr expr1) val1"
  assumes "valid_value (stamp_expr expr2) val2"
  shows "valid_value (stamp_expr (BinaryExpr op expr1 expr2)) result"
proof -
  have is_IntVal: "\<exists> x y. result = IntVal32 x \<or> result = IntVal64 y"
    using assms(1,2,3,4) apply (cases op; auto; cases val1; auto; cases val2; auto)
    by (meson Values.bool_to_val.elims)+
  then have expr1_intstamp: "is_IntegerStamp (stamp_expr expr1)"
    using assms(1,3,4,5) apply (cases "(stamp_expr expr1)"; auto simp: valid_VoidStamp binary_undef)
    using valid_ObjStamp binary_obj apply (metis assms(4))
    using valid_ObjStamp binary_obj by (metis assms(4))
  from is_IntVal have expr2_intstamp: "is_IntegerStamp (stamp_expr expr2)"
    using assms(2,3,4,6) apply (cases "(stamp_expr expr2)"; auto simp: valid_VoidStamp binary_undef)
    using valid_ObjStamp binary_obj apply (metis assms(4))
    using valid_ObjStamp binary_obj by (metis assms(4))
  from expr1_intstamp obtain b1 lo1 hi1 where stamp_expr1_def: "stamp_expr expr1 = (IntegerStamp b1 lo1 hi1)"
    using is_IntegerStamp_def by auto
  from expr2_intstamp obtain b2 lo2 hi2 where stamp_expr2_def: "stamp_expr expr2 = (IntegerStamp b2 lo2 hi2)"
    using is_IntegerStamp_def by auto

  have "\<exists> x32 x64 y32 y64 . (val1 = IntVal32 x32 \<and> val2 = IntVal32 y32) \<or> (val1 = IntVal64 x64 \<and> val2 = IntVal64 y64)"
    using is_IntVal assms(3) binary_eval_values
    by presburger
    
  have "b1 = b2"
    using assms(3,4,5,6) stamp_expr1_def stamp_expr2_def
    using binary_eval_bits_equal
    by auto 
  then have stamp_def: "stamp_expr (BinaryExpr op expr1 expr2) = 
    (case op \<in> fixed_32 of True \<Rightarrow> unrestricted_stamp (IntegerStamp 32 lo1 hi1)| False \<Rightarrow> unrestricted_stamp (IntegerStamp b1 lo1 hi1))"
    using stamp_expr.simps(2) stamp_binary.simps(1)
    using stamp_expr1_def stamp_expr2_def by presburger
  from stamp_expr1_def have bit32: "b1 = 32 \<Longrightarrow> \<exists> x. result = IntVal32 x"
    using assms apply (cases op; cases val1; cases val2; auto) (*slow*)
    by (meson Values.bool_to_val.elims)+
  from stamp_expr1_def have bit64: "b1 = 64 \<and> op \<notin> fixed_32 \<Longrightarrow> \<exists> x y. result = IntVal64 x" 
    using assms apply (cases op; cases val1; cases val2; simp) (*slow*)
    using fixed_32_def by auto+
  from stamp_expr1_def have fixed: "op \<in> fixed_32 \<Longrightarrow> \<exists> x y. result = IntVal32 x" 
    using assms unfolding fixed_32_def apply (cases op; auto)
    apply (cases val1; cases val2; auto)
    using bit32 apply fastforce 
      apply (meson Values.bool_to_val.elims)
     apply (cases val1; cases val2; auto) 
    using bit32 apply fastforce
     apply (meson Values.bool_to_val.elims)
      apply (cases val1; cases val2; auto) 
    using bit32 apply fastforce
    by (meson Values.bool_to_val.elims)

  show ?thesis apply (cases "op \<in> fixed_32") defer using valid_value.simps(1,2)
    unrestricted_32bit_always_valid unrestricted_64bit_always_valid stamp_expr1_def
    bit32 bit64 stamp_def apply auto
    using \<open>\<exists>x32 x64 y32 y64. val1 = IntVal32 x32 \<and> val2 = IntVal32 y32 \<or> val1 = IntVal64 x64 \<and> val2 = IntVal64 y64\<close> assms(5) apply auto[1]
    using fixed by force
qed

lemma stamp_meet_is_valid:
  assumes "valid_value stamp1 val \<or> valid_value stamp2 val"
  assumes "meet stamp1 stamp2 \<noteq> IllegalStamp"
  shows "valid_value (meet stamp1 stamp2) val"
  using assms proof (cases stamp1)
  case VoidStamp
  then show ?thesis
    by (metis Stamp.exhaust assms(1) assms(2) meet.simps(1) meet.simps(37) meet.simps(44) meet.simps(51) meet.simps(58) meet.simps(65) meet.simps(66) meet.simps(67))
next
  case (IntegerStamp b lo hi)
  obtain b2 lo2 hi2 where stamp2_def: "stamp2 = IntegerStamp b2 lo2 hi2"
    by (metis IntegerStamp assms(2) meet.simps(45) meet.simps(52) meet.simps(59) meet.simps(6) meet.simps(65) meet.simps(66) meet.simps(67) unrestricted_stamp.cases)
  then have "b = b2" using meet.simps(2) assms(2) 
    by (metis IntegerStamp)
  then have meet_def: "meet stamp1 stamp2 = (IntegerStamp b (min lo lo2) (max hi hi2))"
    by (simp add: IntegerStamp stamp2_def)
  then show ?thesis proof (cases "b = 32")
    case True
    then obtain x where val_def: "val = IntVal32 x"
      using IntegerStamp assms(1) valid32
      using \<open>b = b2\<close> stamp2_def by blast
    have min: "sint x \<ge> min lo lo2" 
      using val_def
      using IntegerStamp assms(1)
      using stamp2_def by force
    have max: "sint x \<le> max hi hi2" 
      using val_def
      using IntegerStamp assms(1)
      using stamp2_def by force
    from min max show ?thesis
      by (simp add: True meet_def val_def)
  next
    case False
    then have bit64: "b = 64"
      using assms(1) IntegerStamp valid_value.simps
      valid32or64_both
      by (metis \<open>b = b2\<close> stamp2_def)
    then obtain x where val_def: "val = IntVal64 x"
      using IntegerStamp assms(1) valid64
      using \<open>b = b2\<close> stamp2_def by blast
    have min: "sint x \<ge> min lo lo2" 
      using val_def
      using IntegerStamp assms(1)
      using stamp2_def by force
    have max: "sint x \<le> max hi hi2" 
      using val_def
      using IntegerStamp assms(1)
      using stamp2_def by force
    from min max show ?thesis
      by (simp add: bit64 meet_def val_def)
  qed
next
  case (KlassPointerStamp x31 x32)
  then show ?thesis using assms
    by (metis meet.simps(13) meet.simps(14) meet.simps(65) meet.simps(67) unrestricted_stamp.cases valid_value.simps(10) valid_value.simps(11) valid_value.simps(16) valid_value.simps(9))
next
  case (MethodCountersPointerStamp x41 x42)
  then show ?thesis using assms
    by (metis meet.simps(20) meet.simps(21) meet.simps(24) meet.simps(67) unrestricted_stamp.cases valid_value.simps(10) valid_value.simps(11) valid_value.simps(16) valid_value.simps(9))
next
  case (MethodPointersStamp x51 x52)
then show ?thesis using assms
  by (smt (z3) is_stamp_empty.elims(1) meet.simps(27) meet.simps(28) meet.simps(65) meet.simps(67) valid_value.simps(10) valid_value.simps(11) valid_value.simps(16) valid_value.simps(9))
next
  case (ObjectStamp x61 x62 x63 x64)
  then show ?thesis using assms
    using meet.simps(34) by blast
next
  case (RawPointerStamp x71 x72)
  then show ?thesis using assms
    using meet.simps(35) by blast
next
  case IllegalStamp
  then show ?thesis using assms
    using meet.simps(36) by blast
qed


lemma conditional_eval_implies_valud_value:
  assumes "[m,p] \<turnstile> cond \<mapsto> condv"
  assumes "expr = (if IRTreeEval.val_to_bool condv then expr1 else expr2)"
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "val \<noteq> UndefVal"
  assumes "valid_value (stamp_expr cond) condv"
  assumes "valid_value (stamp_expr expr) val"
  shows "valid_value (stamp_expr (ConditionalExpr cond expr1 expr2)) val"
proof -
  have "meet (stamp_expr expr1) (stamp_expr expr2) \<noteq> IllegalStamp"
    using assms apply (cases "stamp_expr expr"; auto)
    using valid_VoidStamp apply blast sorry
  then show ?thesis using stamp_meet_is_valid using stamp_expr.simps(6)
    using assms(2) assms(6) by presburger
qed

lemma stamp_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  shows "valid_value (stamp_expr expr) val"
  using assms proof (induction expr val)
case (UnaryExpr expr val result op)
  then show ?case using unary_eval_implies_valud_value by simp
next
  case (BinaryExpr expr1 val1 expr2 val2 result op)
  then show ?case using binary_eval_implies_valud_value by simp
next
  case (ConditionalExpr cond condv expr expr1 expr2 val)
  then show ?case using conditional_eval_implies_valud_value by simp
next
  case (ParameterExpr x1 x2)
  then show ?case by auto
next
  case (LeafExpr x1 x2)
  then show ?case by auto
next
  case (ConstantExpr x)
  then show ?case by auto
qed

lemma CanonicalizeBinaryProof:
  assumes "CanonicalizeBinaryOp before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeBinaryOp.induct)
  case (binary_const_fold x val1 y val2 val op)
  then show ?case by auto
next
  case (binary_fold_yneutral y c op stampx x stampy)
  obtain xval where x_eval: "[m, p] \<turnstile> x \<mapsto> xval"
    using binary_fold_yneutral.prems(2) by auto
  then have "bin_eval op xval c = xval"
    using neutral_rewrite_helper binary_fold_yneutral.hyps(2-3,6-) stamp_implies_valid_value is_IntegerStamp_def
    sorry (*by (metis ConstantExpr Value.distinct(5) valid_value.simps(34))*)
  then show ?case
    by (metis binary_fold_yneutral.hyps(1) binary_fold_yneutral.prems(1) binary_fold_yneutral.prems(2) x_eval
          BinaryExprE ConstantExprE evalDet)
next
  case (binary_fold_yzero32 y c op stampx x stampy)
  obtain xval where x_eval: "[m, p] \<turnstile> x \<mapsto> xval"
    using binary_fold_yzero32.prems(1) by auto
  then have "bin_eval op xval c = c"
    using annihilator_rewrite_helper binary_fold_yzero32.hyps stamp_implies_valid_value is_IntegerStamp_def
    sorry
  then show ?case
    by (metis BinaryExprE ConstantExprE binary_fold_yzero32.hyps(1) binary_fold_yzero32.prems(1) binary_fold_yzero32.prems(2) evalDet x_eval)

next
  case (binary_fold_yzero64 y c op stampx x stampy)
  obtain xval where x_eval: "[m, p] \<turnstile> x \<mapsto> xval"
    using binary_fold_yzero64.prems(1) by auto
  then have "bin_eval op xval c = c"
    using annihilator_rewrite_helper
    sorry
  then show ?case
    by (metis BinaryExprE ConstantExprE binary_fold_yzero64.hyps(1) 
        binary_fold_yzero64.prems(1) binary_fold_yzero64.prems(2) evalDet x_eval)

next
  case (binary_idempotent op x)
  obtain xval where x_eval: "[m, p] \<turnstile> x \<mapsto> xval"
    using binary_idempotent.prems(1) by auto
  then have "bin_eval op xval xval = xval"
    using idempotent_rewrite_helper binary_idempotent.hyps 
    sorry
  then show ?case
    by (metis BinaryExprE binary_idempotent.prems(1) binary_idempotent.prems(2) evalDet x_eval)

qed

lemma CanonicalizeUnaryProof:
  assumes "CanonicalizeUnaryOp before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeUnaryOp.induct)
  case (unary_const_fold val' op val)
  then show ?case by auto
qed

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
      stamp_implies_valid_value 
    by (auto; metis)
next
  case (mul_negate64 y x lo hi)
  then show ?case 
    using ConstantExprE BinaryExprE bin_eval.simps evalDet mul_rewrite_helper 
      stamp_implies_valid_value
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
        evalDet stamp_implies_valid_value intval_add_sym add_rewrites_helper(1))
next
  case (add_ysub y a x stampa stampx)
  then show ?case 
    by (metis is_IntegerStamp_def add_ysub.hyps add_ysub.prems evalDet BinaryExprE Stamp.sel(1) 
        bin_eval.simps(1) bin_eval.simps(3) stamp_implies_valid_value intval_add_sym add_rewrites_helper(2))
next
  case (add_xnegate nx x stampx stampy y)
  then show ?case 
    by (smt (verit, del_insts) BinaryExprE Stamp.sel(1) UnaryExprE add_rewrites_helper(4) 
        bin_eval.simps(1) bin_eval.simps(3) evalDet stamp_implies_valid_value intval_add_sym is_IntegerStamp_def unary_eval.simps(2))
next
  case (add_ynegate ny y stampx x stampy)
  then show ?case 
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE add_rewrites_helper(4) bin_eval.simps(1) 
        bin_eval.simps(3) evalDet stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(2))
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
      stamp_implies_valid_value sub_same32.hyps(1) sub_same32.hyps(2)
    by (auto; metis)
next
  case (sub_same64 stampx x lo hi)
  show ?case     
    using ConstantExprE BinaryExprE  bin_eval.simps evalDet sub_same64.prems sub_single_rewrites_helper 
      stamp_implies_valid_value sub_same64.hyps(1) sub_same64.hyps(2)
    by (auto; metis)
next
  case (sub_left_add1 x a b stampa stampb)
  then show ?case
    by (metis BinaryExprE Stamp.collapse(1) bin_eval.simps(1) bin_eval.simps(3) evalDet 
        stamp_implies_valid_value sub_rewrites_helper(1))
next
  case (sub_left_add2 x a b stampa stampb)
  then show ?case
    by (metis BinaryExprE Stamp.collapse(1) bin_eval.simps(1) bin_eval.simps(3) evalDet 
        stamp_implies_valid_value sub_rewrites_helper(2))
next
  case (sub_left_sub x a b stampa stampb)
  then show ?case
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(3) evalDet
        stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(3) unary_eval.simps(2))
next
  case (sub_right_add1 y a b stampa stampb)
  then show ?case
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(1) bin_eval.simps(3) evalDet
        stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(4) unary_eval.simps(2))
next
  case (sub_right_add2 y a b stampa stampb)
  then show ?case
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(1) bin_eval.simps(3) evalDet
        stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(5) unary_eval.simps(2))
next
  case (sub_right_sub y a b stampa stampb)
  then show ?case
    by (metis BinaryExprE Stamp.sel(1) bin_eval.simps(3) evalDet
        stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(6))
next
  case (sub_xzero32 stampx x lo hi)
  then show ?case     
    using ConstantExprE BinaryExprE  bin_eval.simps evalDet sub_xzero32.prems sub_single_rewrites_helper 
      stamp_implies_valid_value sub_xzero32.hyps(1) sub_xzero32.hyps(2)
    by (auto; metis)
next
  case (sub_xzero64 stampx x lo hi)
  then show ?case     
    using ConstantExprE BinaryExprE  bin_eval.simps evalDet sub_xzero64.prems sub_single_rewrites_helper 
      stamp_implies_valid_value sub_xzero64.hyps(1) sub_xzero64.hyps(2)
    by (auto; metis)
next
  case (sub_y_negate nb b stampa a stampb)
  then show ?case
    by (smt (verit, best) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(1) bin_eval.simps(3) evalDet
        stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(7) unary_eval.simps(2))
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
    by (metis UnaryExprE evalDet stamp_implies_valid_value is_IntegerStamp_def negate_negate_helper unary_eval.simps(2))
next
  case (negate_sub e x y stampx stampy)
  thus ?case
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(3) evalDet stamp_implies_valid_value
        is_IntegerStamp_def negate_xsuby_helper unary_eval.simps(2))
qed

(* TODO: a better name for this? *)
lemma word_helper:
  shows "\<And> x :: 32 word. \<not>(- x <s 0 \<and> x <s 0)" 
  and   "\<And> x :: 64 word. \<not>(- x <s 0 \<and> x <s 0)"
  and   "\<And> x :: 32 word. \<not> - x <s 0 \<and> \<not> x <s 0 \<Longrightarrow> 2 * x = 0"
  and   "\<And> x :: 64 word. \<not> - x <s 0 \<and> \<not> x <s 0 \<Longrightarrow> 2 * x = 0"
  apply (case_tac[!] "x")
  apply auto+
  sorry

(* abs(-x) = abs(x) *)
(* abs(abs(x)) = abs(x) 
lemma abs_rewrite_helper:
  assumes "valid_value (IntegerStamp b lox hix) x"
  shows "intval_abs (intval_negate x) = intval_abs x"
  and "intval_abs (intval_abs x) = intval_abs x"
  apply (case_tac[!] "x")
  using word_helper apply auto+
  done
*)

lemma abs_abs_is_abs:
  assumes "valid_value (IntegerStamp b lox hix) x"
  shows "intval_abs (intval_abs x) = intval_abs x"
  using word_helper
  by (metis assms intval_abs.simps(1) intval_abs.simps(2) valid32or64_both) 

lemma abs_neg_is_neg:
  assumes "valid_value (IntegerStamp b lox hix) x"
  shows "intval_abs (intval_negate x) = intval_abs x"
  apply (case_tac[!] "x")
  using word_helper apply auto+
  done


(*
lemma CanonicalizeAbsAbs:
  assumes vv: "is_IntegerStamp (stamp_expr e)"
  assumes "[m, p] \<turnstile> UnaryExpr UnaryAbs (UnaryExpr UnaryAbs e) \<mapsto> v"
  shows "[m, p] \<turnstile> UnaryExpr UnaryAbs e \<mapsto> v"
  by (metis UnaryExprE abs_abs_is_abs assms(2) stamp_implies_valid_value
      is_IntegerStamp_def unary_eval.simps(1) vv)

lemma CanonicalizeAbsNeg:
  assumes vv: "is_IntegerStamp (stamp_expr e)"
  assumes "[m, p] \<turnstile> UnaryExpr UnaryAbs (UnaryExpr UnaryNeg e) \<mapsto> v"
  shows "[m, p] \<turnstile> UnaryExpr UnaryAbs e \<mapsto> v"
  using UnaryExprE abs_neg_is_neg assms(2) stamp_implies_valid_value
      is_IntegerStamp_def unary_eval.simps(2) vv
  by (smt (verit, ccfv_threshold) evaltree.simps unary_eval.simps(1))
  
lemma CanonicalizeAbsProof:
  assumes "CanonicalizeAbs before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeAbs.induct)
  case (abs_abs ax x)
  then show ?case
    by (metis UnaryExprE abs_rewrite_helper(2) evalDet stamp_implies_valid_value is_IntegerStamp_def
        unary_eval.simps(1))
next
  case (abs_neg nx x)
  then show ?case
    by (metis UnaryExprE abs_rewrite_helper(1) evalDet stamp_implies_valid_value is_IntegerStamp_def
        unary_eval.simps(1) unary_eval.simps(2))
qed
*)
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
        stamp_implies_valid_value unary_eval.simps(3))
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
        stamp_implies_valid_value is_IntegerStamp_def)
next
  case (and_demorgans nx x ny y stampx stampy)
  then show ?case
    by (smt (z3) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(4) bin_eval.simps(5) 
        demorgans_rewrites_helper(1) evalDet stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(3))
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
        stamp_implies_valid_value is_IntegerStamp_def)
next
  case (or_demorgans nx x ny y stampx stampy)
  then show ?case
    by (smt (z3) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(4) bin_eval.simps(5) demorgans_rewrites_helper(2)
        evalDet stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(3))
qed

lemma stamps_touch_but_not_less_than_implies_equal:
  "\<lbrakk>valid_value stampx x;
    valid_value stampy y;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy;
    stpi_upper stampx = stpi_lower stampy;
    \<not> val_to_bool (intval_less_than x y)\<rbrakk> \<Longrightarrow> x = y" 
  using valid32or64_both intval_equals.simps(1-2) intval_less_than.simps(1-2) val_to_bool.simps(1)
  sorry

lemma disjoint_stamp_implies_less_than:
  "\<lbrakk>valid_value stampx x;
    valid_value stampy y;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy;
    stpi_upper stampx < stpi_lower stampy\<rbrakk> 
  \<Longrightarrow> val_to_bool(intval_less_than x y)"
  sorry

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
  obtain xval where xeval: "[m,p] \<turnstile> x \<mapsto> xval"
    using cond_eq.hyps(1) cond_eq.prems(1) by blast
  obtain yval where yeval: "[m,p] \<turnstile> y \<mapsto> yval"
    using cond_eq.prems(2) by auto
  show ?case proof (cases "xval = yval")
    case True
    then show ?thesis
      by (smt (verit, ccfv_threshold) ConditionalExprE cond_eq.prems(1) cond_eq.prems(2) evalDet xeval yeval)
  next
    case False
    then have "\<not>(val_to_bool(intval_equals xval yval))"
      using ConstantExpr Value.distinct(9) valid_value.simps stamp_implies_valid_value
      apply (cases "intval_equals xval yval")
      using IRTreeEval.val_to_bool.simps(2) apply presburger sorry
    then have "res = yval"
      by (smt (verit, ccfv_threshold) BinaryExprE ConditionalExprE bin_eval.simps(10) cond_eq.hyps(1) cond_eq.prems(1) evalDet xeval yeval)
    then show ?thesis
      using cond_eq.prems(1) cond_eq.prems(2) xeval yeval evalDet by auto
  qed
next
  case (condition_bounds_x c x y stampx stampy)
  obtain xval where xeval: "[m,p] \<turnstile> x \<mapsto> xval"
    using condition_bounds_x.prems(2) by auto
  obtain yval where yeval: "[m,p] \<turnstile> y \<mapsto> yval"
    using condition_bounds_x.hyps(1) condition_bounds_x.prems(1) by blast
  then show ?case proof (cases "val_to_bool(intval_less_than xval yval)")
    case True
    then show ?thesis
      by (smt (verit, best) BinaryExprE ConditionalExprE bin_eval.simps(11) condition_bounds_x.hyps(1) condition_bounds_x.prems(1) condition_bounds_x.prems(2) evalDet xeval yeval)
  next
    case False
    then have "stpi_upper stampx = stpi_lower stampy"
      by (metis False condition_bounds_x.hyps(4) order.not_eq_order_implies_strict
          disjoint_stamp_implies_less_than condition_bounds_x.hyps(2) condition_bounds_x.hyps(3) condition_bounds_x.hyps(6)
          stamp_implies_valid_value xeval yeval)
    then have "(xval = yval)"
      by (metis False condition_bounds_x.hyps(2-3,6) stamp_implies_valid_value
          stamps_touch_but_not_less_than_implies_equal xeval yeval)
    then have "res = xval \<and> res' = xval"
      using ConditionalExprE condition_bounds_x.prems(1) \<open>[m,p] \<turnstile> x \<mapsto> res'\<close> evalDet xeval yeval
      by force
    then show ?thesis by simp
  qed
next
  case (condition_bounds_y c x y stampx stampy)
  obtain xval where xeval: "[m,p] \<turnstile> x \<mapsto> xval"
    using condition_bounds_y.hyps(1) condition_bounds_y.prems(1) by auto
  obtain yval where yeval: "[m,p] \<turnstile> y \<mapsto> yval"
    using condition_bounds_y.hyps(1) condition_bounds_y.prems(1) by blast
  then show ?case proof (cases "val_to_bool(intval_less_than xval yval)")
    case True
    then show ?thesis
      by (smt (verit, best) BinaryExprE ConditionalExprE bin_eval.simps(11) condition_bounds_y.hyps(1) condition_bounds_y.prems(1) condition_bounds_y.prems(2) evalDet xeval yeval)
  next
    case False
    have "stpi_upper stampx = stpi_lower stampy"
      by (metis False condition_bounds_y.hyps(4) order.not_eq_order_implies_strict
          disjoint_stamp_implies_less_than condition_bounds_y.hyps(2) condition_bounds_y.hyps(3)
          condition_bounds_y.hyps(6) stamp_implies_valid_value xeval yeval)
    then have "(xval = yval)"
      by (metis False condition_bounds_y.hyps(2-3,6)
          stamp_implies_valid_value stamps_touch_but_not_less_than_implies_equal xeval yeval)
    then have "res = yval \<and> res' = yval"
      using ConditionalExprE condition_bounds_y.prems(1) \<open>[m,p] \<turnstile> y \<mapsto> res'\<close> evalDet xeval yeval
      by force
    then show ?thesis by simp
  qed
next
  case (negate_condition nc c stampc lo hi stampx x stampy y)
  obtain cval where ceval: "[m,p] \<turnstile> c \<mapsto> cval"
    using negate_condition.prems(2) by auto
  obtain ncval where nceval: "[m,p] \<turnstile> nc \<mapsto> ncval"
    using negate_condition.prems negate_condition.prems by blast
  then show ?case using assms proof (cases "(val_to_bool ncval)")
    case True
    obtain xval where xeval: "[m,p] \<turnstile> x \<mapsto> xval"
      by (metis (full_types) ConditionalExprE nceval evalDet True negate_condition.prems(1))
    then have "res = xval"
      by (metis (full_types) ConditionalExprE True evalDet nceval negate_condition.prems(1))
    have "c \<noteq> nc"
      by (simp add: negate_condition.hyps(1))
    then have "\<not>(val_to_bool cval)"
      by (metis IRTreeEval.val_to_bool.elims(2) IRTreeEval.val_to_bool.simps(1) True UnaryExprE ceval evalDet nceval negate_condition.hyps(1) unary_eval.simps(4))
    then have "res' = xval"
      using nceval ceval True negate_condition(1) negate_condition(9)
      by (metis (full_types) ConditionalExprE evalDet xeval)
    then show ?thesis
      by (simp add: \<open>res = xval\<close>)
  next
    case False
    obtain yval where yeval: "[m,p] \<turnstile> y \<mapsto> yval"
      by (metis (full_types) ConditionalExprE nceval evalDet False negate_condition.prems(1))
    then have "res = yval" 
      using False nceval negate_condition.prems(1) evaltree.ConditionalExpr yeval evalDet
      by (metis (full_types) ConditionalExprE)
    moreover have "val_to_bool(cval)" 
      by (metis False UnaryExprE ceval nceval negate_condition.hyps(1-3) unary_eval.simps(4)
          IRTreeEval.val_to_bool.simps(1) evalDet IRTreeEval.bool_to_val.simps(2)
          stamp_implies_valid_value valid_int32 zero_neq_one)
    moreover have "res' = yval"
      using calculation(2) ceval negate_condition.prems evaltree.ConditionalExpr yeval evalDet  unary_eval.simps(4)
      by (metis (full_types) ConditionalExprE)
    ultimately show ?thesis by simp
  qed
next
  case (const_true c val t f)
  then show ?case using evalDet by auto
next
  case (const_false c val t f)
  then show ?case using evalDet by auto
qed

end