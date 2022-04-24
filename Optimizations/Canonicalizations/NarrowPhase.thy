theory NarrowPhase
  imports
    Common
begin
(*
lemma eval_not_undef:
  "([m,p] \<turnstile> e \<mapsto> v) \<longrightarrow> v \<noteq> UndefVal"
  by (induction e; auto)
*)

section \<open>Optimizations for Narrow/Widen Nodes\<close>

text \<open>Our first goal in this section is to explore the known (fixed) bug
  in narrowing / widening within equality comparisons, in Issue 2011.\<close>

context
  includes bit_operations_syntax
begin


text \<open>Some of the CodeUtil methods from the GraalVM compiler"\<close>

(*
//    public static long signExtend(long value, int inputBits) {
//        if (inputBits < 64) {
//            return (value >>> inputBits - 1 & 1L) == 1L 
//                   ? value | -1L << inputBits 
//                   : value & ~(-1L << inputBits);
//        } else {
//            return value;
//        }
//    }
*)
definition CodeUtil_signExtend :: "int64 \<Rightarrow> nat \<Rightarrow> int64" where
  "CodeUtil_signExtend value inputBits =
    (if inputBits < 64
     then (if ((value >>> (inputBits - 1)) AND 1) = 1
          then value OR ((-1) << inputBits)
          else value AND NOT((-1) << inputBits))
     else value)"

(* temporary version for 32-bit in and out. *)
definition CodeUtil_signExtend32 :: "int32 \<Rightarrow> nat \<Rightarrow> int32" where
  "CodeUtil_signExtend32 value inputBits =
    (if inputBits < 64
     then (if ((value >>> (inputBits - 1)) AND 1) = 1
          then value OR ((-1) << inputBits)
          else value AND NOT((-1) << inputBits))
     else value)"

(*
//     public static long zeroExtend(long value, int inputBits) {
//         return inputBits < 64 ? value & ~(-1L << inputBits) : value;
//     }
*)
definition CodeUtil_zeroExtend :: "int64 \<Rightarrow> nat \<Rightarrow> int64" where
  "CodeUtil_zeroExtend value inputBits =
    (if inputBits < 64
     then value AND NOT((-1) << inputBits)
     else value)"

(*
//     public static long narrow(long value, int resultBits) {
//         long ret = value & mask(resultBits);
//         return signExtend(ret, resultBits);
//     }
*)
definition CodeUtil_narrow :: "int64 \<Rightarrow> nat \<Rightarrow> int64" where
  "CodeUtil_narrow value resultBits =
    signed_take_bit (resultBits - 1) (value AND mask resultBits)"

end

lemma dummy: "(0 :: int32) + 1 = 1"
  by simp


subsection \<open>Example tests of the CodeUtil narrow and widen operators\<close>

experiment begin
corollary "sint(CodeUtil_signExtend 0x00FF 64) = 255" by code_simp
corollary "sint(CodeUtil_signExtend 0x007F 8)  = 127" by code_simp
corollary "sint(CodeUtil_signExtend 0x00FF 8)  = -1" by code_simp
corollary "sint(CodeUtil_signExtend 0x0000 1)  = 0" by code_simp
corollary "sint(CodeUtil_signExtend 0x0001 1)  = -1" by code_simp

corollary "sint(CodeUtil_zeroExtend 0x00FF 64) = 255" by code_simp
corollary "sint(CodeUtil_zeroExtend 0x007F 8)  = 127" by code_simp
corollary "sint(CodeUtil_zeroExtend 0x00FF 8)  = 255" by code_simp
corollary "sint(CodeUtil_zeroExtend 0x0000 1)  = 0" by code_simp
corollary "sint(CodeUtil_zeroExtend 0x0001 1)  = 1" by code_simp

corollary "sint(CodeUtil_narrow 0xFFFF 8) = -1" by code_simp
corollary "sint(CodeUtil_narrow 0xFF7F 8) = 127" by code_simp
corollary "sint(CodeUtil_narrow 0x00FF 8) = -1" by code_simp
corollary "sint(CodeUtil_narrow 0x0000 1) = 0" by code_simp
corollary "sint(CodeUtil_narrow 0x0001 1) = -1" by code_simp
end




phase Issue2011Phase 
  terminating size
begin

fun isDefaultForKind :: "Value \<Rightarrow> bool" where
  "isDefaultForKind (IntVal32 val) = (val = 0)" |
  "isDefaultForKind (IntVal64 val) = (val = 0)" |
  "isDefaultForKind _ = False"


lemma shift_n_eq_bit_n:
  fixes val :: \<open>'a::len word\<close>
  shows "(and (val >>> n) 1 = 1) = bit val n"
  by (simp add: bit_iff_and_drop_bit_eq_1 shiftr_def)

lemma neg1_shift_eq_mask:
  fixes val :: \<open>'a::len word\<close>
  assumes "n < LENGTH('a)"
  assumes "0 < n"
  shows "(- 1 << n) = not (mask (n - 1))" (is "?A = ?B")
proof (rule bit_eqI)
  fix pos
  assume "possible_bit TYPE('b) pos"
  show "bit (- 1 << n) pos = bit (not (mask (n - 1))) pos"
  proof (cases "pos < n")
    case True
    then have "bit (- 1 << n) pos = False"
      by (simp add: bit_push_bit_iff shiftl_def)
    moreover have "bit (not (mask (n - 1))) pos = False"
      sorry (* apply (induction pos) *)
    then show ?thesis
      using calculation by blast
  next
    case False
    then have "bit (- 1 << n) pos = True"
      sorry
    moreover have "bit (not (mask (n - 1))) pos = True"
      by (metis False One_nat_def Suc_pred assms(2) bit_imp_possible_bit bit_mask_iff bit_not_iff calculation less_SucI)
    then show ?thesis
      using calculation by blast
  qed
qed

value "bit (- (1 :: int32) << 8) 8"
value "bit (not (mask 7) :: int32) 6"


lemma narrow_reverse_pos:
  assumes "and (val32 >>> 7) 1 \<noteq> 1"
  assumes "val = IntVal32 val32"
  shows "(i32 = un_IntVal32(intval_narrow 32 8 val))
        \<longleftrightarrow> (and i32 (not (- 1 << 8)) = un_IntVal32 val)"
  unfolding assms intval_narrow.simps narrow_helper.simps
  apply simp
  oops

(* this is where the Issue2011 bug should appear. *)
lemma narrow_reverse_neg:
  assumes "and (val32 >>> 7) 1 = 1"
  assumes "val = IntVal32 val32"
  shows "(i32 = un_IntVal32(intval_narrow 32 8 val))
        \<longleftrightarrow> (or i32 (- 1 << 8) = un_IntVal32 val)"
  unfolding assms intval_narrow.simps narrow_helper.simps signed_take_bit_def
  using assms apply simp
  unfolding shift_n_eq_bit_n apply simp
  (* TODO: use thm neg1_shift_eq_mask to rewrite (- 1 << 8) *)
  oops


lemma unfold_ex_let: "(\<exists>x. x=E \<and> P) = (let x=E in P)"
  by force
  
lemma unfold_ex2_let: "(\<exists>x y. x=E \<and> P x y) = (let x=E in (\<exists>y. P x y))"
  by force

lemma unfold_ex2_ex_let: "(\<exists>y. (\<exists>x. (R x y \<and> y=E x \<and> Q x y)) \<and> P y) = (\<exists>x'. (let y=E x' in (R x' y \<and> Q x' y \<and> P y)))"
  by metis

lemma unfold_ex_bubble_out: "(P \<and> (\<exists>x. Q x) \<and> R) = (\<exists>x. (Q x \<and> P \<and> R))"
  by auto

(* use context assumptions about definedness to deduce int size *)
lemma eq_must_be_int32:
  assumes "intval_equals (IntVal32 a) b \<noteq> UndefVal"
  shows "(intval_equals (IntVal32 a) b = intval_equals (IntVal32 c) d)
         = ((a = un_IntVal32 b) \<longleftrightarrow> (c = un_IntVal32 d))"
proof (rule iffI)
  assume 1: "(intval_equals (IntVal32 a) b = intval_equals (IntVal32 c) d)"
  obtain bv where "b = IntVal32 bv" 
    using assms intval_eq32 is_IntVal32_def by blast 
  then show "(a = un_IntVal32 b) \<longleftrightarrow> (c = un_IntVal32 d)"
    using 1 assms intval_eq32 is_IntVal32_def by fastforce 
next
  assume 2: "(a = un_IntVal32 b) \<longleftrightarrow> (c = un_IntVal32 d)"
  then have 3: "bool_to_val (a = un_IntVal32 b) = bool_to_val (c = un_IntVal32 d)"
    by simp
  obtain bv where "b = IntVal32 bv" 
    using assms intval_eq32 is_IntVal32_def by blast
  then have "intval_equals (IntVal32 c) d \<noteq> UndefVal"
    using assms sorry
  then have "intval_equals (IntVal32 a) b = intval_equals (IntVal32 c) d"
    using 3 assms sorry
  
  then show "(intval_equals (IntVal32 a) b = intval_equals (IntVal32 c) d)"
    using 2 
    oops


(* we first investigate the case of narrowing from 32 to 8 bits *)

optimization Issue2011_Bug:
  "(BinaryExpr BinIntegerEquals
      (ConstantExpr (IntVal32 value))
      (UnaryExpr (UnaryNarrow inBits outBits) expr))
   \<longmapsto>
   (BinaryExpr BinIntegerEquals
      (ConstantExpr (IntVal32 (CodeUtil_signExtend32 value outBits)))
      expr)
   when (inBits = 32 \<and> outBits = 8)"
   apply unfold_optimization
  apply (rule impI)
  subgoal premises 1 
  unfolding le_expr_def unfold_evaltree bin_eval.simps unary_eval.simps
   apply (rule allI impI)+
  unfolding ex_neg_all_pos unfold_ex_bubble_out
  subgoal premises 2 for m p v x y ev
      apply (rule exI[of _ "IntVal32 (CodeUtil_signExtend32 value outBits)"]; rule exI[of _ ev])
      unfolding CodeUtil_signExtend32_def 
      apply (simp add: 1 2) (*  eq_must_be_int32) *)
      unfolding imp_conjL[symmetric]

      unfolding intval_equals.simps imp_conjL[symmetric]
      oops

  
(* other side-conditions in the code:
  NB. 'convert' and narrowNode are the unary narrow expr.

  !(narrowNode.getInputBits() > 32 && !constant.isDefaultForKind())
   smallestCompareWidth != null && 
     intStamp.getBits() >= smallestCompareWidth

  (convert.preservesOrder(condition, constant, constantReflection))
  // then calculate reverseConverted:
  (reverseConverted != null && convert.convert(reverseConverted, constantReflection).equals(constant))

  (ConstantExpr newConstant) is: 
    return ConstantNode.forConstant(convert.getValue().stamp(view), reverseConverted, metaAccess);
*)


(*

optimization e:
  "x * (const c) \<longmapsto> x << (const n) when (n = intval_log2 c \<and> in_bounds n 0 32)"
   apply unfold_optimization apply simp using e_intval
  using BinaryExprE ConstantExprE bin_eval.simps(2,7) sorry


  nitpick [unary_ints]
  nitpick [binary_ints, bits=16]
  But these give error: 
    Unsupported case: representation function on "Int.int"

+//   && supported   // ie. (convert.stamp as IntegerStamp).getBits() >= smallestCompareWidth
+//   && let value = ((PrimitiveConstant) konstant).asLong()
+//   && let narrow = convert
+//   && let inputBits = narrow.inputBits
# Ian: instead shift left then right
+//   && let reverseConverted = if (convert.inputBits < 64)
+//                             then if (value >>> inputBits - 1 & 1L) == 1L
+//                                  then value | -1L << inputBits
+//                                  else value & ~(-1L << inputBits)
+//                             else value
+//   && reverseConverted != null   // I don't think it can be null?
+//   && narrow.convert(reverseConverted, constantReflection).equals(konstant))
+//   && !GeneratePIC.getValue(options))
+//   && let newConstant = ConstantNode.forConstant(narrow.getValue().stamp(view), reverseConverted, metaAccess)
+//   && newConstant != null
*)

end
