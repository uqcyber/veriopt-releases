theory ValidationSnippets
  imports
    Tests.UnitTesting
    Graph.Values
    Optimizations.CanonicalizationTree
begin

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

text_raw \<open>\Snip{StepSemantics}%\<close>
text \<open>
@{thm[display,margin=60] intval_mod.simps(1)}

\induct{@{thm[mode=Rule] step.SignedRemNode [no_vars]}}{eval:rem}
\<close>
text_raw \<open>\EndSnip\<close>

(* moduloSnippet not checked in
text_raw \<open>\Snip{ModuloSnippet}%
@{thm[display,margin=80] moduloSnippet_def}
\EndSnip\<close>
*)

text_raw \<open>\Snip{ModuloTestSnippet}%
@{theory_text "static_test moduloSnippet [(IntVal 32 (1)), (Intval 32 (-2147483648))] (IntVal 32 (1))"}
\EndSnip\<close>


text_raw \<open>\Snip{SampleCanonicalizations}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] CanonicalizeAdd.add_xsub [no_vars]}}{canon:addxsub}
\induct{@{thm[mode=Rule] CanonicalizeAdd.add_ysub [no_vars]}}{canon:addysub}
\induct{@{thm[mode=Rule] CanonicalizeAdd.add_xnegate [no_vars]}}{canon:addxnegate}
\induct{@{thm[mode=Rule] CanonicalizeAdd.add_ynegate [no_vars]}}{canon:addynegate}
\induct{@{thm[mode=Rule] CanonicalizeConditional.eq_branches [no_vars]}}{canon:eqbranch}
\induct{@{thm[mode=Rule] CanonicalizeConditional.cond_eq [no_vars]}}{canon:condeq}
\induct{@{thm[mode=Rule] CanonicalizeConditional.condition_bounds_x [no_vars]}}{canon:conditionboundsx}
\induct{@{thm[mode=Rule] CanonicalizeConditional.condition_bounds_y [no_vars]}}{canon:conditionboundsy}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>

text_raw \<open>\Snip{SampleCanonicalizations2}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] CanonicalizeConditional.negate_condition [no_vars]}}{canon:addxsub}
\induct{@{thm[mode=Rule] CanonicalizeConditional.const_true [no_vars]}}{canon:addysub}
\induct{@{thm[mode=Rule] CanonicalizeConditional.const_false [no_vars]}}{canon:addxnegate}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_same [no_vars]}}{canon:addynegate}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_distinct [no_vars]}}{canon:eqbranch}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_add_first_both_same [no_vars]}}{canon:condeq}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_add_first_second_same [no_vars]}}{canon:conditionboundsx}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_add_second_first_same [no_vars]}}{canon:conditionboundsy}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>

text_raw \<open>\Snip{SampleCanonicalizations3}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_add_second_both__same [no_vars]}}{canon:addxsub}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_sub_first_both_same [no_vars]}}{canon:addysub}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_sub_second_both_same [no_vars]}}{canon:addxnegate}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_left_contains_right1 [no_vars]}}{canon:addynegate}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_left_contains_right2 [no_vars]}}{canon:eqbranch}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_right_contains_left1 [no_vars]}}{canon:condeq}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_right_contains_left2 [no_vars]}}{canon:conditionboundsx}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_left_contains_right3 [no_vars]}}{canon:conditionboundsx}
\induct{@{thm[mode=Rule] CanonicalizeIntegerEquals.int_equals_right_contains_left3 [no_vars]}}{canon:conditionboundsy}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>


text_raw \<open>\Snip{SampleCanonicalizations4}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] CanonicalizeOr.or_same [no_vars]}}{canon:addxsub}
\induct{@{thm[mode=Rule] CanonicalizeOr.or_demorgans [no_vars]}}{canon:addysub}
\induct{@{thm[mode=Rule] CanonicalizeAnd.and_same [no_vars]}}{canon:addxnegate}
\induct{@{thm[mode=Rule] CanonicalizeAnd.and_demorgans [no_vars]}}{canon:addynegate}
\induct{@{thm[mode=Rule] CanonicalizeNot.not_not [no_vars]}}{canon:eqbranch}
\induct{@{thm[mode=Rule] CanonicalizeAbs.abs_abs [no_vars]}}{canon:condeq}
\induct{@{thm[mode=Rule] CanonicalizeAbs.abs_abs [no_vars]}}{canon:conditionboundsx}
\induct{@{thm[mode=Rule] CanonicalizeNegate.negate_negate [no_vars]}}{canon:conditionboundsx}
\induct{@{thm[mode=Rule] CanonicalizeNegate.negate_negate [no_vars]}}{canon:conditionboundsy}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>


text_raw \<open>\Snip{SampleCanonicalizations5}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] CanonicalizeSub.sub_same32 [no_vars]}}{canon:addxsub}
\induct{@{thm[mode=Rule] CanonicalizeSub.sub_same64 [no_vars]}}{canon:addysub}
\induct{@{thm[mode=Rule] CanonicalizeSub.sub_left_add1 [no_vars]}}{canon:addxnegate}
\induct{@{thm[mode=Rule] CanonicalizeSub.sub_left_add2 [no_vars]}}{canon:addynegate}
\induct{@{thm[mode=Rule] CanonicalizeSub.sub_left_sub [no_vars]}}{canon:eqbranch}
\induct{@{thm[mode=Rule] CanonicalizeSub.sub_right_add1 [no_vars]}}{canon:condeq}
\induct{@{thm[mode=Rule] CanonicalizeSub.sub_right_add2 [no_vars]}}{canon:conditionboundsx}
\induct{@{thm[mode=Rule] CanonicalizeSub.sub_right_sub [no_vars]}}{canon:conditionboundsy}
\induct{@{thm[mode=Rule] CanonicalizeSub.sub_xzero32 [no_vars]}}{canon:conditionboundsy}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>

text_raw \<open>\Snip{SampleCanonicalizations6}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] CanonicalizeSub.sub_xzero64 [no_vars]}}{canon:addxsub}
\induct{@{thm[mode=Rule] CanonicalizeSub.sub_y_negate [no_vars]}}{canon:addysub}
\induct{@{thm[mode=Rule] CanonicalizeMul.mul_negate32 [no_vars]}}{canon:addxnegate}
\induct{@{thm[mode=Rule] CanonicalizeMul.mul_negate64 [no_vars]}}{canon:addynegate}
\induct{@{thm[mode=Rule] CanonicalizeUnaryOp.unary_const_fold [no_vars]}}{canon:eqbranch}
\induct{@{thm[mode=Rule] CanonicalizeBinaryOp.binary_const_fold [no_vars]}}{canon:condeq}
\induct{@{thm[mode=Rule] CanonicalizeBinaryOp.binary_fold_yneutral [no_vars]}}{canon:conditionboundsx}
\induct{@{thm[mode=Rule] CanonicalizeBinaryOp.binary_fold_yzero32 [no_vars]}}{canon:conditionboundsy}
\induct{@{thm[mode=Rule] CanonicalizeBinaryOp.binary_fold_yzero64 [no_vars]}}{canon:conditionboundsy}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>




end