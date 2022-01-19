theory Markup
  imports Semantics.IRTreeEval
begin

datatype 'a Rewrite =
  Transform 'a 'a |
  Conditional 'a 'a "bool" |
  Sequential "'a Rewrite" "'a Rewrite" |
  Transitive "'a Rewrite"

notation ConditionalExpr ("_ ? _ : _")

ML_file \<open>markup.ML\<close>

syntax "_constantValues" :: "term \<Rightarrow> term" ("const _" 120)
parse_translation \<open> [( @{syntax_const "_constantValues"} , DSL_Markup.const_expr)] \<close>

syntax "_binEquals" :: "term \<Rightarrow> term \<Rightarrow> term" ("_ == _" 100)
parse_translation \<open> [( @{syntax_const "_binEquals"} , DSL_Markup.equals_expr)] \<close>

syntax "_expandNodes" :: "term \<Rightarrow> term" ("exp[_]")
parse_translation \<open> [( @{syntax_const "_expandNodes"} , DSL_Markup.markup_expr)] \<close>

syntax "_baseTransform" :: "term \<Rightarrow> term \<Rightarrow> term" ("_ \<mapsto> _" 10)
parse_translation \<open> [( @{syntax_const "_baseTransform"} , DSL_Markup.rewrite)] \<close>

syntax "_conditionalTransform" :: "term \<Rightarrow> term \<Rightarrow> term \<Rightarrow> term" ("_ \<mapsto> _ when _" 70)
parse_translation \<open> [( @{syntax_const "_conditionalTransform"} , DSL_Markup.conditional_rewrite)] \<close>

end