section \<open>Optization DSLs\<close> (* first theory in list, not related to file contents *)

theory Markup
  imports Semantics.IRTreeEval Snippets.Snipping
begin

datatype 'a Rewrite =
  Transform 'a 'a ("_ \<longmapsto> _" 10) |
  Conditional 'a 'a "bool" ("_ \<longmapsto> _ when _" 70) |
  Sequential "'a Rewrite" "'a Rewrite" |
  Transitive "'a Rewrite"

datatype 'a ExtraNotation =
  ConditionalNotation 'a 'a 'a ("_ ? _ : _") |
  EqualsNotation 'a 'a ("_ eq _") |
  ConstantNotation 'a ("const _" 120) |
  TrueNotation ("true") |
  FalseNotation ("false")

ML_file \<open>markup.ML\<close>

ML \<open>
structure IRExprTranslator : DSL_TRANSLATION =
struct
fun markup DSL_Tokens.Add = @{term BinaryExpr} $ @{term BinAdd}
  | markup DSL_Tokens.Sub = @{term BinaryExpr} $ @{term BinSub}
  | markup DSL_Tokens.Mul = @{term BinaryExpr} $ @{term BinMul}
  | markup DSL_Tokens.And = @{term BinaryExpr} $ @{term BinAnd}
  | markup DSL_Tokens.Abs = @{term UnaryExpr} $ @{term UnaryAbs}
  | markup DSL_Tokens.Less = @{term BinaryExpr} $ @{term BinIntegerLessThan}
  | markup DSL_Tokens.Equals = @{term BinaryExpr} $ @{term BinIntegerEquals}
  | markup DSL_Tokens.Not = @{term UnaryExpr} $ @{term UnaryLogicNegation}
  | markup DSL_Tokens.Negate = @{term UnaryExpr} $ @{term UnaryNeg}
  | markup DSL_Tokens.LeftShift = @{term BinaryExpr} $ @{term BinLeftShift}
  | markup DSL_Tokens.RightShift = @{term BinaryExpr} $ @{term BinRightShift}
  | markup DSL_Tokens.UnsignedRightShift = @{term BinaryExpr} $ @{term BinURightShift}
  | markup DSL_Tokens.Conditional = @{term ConditionalExpr}
  | markup DSL_Tokens.Constant = @{term ConstantExpr}
  | markup DSL_Tokens.TrueConstant = @{term "ConstantExpr (IntVal32 1)"}
  | markup DSL_Tokens.FalseConstant = @{term "ConstantExpr (IntVal32 0)"}
end

structure IntValTranslator : DSL_TRANSLATION =
struct
fun markup DSL_Tokens.Add = @{term intval_add}
  | markup DSL_Tokens.Sub = @{term intval_sub}
  | markup DSL_Tokens.Mul = @{term intval_mul}
  | markup DSL_Tokens.And = @{term intval_and}
  | markup DSL_Tokens.Abs = @{term intval_abs}
  | markup DSL_Tokens.Less = @{term intval_less_than}
  | markup DSL_Tokens.Equals = @{term intval_equals}
  | markup DSL_Tokens.Not = @{term intval_logic_negation}
  | markup DSL_Tokens.Negate = @{term intval_negate}
  | markup DSL_Tokens.LeftShift = @{term intval_left_shift}
  | markup DSL_Tokens.RightShift = @{term intval_right_shift}
  | markup DSL_Tokens.UnsignedRightShift = @{term intval_uright_shift}
  | markup DSL_Tokens.Conditional = @{term intval_conditional}
  | markup DSL_Tokens.Constant = @{term IntVal32}
  | markup DSL_Tokens.TrueConstant = @{term "IntVal32 1"}
  | markup DSL_Tokens.FalseConstant = @{term "IntVal32 0"}
end

structure IRExprMarkup = DSL_Markup(IRExprTranslator);
structure IntValMarkup = DSL_Markup(IntValTranslator);
\<close>

snipbegin \<open>ir expression translation\<close>
syntax "_expandExpr" :: "term \<Rightarrow> term" ("exp[_]")
parse_translation \<open> [( @{syntax_const "_expandExpr"} , IRExprMarkup.markup_expr)] \<close>
snipend -

snipbegin \<open>value expression translation\<close>
syntax "_expandIntVal" :: "term \<Rightarrow> term" ("val[_]")
parse_translation \<open> [( @{syntax_const "_expandIntVal"} , IntValMarkup.markup_expr)] \<close>
snipend -

snipbegin \<open>ir expression example\<close>
value "exp[(e\<^sub>1 < e\<^sub>2) ? e\<^sub>1 : e\<^sub>2]"
text \<open>@{term \<open>exp[(e\<^sub>1 < e\<^sub>2) ? e\<^sub>1 : e\<^sub>2]\<close>}\<close>
snipend - 

snipbegin \<open>value expression example\<close>
value "val[(e\<^sub>1 < e\<^sub>2) ? e\<^sub>1 : e\<^sub>2]"
text \<open>@{term \<open>val[(e\<^sub>1 < e\<^sub>2) ? e\<^sub>1 : e\<^sub>2]\<close>}\<close>
snipend -
value "exp[((e\<^sub>1 - e\<^sub>2) + (const (IntVal32 0)) + e\<^sub>2) \<longmapsto> e\<^sub>1 when True]"
value "val[((e\<^sub>1 - e\<^sub>2) + (const 0) + e\<^sub>2) \<longmapsto> e\<^sub>1 when True]"

end