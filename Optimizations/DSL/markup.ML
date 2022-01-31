(*  Title:      Optimizations/DSL/markup.ML
    Author:     Brae Webb

Lift shorthand expressions to the full type.
*)

structure DSL_Tokens =
struct

datatype Tokens =
    Add
  | Sub
  | Mul
  | And
  | Less
  | Abs
  | Equals
  | Not
  | Negate
  | LeftShift
  | RightShift
  | UnsignedRightShift
  | Conditional
  | Constant
end

signature DSL_TRANSLATION =
sig
val markup: DSL_Tokens.Tokens -> term
end

signature DSL_MARKUP =
sig
  val const_expr: Proof.context -> term list -> term
  val equals_expr: Proof.context -> term list -> term

  val markup_expr: Proof.context -> term list -> term

  val rewrite: Proof.context -> term list -> term
  val conditional_rewrite: Proof.context -> term list -> term
end;

functor DSL_Markup(Translator: DSL_TRANSLATION): DSL_MARKUP =
struct

fun const_expr _ [c as Const _] =
    @{const ConstantExpr} $ (@{const IntVal32} $ c)
  | const_expr _ [x $ y] =
    @{const ConstantExpr} $ (@{const IntVal32} $ (x $ y))
  | const_expr _ ts = raise TERM ("const_expr", ts)

fun equals_expr _ [lhs, rhs] =
    Translator.markup DSL_Tokens.Equals $ lhs $ rhs
  | equals_expr _ ts = raise TERM ("equals_expr", ts)


(* Shorthand expressions *)
fun markup_constant (str, typ) =
  case (str, typ) of
    ("\<^const>Markup.ExtraNotation.ConditionalNotation", _) => Translator.markup DSL_Tokens.Conditional
    | ("Markup.ExtraNotation.ConditionalNotation", _) => Translator.markup DSL_Tokens.Conditional
    | ("\<^const>Markup.ExtraNotation.EqualsNotation", _) => Translator.markup DSL_Tokens.Equals
    | ("Markup.ExtraNotation.EqualsNotation", _) => Translator.markup DSL_Tokens.Equals
    | ("\<^const>Markup.ExtraNotation.ConstantNotation", _) => Translator.markup DSL_Tokens.Constant
    | ("Markup.ExtraNotation.ConstantNotation", _) => Translator.markup DSL_Tokens.Constant
    | ("\<^const>Groups.plus_class.plus", _) => Translator.markup DSL_Tokens.Add
    | ("Groups.plus_class.plus", _) => Translator.markup DSL_Tokens.Add
    | ("\<^const>Groups.minus_class.minus", _) => Translator.markup DSL_Tokens.Sub
    | ("Groups.minus_class.minus", _) => Translator.markup DSL_Tokens.Sub
    | ("\<^const>Groups.times_class.times", _) => Translator.markup DSL_Tokens.Mul
    | ("Groups.times_class.times", _) => Translator.markup DSL_Tokens.Mul
    | ("\<^const>HOL.conj", _) => Translator.markup DSL_Tokens.And
    | ("HOL.conj", _) => Translator.markup DSL_Tokens.And
    | ("\<^const>Groups.uminus_class.uminus", _) => Translator.markup DSL_Tokens.Negate
    | ("Groups.uminus_class.uminus", _) => Translator.markup DSL_Tokens.Negate
    | ("\<^const>HOL.Not", _) => Translator.markup DSL_Tokens.Not
    | ("HOL.Not", _) => Translator.markup DSL_Tokens.Not
    | ("\<^const>Orderings.ord_class.less", _) => Translator.markup DSL_Tokens.Less
    | ("Orderings.ord_class.less", _) => Translator.markup DSL_Tokens.Less
    | ("\<^const>Groups.abs_class.abs", _) => Translator.markup DSL_Tokens.Abs
    | ("Groups.abs_class.abs", _) => Translator.markup DSL_Tokens.Abs
    | ("\<^const>Values.shiftl", _) => Translator.markup DSL_Tokens.LeftShift
    | ("Values.shiftl", _) => Translator.markup DSL_Tokens.LeftShift
    | ("\<^const>Values.shiftr", _) => Translator.markup DSL_Tokens.RightShift
    | ("Values.shiftr", _) => Translator.markup DSL_Tokens.RightShift
    | ("\<^const>Values.sshiftr", _) => Translator.markup DSL_Tokens.UnsignedRightShift
    | ("Values.sshiftr", _) => Translator.markup DSL_Tokens.UnsignedRightShift
    | _ => Const (str, typ)

fun markup_free (str, typ) =
  case (str, typ) of
    ("abs", _) => Translator.markup DSL_Tokens.Abs
    | (var, typ) => Free (var, typ)

fun markup_expr ctxt [trm] =
  let
    val res = (case trm of
      Const (str, typ) => markup_constant (str, typ)
    | e as ((Const ("\<^const>IRTreeEval.IRExpr.ConstantExpr",_)) $ _) => e (* ignore within a constant *)
    | (e as (Const ("\<^const>Markup.Rewrite.Conditional",_))) $ lhs $ rhs $ cond => 
      e $ markup_expr ctxt [lhs] $ markup_expr ctxt [rhs] $ cond
    | (e as (Const ("Markup.Rewrite.Conditional",_))) $ lhs $ rhs $ cond => 
      e $ markup_expr ctxt [lhs] $ markup_expr ctxt [rhs] $ cond
    | (x $ y) => (markup_expr ctxt [x] $ markup_expr ctxt [y])
    | Free (str, typ) => markup_free (str, typ)
    | Abs (str, typ, trm) => Abs (str, typ, markup_expr ctxt [trm])
    | _ => trm);
  in
    res
  end
  | markup_expr _ ts = raise TERM ("markup_expr", ts)


(* Rewrite syntax *)
fun rewrite ctxt [pre, post] =
  Const ("Transform", @{typ "'a => 'a \<Rightarrow> 'a Rewrite"})
    $ markup_expr ctxt [pre]
    $ markup_expr ctxt [post]

  | rewrite _ ts = raise TERM ("rewrite", ts)

fun conditional_rewrite ctxt [pre, post, cond] =
  Const ("Conditional", @{typ "'a \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a Rewrite"})
    $ markup_expr ctxt [pre]
    $ markup_expr ctxt [post]
    $ cond

  | conditional_rewrite _ ts = raise TERM ("conditional_rewrite", ts)

end