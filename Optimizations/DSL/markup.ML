(*  Title:      Optimizations/DSL/markup.ML
    Author:     Brae Webb

Lift shorthand expressions to the full type.
*)

signature DSL_MARKUP =
sig
  val const_expr: Proof.context -> term list -> term
  val equals_expr: Proof.context -> term list -> term

  val markup_expr: Proof.context -> term list -> term

  val rewrite: Proof.context -> term list -> term
  val conditional_rewrite: Proof.context -> term list -> term
end;

structure DSL_Markup: DSL_MARKUP =
struct

fun const_expr _ [c as Const _] =
    @{const ConstantExpr} $ (@{const IntVal32} $ c)
  | const_expr _ [x $ y] =
    @{const ConstantExpr} $ (@{const IntVal32} $ (x $ y))
  | const_expr _ ts = raise TERM ("const_expr", ts)

fun equals_expr _ [lhs, rhs] =
    @{const BinaryExpr} $ @{const BinIntegerEquals} $ lhs $ rhs
  | equals_expr _ ts = raise TERM ("equals_expr", ts)


(* Shorthand expressions *)
fun markup_constant (str, typ) =
  case (str, typ) of
    ("\<^const>Groups.plus_class.plus", _) => @{const BinaryExpr} $ @{const BinAdd}
    | ("\<^const>Groups.minus_class.minus", _) => @{const BinaryExpr} $ @{const BinSub}
    | ("\<^const>Groups.times_class.times", _) => @{const BinaryExpr} $ @{const BinMul}
    | ("\<^const>HOL.conj", _) => @{const BinaryExpr} $ @{const BinAnd}
    | ("\<^const>_binEquals", _) => @{const BinaryExpr} $ @{const BinIntegerEquals}
    | ("\<^const>Groups.uminus_class.uminus", _) => @{const UnaryExpr} $ @{const UnaryNeg}
    | ("\<^const>Values.shiftl", _) => @{const BinaryExpr} $ @{const BinLeftShift}
    | ("\<^const>Values.shiftr", _) => @{const BinaryExpr} $ @{const BinRightShift}
    | ("\<^const>Values.sshiftr", _) => @{const BinaryExpr} $ @{const BinURightShift}
    | _ => Const (str, typ)

fun markup_free (str, typ) =
  case (str, typ) of
    ("abs", _) => @{const UnaryExpr} $ @{const UnaryAbs}
    | (var, typ) => 
      (if String.sub(var,0) = #"c" 
        then @{const ConstantExpr} $ Free ("val_" ^ var, typ)
        else Free (var, typ))

fun markup_expr ctxt [trm] =
  (case trm of
    Const (str, typ) => markup_constant (str, typ)
    | Free (str, typ) => markup_free (str, typ)
    | Abs (str, typ, trm) => Abs (str, typ, markup_expr ctxt [trm])
    | e as ((Const ("\<^const>IRTreeEval.IRExpr.ConstantExpr",_)) $ _) => e
    | (x $ y) => (markup_expr ctxt [x] $ markup_expr ctxt [y])
    | _ => trm)
  | markup_expr _ ts = raise TERM ("markup_expr", ts)


(* Rewrite syntax *)
fun rewrite ctxt [pre, post] =
  Const ("Transform", @{typ "IRExpr => IRExpr \<Rightarrow> IRExpr Rewrite"})
    $ markup_expr ctxt [pre]
    $ markup_expr ctxt [post]

  | rewrite _ ts = raise TERM ("rewrite", ts)

fun conditional_rewrite ctxt [pre, post, cond] =
  Const ("Conditional", @{typ "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool \<Rightarrow> IRExpr Rewrite"})
    $ markup_expr ctxt [pre]
    $ markup_expr ctxt [post]
    $ cond

  | conditional_rewrite _ ts = raise TERM ("conditional_rewrite", ts)

end