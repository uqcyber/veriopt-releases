theory CanonicalizationSyntax
imports CanonicalizationTreeProofs
begin


ML \<open>
fun translateConst (str, typ) =
  case (str, typ) of
    ("\<^const>Groups.plus_class.plus", _) => @{const BinaryExpr} $ @{const BinAdd}
    | ("\<^const>Groups.minus_class.minus", _) => @{const BinaryExpr} $ @{const BinSub}
    | ("\<^const>Groups.times_class.times", _) => @{const BinaryExpr} $ @{const BinMul}
    | ("\<^const>Groups.uminus_class.uminus", _) => @{const UnaryExpr} $ @{const UnaryNeg}
    | _ => Const (str, typ)

fun expandNode ctxt trm =
  case trm of
    Const (str, typ) => translateConst (str, typ)
    | Abs (str, typ, trm) => Abs (str, typ, expandNode ctxt trm)
    | e as ((Const ("\<^const>IRTreeEval.IRExpr.ConstantExpr",_)) $ _) => e
    | (x $ y) => (expandNode ctxt x $ expandNode ctxt y)
    | _ => trm

fun expandNodes ctxt [trm] = expandNode ctxt trm
  | expandNodes _ ts = raise TERM ("expandNodes", ts)

fun baseTransform ctxt [pre, post] =
  Const
     ("Orderings.ord_class.less_eq", @{typ "IRExpr => IRExpr \<Rightarrow> bool"})
    $ expandNode ctxt pre
    $ expandNode ctxt post

  | baseTransform _ ts = raise TERM ("baseTransform", ts)

fun constantValues _ [trm] =
  (case trm of
    c as Const _ =>
      @{const ConstantExpr} $ (@{const IntVal32} $ c)
    | x $ y => 
      @{const ConstantExpr} $ (@{const IntVal32} $ (x $ y))
    | _ => trm)
  | constantValues _ ts = raise TERM ("constantValues", ts)

\<close>

syntax "_constantValues" :: "term \<Rightarrow> term" ("C _" 100)
parse_translation \<open> [( @{syntax_const "_constantValues"} , constantValues)] \<close>

syntax "_expandNodes" :: "term \<Rightarrow> term" ("exp[_]")
parse_translation \<open> [( @{syntax_const "_expandNodes"} , expandNodes)] \<close>

syntax "_baseTransform" :: "term \<Rightarrow> term \<Rightarrow> term" ("_ \<mapsto> _" 40)
parse_translation \<open> [( @{syntax_const "_baseTransform"} , baseTransform)] \<close>


ML_val \<open>@{term "C 1"}\<close>

(*declare [[show_types,show_sorts,names_long,show_consts,show_brackets]]
declare [[eta_contract]]*)
(*declare [[syntax_ast_trace]]*)


datatype Type =
  Integer |
  Object |
  Unknown

definition type :: "IRExpr \<Rightarrow> Type" where
  "type e = (case (stamp_expr e) of
    IntegerStamp _ _ _ \<Rightarrow> Integer
    | ObjectStamp _ _ _ _ \<Rightarrow> Object
    | _ \<Rightarrow> Unknown)"

lemma unfold_type[simp]:
  "(type x = Integer) = is_IntegerStamp (stamp_expr x)"
  unfolding type_def using is_IntegerStamp_def
  using Stamp.case_eq_if Stamp.disc(1) Type.distinct(1) Type.distinct(3)
  by (simp add: Stamp.case_eq_if)

definition type_safe :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "type_safe e1 e2 = 
    ((type e1 = type e2) 
    \<and> (is_IntegerStamp (stamp_expr e1) 
        \<longrightarrow> (stp_bits (stamp_expr e1) = stp_bits (stamp_expr e2))))"

lemma unfold_int_typesafe[simp]:
  assumes "type e1 = Integer"
  shows "type_safe e1 e2 = 
    ((type e1 = type e2) \<and>
    (stp_bits (stamp_expr e1) = stp_bits (stamp_expr e2)))"
proof -
  have "is_IntegerStamp (stamp_expr e1)"
    using assms unfold_type by simp
  then show ?thesis unfolding type_safe_def
    by simp
qed


lemma 
  assumes "type x = Integer"
  assumes "type_safe x y"
  shows "x + (-y) \<mapsto> x - y"
  using assms apply simp
  using BinaryExprE Stamp.sel(1) UnaryExprE add_rewrites_helper(4) bin_eval.simps(1) 
        bin_eval.simps(3) evalDet int_stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(2)
  proof -
    have "\<forall>i f cs vs. \<not> [f,vs] \<turnstile> i \<mapsto> ObjStr cs"
      by (meson int_stamp_implies_valid_value valid_value.simps(42))
    then show "\<forall>m p v. [m,p] \<turnstile> BinaryExpr BinAdd x (UnaryExpr UnaryNeg y) \<mapsto> v \<longrightarrow> [m,p] \<turnstile> BinaryExpr BinSub x y \<mapsto> v"
      by blast
  qed


(* CODE GENERATION ATTEMPTS *)
definition replace :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool"
where
[code_abbrev]: "replace a b = (a \<mapsto> b)"

definition sub_to_add where
  "sub_to_add = (C 0 + C 1 \<mapsto> C 0 - C 1)"

export_code sub_to_add in Scala


end