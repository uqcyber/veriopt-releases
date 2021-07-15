theory CanonicalizationSyntax
imports CanonicalizationTreeProofs
keywords
  "phase" :: thy_decl and
  "optimization" :: thy_goal_defn and
  "print_optimizations" :: diag
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

fun conditionTransform ctxt [pre, post, cond] =
  Const ("HOL.implies", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"}) $
    cond $
  (Const
     ("Orderings.ord_class.less_eq", @{typ "IRExpr => IRExpr \<Rightarrow> bool"})
    $ expandNode ctxt pre
    $ expandNode ctxt post)

  | conditionTransform _ ts = raise TERM ("conditionTransform", ts)

fun constantValues _ [trm] =
  (case trm of
    c as Const _ =>
      @{const ConstantExpr} $ (@{const IntVal32} $ c)
    | x $ y => 
      @{const ConstantExpr} $ (@{const IntVal32} $ (x $ y))
    | _ => trm)
  | constantValues _ ts = raise TERM ("constantValues", ts)

\<close>

syntax "_constantValues" :: "term \<Rightarrow> term" ("C\<langle>_\<rangle>" 100)
parse_translation \<open> [( @{syntax_const "_constantValues"} , constantValues)] \<close>

syntax "_expandNodes" :: "term \<Rightarrow> term" ("exp[_]")
parse_translation \<open> [( @{syntax_const "_expandNodes"} , expandNodes)] \<close>

syntax "_baseTransform" :: "term \<Rightarrow> term \<Rightarrow> term" ("_ \<mapsto> _" 40)
parse_translation \<open> [( @{syntax_const "_baseTransform"} , baseTransform)] \<close>

syntax "_conditionalTransform" :: "term \<Rightarrow> term \<Rightarrow> term \<Rightarrow> term" ("_ \<mapsto> _ when _" 70)
parse_translation \<open> [( @{syntax_const "_conditionalTransform"} , conditionTransform)] \<close>


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


lemma assume_proof:
  assumes "type x = Integer"
  assumes "type_safe x y"
  shows "x + (-y) \<mapsto> x - y"
  using assms apply simp
  using BinaryExprE Stamp.sel(1) UnaryExprE add_rewrites_helper(4) bin_eval.simps(1) 
        bin_eval.simps(3) evalDet int_stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(2)
  proof -
    have "\<forall>i f cs vs. \<not> [f,vs] \<turnstile> i \<mapsto> ObjStr cs"
      by (meson int_stamp_implies_valid_value valid_value.simps(42))
    then show "\<forall>m p v. ([m,p] \<turnstile> BinaryExpr BinAdd x (UnaryExpr UnaryNeg y) \<mapsto> v) \<longrightarrow> ([m,p] \<turnstile> BinaryExpr BinSub x y \<mapsto> v)"
      by blast
  qed


lemma "(x + (-y)) \<mapsto> (x - y) when (type x = Integer \<and> type_safe x y)"
  using assume_proof by blast


ML \<open>
datatype 'a Rewrite =
  Transform of 'a * 'a |
  Conditional of 'a * 'a * ('a -> 'a -> bool) |
  Sequential of 'a Rewrite * 'a Rewrite |
  Transitive of 'a Rewrite

type rewrite =
  {name: string, rewrite: term Rewrite}

signature RewriteList =
sig
  val get: theory -> rewrite list
  val add: rewrite -> theory -> theory
  val reset: theory -> theory
end;

structure RWList: RewriteList =
struct

structure RewriteStore = Theory_Data
(
  type T = rewrite list;
  val empty = [];
  val extend = I;
  val merge = Library.merge (fn (_) => true);
);

val get = RewriteStore.get;

fun add t thy = RewriteStore.map (cons t) thy

val reset = RewriteStore.put [];

end;

fun register_optimization 
  ((bind: binding, _), opt: string) ctxt = 
  let
    val prop = Syntax.read_prop ctxt opt;
    val term = Syntax.read_term ctxt opt;
    val rewrite = Transform (term, term);
    val _ = @{print} (Toplevel.theory_toplevel (Proof_Context.theory_of ctxt));

    val register = RWList.add {name=Binding.print bind, rewrite=rewrite}

    fun after_qed _ ctxt =
      Local_Theory.background_theory register ctxt
  in
    Proof.theorem NONE after_qed [[(prop, [])]] ctxt
  end


val parse_optimization_declaration =
  Parse_Spec.thm_name ":"

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>optimization\<close>
    "define an optimization and open proof obligation"
    (parse_optimization_declaration
     -- Parse.term
     >> register_optimization);

fun exit_phase thy =
  thy

fun begin_phase thy =
  Proof_Context.init_global thy

fun
  pretty_rewrite (Transform (x, y)) = Syntax.pretty_term @{context} x
  | pretty_rewrite (Conditional (x, y, cond)) = Syntax.pretty_term @{context} x
  | pretty_rewrite (Sequential (x, y)) = pretty_rewrite x
  | pretty_rewrite (Transitive x) = pretty_rewrite x

fun print_optimizations ctxt =
  let
    fun print_rule tact =
      Pretty.block [
        Pretty.str ((#name tact) ^ ": "),
        pretty_rewrite (#rewrite tact)
      ];
  in
    [Pretty.big_list "optimizations:" (map print_rule (RWList.get ctxt))]
  end

fun print_phase name thy =
  [Pretty.str ("phase: " ^ name)] 
  @ (print_optimizations (Proof_Context.theory_of thy))

fun phase_theory_init name thy = 
  Local_Theory.init 
    {background_naming = Sign.naming_of thy,
        setup = begin_phase,
        conclude = exit_phase}
    {define = Generic_Target.define Generic_Target.theory_target_foundation,
        notes = Generic_Target.notes Generic_Target.theory_target_notes,
        abbrev = Generic_Target.abbrev Generic_Target.theory_target_abbrev,
        declaration = K Generic_Target.theory_declaration,
        theory_registration = Locale.add_registration_theory,
        locale_dependency = fn _ => error "Not possible in instantiation target",
        pretty = print_phase name}
    thy

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>phase\<close> "instantiate and prove type arity"
   (Parse.name --| Parse.begin
     >> (fn name => Toplevel.begin_main_target true (phase_theory_init name)));


fun apply_print_optimizations thy =
  (print_optimizations thy |> Pretty.writeln_chunks)


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_optimizations\<close>
    "print debug information for optimizations"
    (Scan.succeed
      (Toplevel.keep (apply_print_optimizations o Toplevel.theory_of)));
\<close>

setup \<open>RWList.reset\<close>

phase Canonicalization begin

optimization add_ynegate:
  "(x + (-y)) \<mapsto> (x - y) when (type x = Integer \<and> type_safe x y)"
  using assume_proof
  by blast 

print_context

end

print_context
print_optimizations

end
