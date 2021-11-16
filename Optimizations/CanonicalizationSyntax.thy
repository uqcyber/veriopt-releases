theory CanonicalizationSyntax
imports CanonicalizationTreeProofs
keywords
  "phase" :: thy_decl and
  "optimization" :: thy_goal_defn and
  "print_optimizations" :: diag
begin


fun size :: "IRExpr \<Rightarrow> int" where
  "size (UnaryExpr op e) = (size e) + 2" |
  "size (BinaryExpr op x y) = (size x) + (size y) + 2" |
  "size (ConditionalExpr cond t f) = (size cond) + (size t) + (size f) + 2" |
  "size (ConstantExpr const) = 1" |
  "size (ParameterExpr ind s) = 2" |
  "size (LeafExpr nid s) = 2" |
  "size (ConstantVar c) = 1" |
  "size (VariableExpr x s) = 1"


datatype 'a Rewrite =
  Transform 'a 'a |
  Conditional 'a 'a "bool" |
  Sequential "'a Rewrite" "'a Rewrite" |
  Transitive "'a Rewrite"


ML_val \<open>@{term "Transform a a"}\<close>
ML_val \<open>@{term "Conditional a b c"}\<close>
ML_val \<open>@{term "Sequential a b"}\<close>
ML_val \<open>@{term "Transitive a"}\<close>


fun rewrite_obligation :: "IRExpr Rewrite \<Rightarrow> bool" where
  "rewrite_obligation (Transform x y) = (y \<le> x)" |
  "rewrite_obligation (Conditional x y cond) = (cond \<longrightarrow> (y \<le> x))" |
  "rewrite_obligation (Sequential x y) = (rewrite_obligation x \<and> rewrite_obligation y)" |
  "rewrite_obligation (Transitive x) = rewrite_obligation x"


ML_val \<open>@{term "rewrite_obligation a"}\<close>

ML \<open>
val debugMode = false

fun debugPrint value =
  if debugMode then (@{print} value) else value

fun translateConst (str, typ) =
  case (str, typ) of
    ("\<^const>Groups.plus_class.plus", _) => @{const BinaryExpr} $ @{const BinAdd}
    | ("\<^const>Groups.minus_class.minus", _) => @{const BinaryExpr} $ @{const BinSub}
    | ("\<^const>Groups.times_class.times", _) => @{const BinaryExpr} $ @{const BinMul}
    | ("\<^const>HOL.conj", _) => @{const BinaryExpr} $ @{const BinAnd}
    | ("\<^const>_binEquals", _) => @{const BinaryExpr} $ @{const BinIntegerEquals}
    | ("\<^const>Groups.uminus_class.uminus", _) => @{const UnaryExpr} $ @{const UnaryNeg}
    | _ => Const (str, typ)

fun translateEquals _ terms =
  @{const BinaryExpr} $ @{const BinIntegerEquals} $ hd terms $ hd (tl terms)

(* A seemingly arbitrary distinction  *)
fun translateFree (str, typ) =
  case (str, typ) of
    ("abs", _) => @{const UnaryExpr} $ @{const UnaryAbs}
    | (var, typ) => 
      (if String.sub(var,0) = #"c" 
        then @{const ConstantExpr} $ Free ("val_" ^ var, typ)
        else Free (var, typ))

fun expandNode ctxt trm =
  let
    val _ = debugPrint "Expanding node";
    val _ = debugPrint trm;
  in
  case trm of
    Const (str, typ) => translateConst (str, typ)
    | Free (str, typ) => translateFree (str, typ)
    | Abs (str, typ, trm) => Abs (str, typ, expandNode ctxt trm)
    | e as ((Const ("\<^const>IRTreeEval.IRExpr.ConstantExpr",_)) $ _) => e
    | (x $ y) => (expandNode ctxt x $ expandNode ctxt y)
    | _ => trm
  end

fun expandNodes ctxt [trm] = expandNode ctxt trm
  | expandNodes _ ts = raise TERM ("expandNodes", ts)

fun baseTransform ctxt [pre, post] =
  Const
     ("CanonicalizationSyntax.Rewrite.Transform", @{typ "IRExpr => IRExpr \<Rightarrow> IRExpr Rewrite"})
    $ expandNode ctxt pre
    $ expandNode ctxt post

  | baseTransform _ ts = raise TERM ("baseTransform", ts)

fun conditionTransform ctxt [pre, post, cond] =
  Const ("CanonicalizationSyntax.Rewrite.Conditional", @{typ "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool \<Rightarrow> IRExpr Rewrite"})
    $ expandNode ctxt pre
    $ expandNode ctxt post
    $ cond

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

syntax "_constantValues" :: "term \<Rightarrow> term" ("const _" 120)
parse_translation \<open> [( @{syntax_const "_constantValues"} , constantValues)] \<close>

notation ConditionalExpr ("_ ? _ : _")
syntax "_binEquals" :: "term \<Rightarrow> term \<Rightarrow> term" ("_ == _" 100)
parse_translation \<open> [( @{syntax_const "_binEquals"} , translateEquals)] \<close>

syntax "_expandNodes" :: "term \<Rightarrow> term" ("exp[_]")
parse_translation \<open> [( @{syntax_const "_expandNodes"} , expandNodes)] \<close>

syntax "_baseTransform" :: "term \<Rightarrow> term \<Rightarrow> term" ("_ \<mapsto> _" 10)
parse_translation \<open> [( @{syntax_const "_baseTransform"} , baseTransform)] \<close>

syntax "_conditionalTransform" :: "term \<Rightarrow> term \<Rightarrow> term \<Rightarrow> term" ("_ \<mapsto> _ when _" 70)
parse_translation \<open> [( @{syntax_const "_conditionalTransform"} , conditionTransform)] \<close>


value "exp[abs e]"
ML_val \<open>@{term "abs e"}\<close>
ML_val \<open>@{term "x & x"}\<close>
ML_val \<open>@{term "cond ? tv : fv"}\<close>
ML_val \<open>@{term "x < y"}\<close>
ML_val \<open>@{term "c < y"}\<close>
value "exp[c1 + y]"

datatype Type =
  Integer |
  Float |
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


lemma add_intstamp_prop:
  assumes "type x = Integer"
  assumes "type_safe x y"
  shows "type exp[x + y] = Integer"
  using assms unfolding type_def type_safe_def
  using stamp_expr.simps(3) stamp_binary.simps(1)
  using is_IntegerStamp_def type_def unfold_type by force

lemma sub_intstamp_prop:
  assumes "type x = Integer"
  assumes "type_safe x y"
  shows "type exp[x - y] = Integer"
  using assms unfolding type_def type_safe_def
  using stamp_expr.simps(3) stamp_binary.simps(1)
  by (metis Stamp.collapse(1) Stamp.disc(2) stamp_expr.simps(2) type_def unfold_type unrestricted_stamp.simps(2))

lemma uminus_intstamp_prop:
  assumes "type x = Integer"
  shows "type exp[-x] = Integer"
  using assms unfolding type_def type_safe_def
  using stamp_expr.simps(1) stamp_unary.simps(1)
  by (metis Stamp.collapse(1) Stamp.discI(1) type_def unfold_type unrestricted_stamp.simps(2))


lemma assume_proof :
  assumes "type x = Integer"
  assumes "type_safe x y"
  shows "rewrite_obligation ((x + (-y) \<mapsto> x - y))"
  unfolding rewrite_obligation.simps 
  unfolding le_expr_def apply (rule allI)+ apply (rule impI)
  using assms unfolding type_def type_safe_def 
  using CanonicalizeAddProof CanonicalizeAdd.intros
  sorry
(*
proof (induction rule: evaltree.induct)
  fix m p
  have "is_IntegerStamp (stamp_expr ?lhs)"
    using assms unfolding type_def
    by (smt (z3) Stamp.collapse(1) Stamp.sel(1) add_intstamp_prop assms(1) stamp_expr.simps(1) stamp_unary.simps(1) uminus_intstamp_prop unfold_int_typesafe unfold_type unrestricted_stamp.simps(2))
  obtain v where lhs: "[m,p] \<turnstile> ?lhs \<mapsto> v"
    using BinaryExprE evalDet sorry
  obtain v2 where rhs: "[m,p] \<turnstile> ?rhs \<mapsto> v2"
    sorry
  then show "v = v2"
    sorry
  then show ?thesis
*)


lemma "rewrite_obligation ((x + (-y)) \<mapsto> (x - y) when (type x = Integer \<and> type_safe x y))"
  sorry


lemma "(size exp[x + (-y)]) > (size exp[x - y])"
  using size.simps(1,2)
  by force



ML \<open>
datatype 'a Rewrite =
  Transform of 'a * 'a |
  Conditional of 'a * 'a * term |
  Sequential of 'a Rewrite * 'a Rewrite |
  Transitive of 'a Rewrite

type rewrite =
  {name: string, rewrite: term Rewrite}

type phase =
  {name: string, rewrites: rewrite list, preconditions: term list}

type phase_store = (string list * (string -> phase option))

datatype phase_state =
  NoPhase of phase_store |
  InPhase of (string * phase_store)

signature PhaseState =
sig
  val get: theory -> phase_state
  val add: rewrite -> theory -> theory
  val reset: theory -> theory
  val enter_phase: string -> theory -> theory
  val exit_phase: theory -> theory
end;

structure RWList: PhaseState =
struct

val empty = NoPhase ([], (fn _ => NONE));

fun merge_maps (left: 'a list * ('a -> 'b option)) (right: 'a list * ('a -> 'b option)) =
  ((fst left) @ (fst right), fn x => (case (snd left) x of
    NONE => (snd right) x |
    SOME v => SOME v))

structure RewriteStore = Theory_Data
(
  type T = phase_state;
  val empty = empty;
  val extend = I;
  fun merge (lhs, rhs) = 
    case lhs of
      NoPhase left_store => (case rhs of
        NoPhase right_store => NoPhase (merge_maps left_store right_store) |
        InPhase (name, right_store) => InPhase (name, (merge_maps left_store right_store))) |
      InPhase (name, left_store) => (case rhs of
        NoPhase right_store => InPhase (name, (merge_maps left_store right_store)) |
        InPhase (name, right_store) => InPhase (name, (merge_maps left_store right_store)))
);

val get = RewriteStore.get;

fun expand_phase rewrite (phase: phase) =
  {name = (#name phase), rewrites = cons rewrite (#rewrites phase), preconditions = (#preconditions phase)}

fun update_existing name (dom, map) rewrite =
  let
    val value = map name
  in
    case value of
      NONE => raise TERM ("phase not in store", []) |
      SOME v => InPhase (name, (dom, (fn id => (if id = name then SOME (expand_phase rewrite v) else map id))))
  end

fun add t thy = RewriteStore.map (fn state =>
  case state of
    NoPhase _ => raise TERM ("error", []) |
    InPhase (name, store) => update_existing name store t
  ) thy

val reset = RewriteStore.put empty;

fun new_phase name = {name = name, rewrites = ([] : rewrite list), preconditions = ([] : term list)};

fun enter_phase name thy = RewriteStore.map (fn state =>
  case state of
    NoPhase (dom, store) => InPhase (name, ([name] @ dom, fn id => (if id = name then SOME (new_phase name) else store id))) |
    InPhase (_, _) => raise TERM ("optimization phase already established", [])
  ) thy

fun exit_phase thy = RewriteStore.map (fn state =>
  case state of
    NoPhase _ => raise TERM ("phase already exited", []) |
    InPhase (_, existing) => NoPhase existing
  ) thy

end;


fun term_to_rewrite term =
  case term of
    (((Const ("CanonicalizationSyntax.Rewrite.Transform", _)) $ lhs) $ rhs) => Transform (lhs, rhs)
    | ((((Const ("CanonicalizationSyntax.Rewrite.Conditional", _)) $ lhs) $ rhs) $ cond) => Conditional (lhs, rhs, cond)
    | _ => raise TERM ("optimization is not a rewrite", [term])

fun rewrite_to_term rewrite = 
  case rewrite of
    Transform (lhs, rhs) => 
      (Const ("CanonicalizationSyntax.Rewrite.Transform", @{typ "'a => 'a"})) $ lhs $ rhs
    | Conditional (lhs, rhs, cond) => 
      (Const ("CanonicalizationSyntax.Rewrite.Conditional", @{typ "'a => 'a"})) $ lhs $ rhs $ cond
    | _ => raise TERM ("rewrite cannot be translated yet", [])

fun term_to_obligation ctxt term =
  Syntax.check_prop ctxt (@{const Trueprop} $ (@{const rewrite_obligation} $ term))

fun rewrite_to_termination rewrite = 
  case rewrite of
    Transform (lhs, rhs) => (
      @{const Trueprop} 
      $ (Const ("Orderings.ord_class.less", @{typ "int \<Rightarrow> int \<Rightarrow> bool"})
      $ (@{const size} $ rhs) $ (@{const size} $ lhs)))
    | Conditional (lhs, rhs, _) => (
      @{const Trueprop} 
      $ (Const ("Orderings.ord_class.less", @{typ "int \<Rightarrow> int \<Rightarrow> bool"})
      $ (@{const size} $ rhs) $ (@{const size} $ lhs)))
    | _ => raise TERM ("rewrite termination generation not implemented", [])

fun register_optimization 
  ((bind: binding, _), opt: string) ctxt = 
  let
    val term = Syntax.read_term ctxt opt;

    val rewrite = term_to_rewrite term;

    val obligation = term_to_obligation ctxt term;
    val terminating = rewrite_to_termination rewrite;

    val register = RWList.add {name=Binding.print bind, rewrite=rewrite}

    fun after_qed _ ctxt =
      Local_Theory.background_theory register ctxt
  in
    Proof.theorem NONE after_qed [[(obligation, []), (terminating, [])]] ctxt
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
  Local_Theory.background_theory (RWList.exit_phase) thy

fun begin_phase name thy =
  Proof_Context.init_global (RWList.enter_phase name thy)

fun
  pretty_rewrite rewrite = Syntax.pretty_term @{context} (rewrite_to_term rewrite)

fun print_optimizations rewrites = 
  let
    fun print_rule tact =
      Pretty.block [
        Pretty.str ((#name tact) ^ ": "),
        pretty_rewrite (#rewrite tact)
      ];
  in
    [Pretty.big_list "optimizations:" (map print_rule rewrites)]
  end

fun print_phase (phase: phase option) =
  case phase of
    NONE => [Pretty.str "no phase"] |
    SOME phase =>
  [Pretty.str ("phase: " ^ (#name phase))]
  @ (print_optimizations (#rewrites phase))

fun print_phase_state thy =
  case RWList.get (Proof_Context.theory_of thy) of
    NoPhase _ => [Pretty.str "not in a phase"] |
    InPhase (name, (dom, map)) => print_phase (map name)

fun print_all_phases thy =
  case RWList.get thy of
    NoPhase (dom, store) => 
      let val _ = @{print} dom;
      in List.foldr (fn (name, acc) => print_phase (store name) @ acc) [] dom end |
    InPhase (name, (dom, store)) => List.foldr (fn (name, acc) => print_phase (store name) @ acc) [] dom

fun phase_theory_init name thy = 
  Local_Theory.init 
    {background_naming = Sign.naming_of thy,
        setup = begin_phase name,
        conclude = exit_phase}
    {define = Generic_Target.define Generic_Target.theory_target_foundation,
        notes = Generic_Target.notes Generic_Target.theory_target_notes,
        abbrev = Generic_Target.abbrev Generic_Target.theory_target_abbrev,
        declaration = K Generic_Target.theory_declaration,
        theory_registration = Locale.add_registration_theory,
        locale_dependency = fn _ => error "Not possible in instantiation target",
        pretty = print_phase_state}
    thy

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>phase\<close> "instantiate and prove type arity"
   (Parse.name --| Parse.begin
     >> (fn name => Toplevel.begin_main_target true (phase_theory_init name)));


fun apply_print_optimizations thy =
  (print_all_phases thy |> Pretty.writeln_chunks)


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_optimizations\<close>
    "print debug information for optimizations"
    (Scan.succeed
      (Toplevel.keep (apply_print_optimizations o Toplevel.theory_of)));
\<close>

setup \<open>RWList.reset\<close>


(*
notation BinaryExpr ("_ \<oplus>\<^sub>_ _")

value "x \<oplus>\<^sub>s y"
*)
phase Canonicalization begin

(*
optimization constant_fold:
  "(const(c\<^sub>1) \<oplus>\<^sub>x const(c\<^sub>2)) \<mapsto> (bin_eval c\<^sub>1 x c\<^sub>2)"
*)
optimization constant_add:
  "(e1 + e2) \<mapsto> r when (e1 = ConstantExpr v1 \<and> e2 = ConstantExpr v2 \<and> r = ConstantExpr (intval_add v1 v2))"
  unfolding le_expr_def apply (cases; auto) using evaltree.ConstantExpr defer
   apply simp
  sorry

optimization constant_add:
  "(c1 + c2) \<mapsto> ConstantExpr (intval_add val_c1 val_c2)"
  unfolding le_expr_def apply (cases; auto) using evaltree.ConstantExpr defer
   apply simp
  sorry

print_context
print_optimizations

optimization constant_shift:
  "(c + e) \<mapsto> (e + c) when (\<not>(is_ConstantExpr e) \<and> type e = Integer)"
   unfolding rewrite_obligation.simps apply (rule impI) defer apply simp
  sorry

optimization neutral_zero:
  "(e + const(0)) \<mapsto> e when (type e = Integer)"
   defer apply simp+
  sorry

ML_val \<open>@{term "(e1 - e2) + e2 \<mapsto> e1"}\<close>

optimization neutral_left_add_sub:
  "(e1 - e2) + e2 \<mapsto> e1"
  sorry

optimization neutral_right_add_sub:
  "e1 + (e2 - e1) \<mapsto> e2"
  sorry

optimization add_ynegate:
  "(x + (-y)) \<mapsto> (x - y) when (type x = Integer \<and> type_safe x y)"
  sorry

print_context
print_optimizations



end

print_context
print_optimizations

phase DirectTranslationTest begin
print_optimizations

optimization AbsIdempotence: "abs(abs(e)) \<mapsto> abs(e) when is_IntegerStamp (stamp_expr e)"
  apply auto
  by (metis UnaryExpr abs_abs_is_abs stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(1))


print_optimizations
optimization AbsNegate: "abs(-e) \<mapsto> abs(e) when is_IntegerStamp (stamp_expr e)"
  apply auto
  by (metis UnaryExpr abs_neg_is_neg stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(1))

lemma
  assumes "[m, p] \<turnstile> UnaryExpr op c \<mapsto> val"
  shows "valid_value (stamp_expr (UnaryExpr op c)) val"
  using stamp_implies_valid_value assms
  by blast

lemma int_constants_valid:
  assumes "is_int_val val"  
  shows "valid_value (constantAsStamp val) val"
  using assms apply (cases val)
  by simp+

lemma unary_eval_preserves_validity:
  assumes "is_int_val c"
  shows "valid_value (constantAsStamp (unary_eval op c)) (unary_eval op c)"
  using assms apply (cases c) apply simp
     defer defer apply simp+
  apply (cases op)
  using int_constants_valid intval_abs.simps(1) is_int_val.simps(1) unary_eval.simps(1) apply presburger
  using int_constants_valid intval_negate.simps(1) is_int_val.simps(1) unary_eval.simps(2) apply presburger
  using int_constants_valid intval_not.simps(1) is_int_val.simps(1) unary_eval.simps(3) apply presburger
  using int_constants_valid is_int_val.simps(1) unary_eval.simps(4) apply presburger
     defer defer defer
     apply (cases op)
  using int_constants_valid intval_abs.simps(2) is_int_val.simps(2) unary_eval.simps(1) apply presburger
  using int_constants_valid intval_negate.simps(2) is_int_val.simps(2) unary_eval.simps(2) apply presburger
  using int_constants_valid intval_not.simps(2) is_int_val.simps(2) unary_eval.simps(3) apply presburger
  sorry (* WARNING: TODO: WARNING: a whole bunch of unary operations aren't implemented making this false *)

optimization UnaryConstantFold: "UnaryExpr op c \<mapsto> ConstantExpr (unary_eval op val_c) when is_int_val val_c"
  apply (auto simp: int_constants_valid)
  using evaltree.ConstantExpr int_constants_valid unary_eval_preserves_validity by simp

optimization AndEqual: "x & x \<mapsto> x when is_IntegerStamp (stamp_expr x)" sorry
optimization AndShiftConstantRight: "((ConstantExpr x) + y) \<mapsto> y + (ConstantExpr x) when ~(is_ConstantExpr y)" sorry
(*
optimization AndRightFallthrough: "x & y \<mapsto> y when (canBeZero x.stamp & canBeOne y.stamp) = 0" sorry
optimization AndLeftFallthrough: "x & y \<mapsto> x when (canBeZero y.stamp & canBeOne x.stamp) = 0" sorry
*)
optimization AndNeutral: "x & (const (NOT 0)) \<mapsto> x" sorry
optimization ConditionalEqualBranches: "(b ? v : v) \<mapsto> v" sorry
optimization ConditionalEqualIsRHS: "((x == y) ? x : y) \<mapsto> y" sorry
(*
optimization ConditionalEliminateKnownLess: "(x < y ? x : y) \<mapsto> x when (x.stamp.upper <= y.stamp.lower)" sorry
optimization ConditionalEliminateKnownLess: "(x < y ? y : x) \<mapsto> y when (x.stamp.upper <= y.stamp.lower)" sorry
*)
optimization BinaryFoldConstant: "BinaryExpr op (ConstantExpr e1) (ConstantExpr e2) \<mapsto> ConstantExpr (bin_eval op e1 e2)" sorry
optimization AddShiftConstantRight: "((ConstantExpr x) + y) \<mapsto> y + (ConstantExpr x) when ~(is_ConstantExpr y)" sorry
(*
optimization RedundantSubAdd: "isAssociative + => (a - b) + b \<mapsto> a" sorry
optimization RedundantAddSub: "isAssociative + => (b + a) - b \<mapsto> a" sorry
*)
optimization AddNeutral: "e + (const 0) \<mapsto> e" sorry
optimization AddLeftNegateToSub: "-e + y \<mapsto> y - e" sorry
optimization AddRightNegateToSub: "x + -e \<mapsto> x - e" sorry
optimization AddShiftConstantRight: "((ConstantExpr x) + y) \<mapsto> y + (ConstantExpr x) when ~ (is_ConstantExpr y)" sorry

print_context
print_optimizations
end

print_optimizations

end
