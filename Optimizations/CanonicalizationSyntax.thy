theory CanonicalizationSyntax
imports CanonicalizationTreeProofs
keywords
  "phase" :: thy_decl and
  "optimization" :: thy_goal_defn and
  "print_optimizations" :: diag
begin


datatype 'a Rewrite =
  Transformation 'a 'a |
  Conditional 'a 'a "'a \<Rightarrow> 'a \<Rightarrow> bool" |
  Sequential "'a Rewrite" "'a Rewrite" |
  Transitive "'a Rewrite"


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

ML_val \<open>@{term "C\<langle>1\<rangle>"}\<close>

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
  apply simp using assume_proof
  by (meson le_expr_def unfold_type)


(* CODE GENERATION ATTEMPTS *)
definition replace :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
[code_abbrev]: "replace a b = (a \<mapsto> b)"

definition conditional_replace :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool \<Rightarrow> bool" where
[code_abbrev]: "conditional_replace a b c = (a \<mapsto> b when c)"

definition zero_add where
  "zero_add c = ((c + C\<langle>0\<rangle>) \<mapsto> c)"

definition zero_add_typed where
  "zero_add_typed c = ((c + C\<langle>0\<rangle>) \<mapsto> c when (type c = Integer))"

export_code zero_add in Scala
export_code zero_add_typed in Scala


ML \<open>
type rewrite =
  {name: string, rule: term}

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

val t = @{term "world"}
fun after_qed' _ _ =
    Toplevel.theory o fold
      (fn _ => (RWList.add {name="hello", rule=t}))


fun goals
  ((
    (bind: binding, name)),
    opt: string)
   ctxt = 
  let
    val prop = Syntax.read_prop ctxt opt;
    val term = Syntax.read_term ctxt opt;

    val register = RWList.add {name=Binding.print bind, rule=term}

    (*fun after_qed thms ctxt' =
      Proof_Context.transfer_facts (register (Proof_Context.theory_of ctxt')) ctxt'
    *)

    fun after_qed _ ctxt =
      let
        val _ = @{print} "why"
        val _ = @{print} (RWList.get (Proof_Context.theory_of ctxt))
      in
        Proof_Context.background_theory register ctxt
      end

    
      (*(Toplevel.keep (fn _ => Toplevel.theory_toplevel (register (Toplevel.theory_of ctxt))));*)
(*
      let
        val thy' = ((Local_Theory.note (name, (flat thms)) lthy) |> snd)
      in
        (Local_Theory.note (name, flat thms) lthy) |> snd
      end
*)
    (*val compilation = Predicate_Compile_Core.code_pred
      Predicate_Compile_Aux.default_options
      "flip_negation"
      ctxt*)

    val _ = @{print} {name = name, term = term}
  in
    Proof.theorem NONE after_qed [[(prop, [])]] 
      (Proof_Context.background_theory register ctxt)
  end


val parse_optimization_declaration =
  Parse_Spec.thm_name ":"

val parse_optimization =
  Parse.term

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>optimization\<close>
    "define an optimization and open proof obligation"
    (parse_optimization_declaration
     -- parse_optimization
     >> goals);

fun do_nothing _ = (Local_Theory.background_theory I)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>phase\<close>
    "Whole optimization phase definition"
    (
      Parse.name
      -- Parse.$$$ "begin"
    >> do_nothing);


fun print_optimizations ctxt =
  let
    fun print_rule tact =
      Pretty.block [
        Pretty.str ((#name tact) ^ ": "),
        Syntax.pretty_term @{context} (#rule tact)
      ];
  in
    [Pretty.big_list "optimizations:" (map print_rule (RWList.get ctxt))]
  end |> Pretty.writeln_chunks;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_optimizations\<close>
    "print debug information for optimizations"
    (Scan.succeed
      (Toplevel.keep (print_optimizations o Toplevel.theory_of)));
\<close>

setup \<open>RWList.reset\<close>

phase Canonicalization begin

optimization add_ynegate:
  "(x + (-y)) \<mapsto> (x - y) when (type x = Integer \<and> type_safe x y)"
  using assume_proof
  print_optimizations
  by blast 

print_optimizations
ML_val \<open>RWList.get (Proof_Context.theory_of @{context})\<close>


end