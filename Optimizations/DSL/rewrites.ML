(*  Title:      Optimizations/DSL/rewrites.ML
    Author:     Brae Webb

Generate proof obligation for expression rewrites.
*)

signature RewriteSystem =
sig
val preservation: term;
val termination: term;
val intval: term;
end

signature DSL_REWRITES =
sig
val of_term: binding -> term -> rewrite;

val preservation_of: Proof.context -> rewrite -> term;
val termination_of: Proof.context -> rewrite -> term;
val code_of: Proof.context -> rewrite -> term;

val rewrite_cmd: (binding * Token.src list) * string -> Proof.context -> Proof.state;

end

functor DSL_Rewrites(System: RewriteSystem): DSL_REWRITES =
struct
fun of_term name term =
  case term of
    (((Const ("Markup.Rewrite.Transform", _)) $ lhs) $ rhs) => 
      {name=name, rewrite=Transform (lhs, rhs), proofs=[]}
    | ((((Const ("Markup.Rewrite.Conditional", _)) $ lhs) $ rhs) $ cond) => 
      {name=name, rewrite=Conditional (lhs, rhs, cond), proofs=[]}
    | _ => raise TERM ("optimization is not a rewrite", [term])

fun to_term rewrite = 
  case (#rewrite rewrite) of
    Transform (lhs, rhs) => 
      (Const ("Markup.Rewrite.Transform", @{typ "IRExpr => IRExpr => IRExpr Rewrite"})) $ lhs $ rhs
    | Conditional (lhs, rhs, cond) => 
      (Const ("Markup.Rewrite.Conditional", @{typ "IRExpr => IRExpr \<Rightarrow> bool \<Rightarrow> IRExpr Rewrite"})) $ lhs $ rhs $ cond
    | _ => raise TERM ("rewrite cannot be translated yet", [])

fun lhs (term:term) =
  case term of
  (((Const ("Markup.Rewrite.Transform", _)) $ lhs) $ _) => 
      lhs
    | ((((Const ("Markup.Rewrite.Conditional", _)) $ lhs) $ _) $ _) => 
      lhs
    | _ => raise TERM ("optimization is not a rewrite", [term])

fun rhs (term:term) =
  case term of
  (((Const ("Markup.Rewrite.Transform", _)) $ _) $ rhs) => 
      rhs
    | ((((Const ("Markup.Rewrite.Conditional", _)) $ _) $ rhs) $ _) => 
      rhs
    | _ => raise TERM ("optimization is not a rewrite", [term])

fun preservation_of ctxt rewrite =
  Syntax.check_prop ctxt 
    (@{const Trueprop} $ (System.preservation $ (to_term rewrite)))

fun termination_of' ctxt trm rewrite =
  Syntax.check_prop ctxt 
    (@{const Trueprop} $ (System.termination $ (to_term rewrite) $ trm))

fun intval_of ctxt term =
  Syntax.check_prop ctxt 
    (@{const Trueprop} $ (System.intval $ term))

fun value_def ctxt name rewrite =
  ((Const ("Pure.eq", @{typ "bool \<Rightarrow> bool \<Rightarrow> prop"})
  $ (Free ("val_" ^ (Binding.name_of name), @{typ "bool"}))
  $ (
      (((Const ("HOL.eq", @{typ "Value \<Rightarrow> Value \<Rightarrow> bool"}))
      $ (IntValMarkup.markup_expr [] ctxt [lhs rewrite])
      $ (IntValMarkup.markup_expr [] ctxt [rhs rewrite])))
    )))

fun val_def_const ctxt name rewrite =
  @{const Trueprop}
  $ ((Const ("HOL.eq", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"})
  $ (Free ("val_" ^ (Binding.name_of name), @{typ "bool"}))
  $ (
      ((Const ("HOL.eq", @{typ "int \<Rightarrow> int \<Rightarrow> bool"}))
      (*$ Var (("x", 0), @{typ int})*)
      $ @{term "(10::int) + (-(12::int))"}
      $ @{term "(10::int) + (-(12::int))"}))
    ))

fun word_def ctxt name rewrite =
  ((Const ("HOL.eq", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"})
  $ (Free ("word_" ^ name, @{typ "bool"}))
  $ (
      (@{const Trueprop}
      $ ((Const ("HOL.eq", @{typ "('a::len) word \<Rightarrow> 'a word \<Rightarrow> bool"}))
      $ (WordMarkup.markup_expr [] ctxt [lhs rewrite])
      $ (WordMarkup.markup_expr [] ctxt [rhs rewrite])))
    )))

fun termination_of ctxt rewrite =
  let
    val state = RewritePhase.current (Proof_Context.theory_of ctxt);
    val trm = (case state of
      NONE => raise TERM ("Optimization phase missing", []) |
      SOME phase => (#trm phase)
    );
  in
    termination_of' ctxt trm rewrite
  end

fun code_of _ rewrite =
  @{const Trueprop} 
  $ ((Const ("HOL.eq", @{typ "(IRExpr \<Rightarrow> IRExpr option) \<Rightarrow> (IRExpr \<Rightarrow> IRExpr option) \<Rightarrow> bool"})
  $ (Free ((Binding.name_of (#name rewrite)) ^ "_code", @{typ "IRExpr \<Rightarrow> IRExpr option"}))
  $ @{term \<open>\<lambda> (x::IRExpr) \<Rightarrow> (None::IRExpr option)\<close>}))


fun add_proofs (rewrite: rewrite) proofs =
  {name= #name rewrite, rewrite= #rewrite rewrite, proofs= proofs}

fun rewrite_cmd ((bind, options), opt) ctxt = 
  let
    val intval = case options of [[token]] => Token.content_of token = "intval" | _ => false;
    val name = Binding.name_of bind;

    val subgoals = case options of [[token]] => Token.content_of token = "subgoals" | _ => false;
    val raw_term = (Syntax.parse_term ctxt opt);

    val term = IRExprMarkup.markup_expr [] ctxt [raw_term];
    val rewrite = of_term bind term;

    val ctxt = (if subgoals then
      (Specification.abbreviation (Syntax.mode_default)
        NONE []
        (val_def_const ctxt (#name rewrite) raw_term)
        false ctxt)
        (*((Binding.prefix_name "val_" bind, []), value_def ctxt (#name rewrite) raw_term) ctxt)*)
      else ctxt);

    (*val ctxt = (if subgoals then
      snd (Specification.definition
        NONE [] []
        ((Binding.prefix_name "val_" bind, []), value_def ctxt (#name rewrite) raw_term) ctxt)
      else ctxt);*)

    (*val ctxt = (if subgoals then
      (Specification.abbreviation (Syntax.mode_default)
        NONE []
        (word_def ctxt (#name rewrite) raw_term)
        false ctxt)
      else ctxt);*)

    val intval_preservation = (if intval 
      then intval_of ctxt (IntValMarkup.markup_expr [term] ctxt [(Syntax.parse_term ctxt opt)])
      else @{term True})
    val extra = (if intval then [(intval_preservation, [intval_preservation])] else [])

    val preservation = preservation_of ctxt rewrite;
    val preservation = if intval 
      then @{term "Pure.imp"} $ intval_preservation $ preservation
      else preservation;
    val termination = termination_of ctxt rewrite;
    val code = code_of ctxt rewrite;

    val register = fn proofs => RewritePhase.register (bind, (add_proofs rewrite proofs));

    fun after_qed thms lthy =
      let
        val lthy' = Local_Theory.background_theory (register (hd thms)) lthy;

        val (_, lthy'') = Specification.definition
            NONE [] []
            ((Binding.suffix_name "_code" bind, []), code)
            lthy'
      in
        snd (Local_Theory.note ((bind, []), hd thms) lthy'')
      end

    val target = (Proof.theorem NONE after_qed 
        [extra @ [(preservation, [preservation]), (termination, [termination])]] ctxt);

    val apply = (Proof.apply 
      ((Method.Source (Token.make_src ("unfold_optimization", Position.start) [])),
        Position.no_range) target);

    val result = (case Seq.hd apply of
       Seq.Result r => r
       | Seq.Error _ => target);

    val apply = (Proof.apply
      ((Method.Source (Token.make_src ("unfold_size", Position.start) [])),
       Position.no_range) (Proof.defer 1 result));

    val result = (case Seq.hd apply of
       Seq.Result r => r
       | Seq.Error _ => result);
  in
    result
  end

end