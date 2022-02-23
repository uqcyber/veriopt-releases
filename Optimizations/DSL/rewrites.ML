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
val of_term: string -> term -> rewrite;

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
      {name=name, rewrite=Transform (lhs, rhs)}
    | ((((Const ("Markup.Rewrite.Conditional", _)) $ lhs) $ rhs) $ cond) => 
      {name=name, rewrite=Conditional (lhs, rhs, cond)}
    | _ => raise TERM ("optimization is not a rewrite", [term])

fun to_term rewrite = 
  case (#rewrite rewrite) of
    Transform (lhs, rhs) => 
      (Const ("Markup.Rewrite.Transform", @{typ "IRExpr => IRExpr => IRExpr Rewrite"})) $ lhs $ rhs
    | Conditional (lhs, rhs, cond) => 
      (Const ("Markup.Rewrite.Conditional", @{typ "IRExpr => IRExpr \<Rightarrow> bool \<Rightarrow> IRExpr Rewrite"})) $ lhs $ rhs $ cond
    | _ => raise TERM ("rewrite cannot be translated yet", [])

fun preservation_of ctxt rewrite =
  Syntax.check_prop ctxt 
    (@{const Trueprop} $ (System.preservation $ (to_term rewrite)))

fun termination_of' ctxt trm rewrite =
  Syntax.check_prop ctxt 
    (@{const Trueprop} $ (System.termination $ (to_term rewrite) $ trm))

fun intval_of ctxt term =
  Syntax.check_prop ctxt 
    (@{const Trueprop} $ (System.intval $ term))

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
  $ (Free ((#name rewrite) ^ "_code", @{typ "IRExpr \<Rightarrow> IRExpr option"}))
  $ @{term \<open>\<lambda> (x::IRExpr) \<Rightarrow> (None::IRExpr option)\<close>}))


fun rewrite_cmd ((bind, options), opt) ctxt = 
  let
    val intval = case options of [[token]] => Token.content_of token = "intval" | _ => false;
    val name = Binding.name_of bind;
    
    val term = IRExprMarkup.markup_expr [] ctxt [(Syntax.parse_term ctxt opt)];
    val rewrite = of_term name term;

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

    val register = RewritePhase.register (bind, rewrite);

    fun after_qed thms lthy =
      let
        val lthy' = Local_Theory.background_theory register lthy;

        val (_, lthy'') = Specification.definition
            NONE [] []
            ((Binding.suffix_name "_code" bind, []), code)
            lthy'
      in
        snd (Local_Theory.note ((bind, []), hd thms) lthy'')
      end
  in
    Proof.theorem NONE after_qed 
      [extra @ [(preservation, [preservation]), (termination, [termination])]] ctxt
  end

end