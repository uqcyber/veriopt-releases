(*  Title:      Optimizations/DSL/rewrites.ML
    Author:     Brae Webb

Generate proof obligation for expression rewrites.
*)

signature DSL_REWRITES =
sig
val of_term: string -> term -> rewrite;

val preservation_of: Proof.context -> rewrite -> term;
val termination_of: Proof.context -> rewrite -> term;
val code_of: Proof.context -> rewrite -> term;

val rewrite_cmd: (binding * Token.src list) * string -> Proof.context -> Proof.state;

end

structure DSL_Rewrites: DSL_REWRITES =
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
    (@{const Trueprop} $ (@{const rewrite_obligation} $ (to_term rewrite)))

fun termination_of' _ trm rewrite =
  case (#rewrite rewrite) of
    Transform (lhs, rhs) => (
      @{const Trueprop} 
      $ (Const ("Orderings.ord_class.less", @{typ "nat \<Rightarrow> nat \<Rightarrow> bool"})
      $ (trm $ rhs) $ (trm $ lhs)))
    | Conditional (lhs, rhs, condition) => (
      Const ("Pure.imp", @{typ "prop \<Rightarrow> prop \<Rightarrow> prop"})
      $ (@{const Trueprop} $ condition)
      $ (@{const Trueprop} $ (Const ("Orderings.ord_class.less", @{typ "nat \<Rightarrow> nat \<Rightarrow> bool"})
      $ (trm $ rhs) $ (trm $ lhs))))
    | _ => raise TERM ("rewrite termination generation not implemented", [])

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


fun rewrite_cmd
  ((bind: binding, _), opt: string) ctxt = 
  let
    val name = Binding.name_of bind;

    val term = Syntax.read_term ctxt opt;
    val rewrite = of_term name term;

    val preservation = preservation_of ctxt rewrite;
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
        snd (Local_Theory.note ((bind, ([]:Token.src list)), hd thms) lthy'')
      end
  in
    Proof.theorem NONE after_qed 
      [[(preservation, [preservation]), (termination, [termination])]] ctxt
  end

end