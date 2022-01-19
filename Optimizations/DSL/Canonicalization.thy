theory Canonicalization
  imports
    Markup
    Phase
  keywords
    "phase" :: thy_decl and 
    "trm" :: quasi_command and
    "print_phases" :: diag and
    "optimization" :: thy_goal_defn
begin

fun rewrite_obligation :: "IRExpr Rewrite \<Rightarrow> bool" where
  "rewrite_obligation (Transform x y) = (y \<le> x)" |
  "rewrite_obligation (Conditional x y cond) = (cond \<longrightarrow> (y \<le> x))" |
  "rewrite_obligation (Sequential x y) = (rewrite_obligation x \<and> rewrite_obligation y)" |
  "rewrite_obligation (Transitive x) = rewrite_obligation x"

ML \<open>
datatype 'a Rewrite =
  Transform of 'a * 'a |
  Conditional of 'a * 'a * term |
  Sequential of 'a Rewrite * 'a Rewrite |
  Transitive of 'a Rewrite

type rewrite =
  {name: string, rewrite: term Rewrite}

structure RewriteRule : Rule =
struct
type T = rewrite;

fun pretty_rewrite ctxt (Transform (from, to)) = 
      Pretty.block [
        Syntax.pretty_term ctxt from,
        Pretty.str " \<mapsto> ",
        Syntax.pretty_term ctxt to
      ]
  | pretty_rewrite ctxt (Conditional (from, to, cond)) = 
      Pretty.block [
        Syntax.pretty_term ctxt from,
        Pretty.str " \<mapsto> ",
        Syntax.pretty_term ctxt to,
        Pretty.str " when ",
        Syntax.pretty_term ctxt cond
      ]
  | pretty_rewrite _ _ = Pretty.str "not implemented"

fun pretty ctxt t =
  Pretty.block [
    Pretty.str ((#name t) ^ ": "),
    pretty_rewrite ctxt (#rewrite t)
  ]
end

structure RewritePhase = DSL_Phase(RewriteRule);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>phase\<close> "instantiate and prove type arity"
   (Parse.binding --| Parse.$$$ "trm" -- Parse.const --| Parse.begin
     >> (fn (name, trm) => Toplevel.begin_main_target true (RewritePhase.setup (name, trm))));

fun print_phases ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun print phase = RewritePhase.pretty phase ctxt
  in 
    map print (RewritePhase.phases thy)
  end

fun apply_print_optimizations thy =
  print_phases thy |> Pretty.writeln_chunks

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_phases\<close>
    "print debug information for optimizations"
    (Scan.succeed
      (Toplevel.keep (apply_print_optimizations o Toplevel.context_of)));
\<close>

ML_file "rewrites.ML"

ML \<open>
val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>optimization\<close>
    "define an optimization and open proof obligation"
    (Parse_Spec.thm_name ":" -- Parse.term
        >> DSL_Rewrites.rewrite_cmd);
\<close>

end