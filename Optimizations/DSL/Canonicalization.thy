subsection \<open>Canonicalization DSL\<close>

theory Canonicalization
  imports
    Markup
    Phase
  keywords
    "phase" :: thy_decl and 
    "terminating" :: quasi_command and
    "print_phases" :: diag and
    "optimization" :: thy_goal_defn
begin

ML \<open>
datatype 'a Rewrite =
  Transform of 'a * 'a |
  Conditional of 'a * 'a * term |
  Sequential of 'a Rewrite * 'a Rewrite |
  Transitive of 'a Rewrite

type rewrite = {name: string, rewrite: term Rewrite}

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
  Outer_Syntax.command \<^command_keyword>\<open>phase\<close> "enter an optimization phase"
   (Parse.binding --| Parse.$$$ "terminating" -- Parse.const --| Parse.begin
     >> (Toplevel.begin_main_target true o RewritePhase.setup));

fun print_phases ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun print phase = RewritePhase.pretty phase ctxt
  in 
    map print (RewritePhase.phases thy)
  end

fun print_optimizations thy =
  print_phases thy |> Pretty.writeln_chunks

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_phases\<close>
    "print debug information for optimizations"
    (Scan.succeed
      (Toplevel.keep (print_optimizations o Toplevel.context_of)));
\<close>

ML_file "rewrites.ML"

fun rewrite_preservation :: "IRExpr Rewrite \<Rightarrow> bool" where
  "rewrite_preservation (Transform x y) = (y \<le> x)" |
  "rewrite_preservation (Conditional x y cond) = (cond \<longrightarrow> (y \<le> x))" |
  "rewrite_preservation (Sequential x y) = (rewrite_preservation x \<and> rewrite_preservation y)" |
  "rewrite_preservation (Transitive x) = rewrite_preservation x"

fun rewrite_termination :: "IRExpr Rewrite \<Rightarrow> (IRExpr \<Rightarrow> nat) \<Rightarrow> bool" where
  "rewrite_termination (Transform x y) trm = (trm y < trm x)" |
  "rewrite_termination (Conditional x y cond) trm = (cond \<longrightarrow> (trm y < trm x))" |
  "rewrite_termination (Sequential x y) trm = (rewrite_termination x trm \<and> rewrite_termination y trm)" |
  "rewrite_termination (Transitive x) trm = rewrite_termination x trm"

fun intval :: "Value Rewrite \<Rightarrow> bool" where
  "intval (Transform x y) = (x \<noteq> UndefVal \<and> y \<noteq> UndefVal \<longrightarrow> x = y)" |
  "intval (Conditional x y cond) = (cond \<longrightarrow> (x = y))" |
  "intval (Sequential x y) = (intval x \<and> intval y)" |
  "intval (Transitive x) = intval x"

ML \<open>
structure System : RewriteSystem =
struct
val preservation = @{const rewrite_preservation};
val termination = @{const rewrite_termination};
val intval = @{const intval};
end

structure DSL = DSL_Rewrites(System);

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>optimization\<close>
    "define an optimization and open proof obligation"
    (Parse_Spec.thm_name ":" -- Parse.term
        >> DSL.rewrite_cmd);
\<close>

end