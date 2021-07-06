theory ValidationSnippets
  imports
    Tests.UnitTesting
    Graph.Values2
begin

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

text_raw \<open>\Snip{StepSemantics}%\<close>
text \<open>
@{thm[display,margin=60] intval_mod.simps(1)}

\induct{@{thm[mode=Rule] step.SignedRemNode [no_vars]}}{eval:rem}
\<close>
text_raw \<open>\EndSnip\<close>

(* moduloSnippet not checked in
text_raw \<open>\Snip{ModuloSnippet}%
@{thm[display,margin=80] moduloSnippet_def}
\EndSnip\<close>
*)

text_raw \<open>\Snip{ModuloTestSnippet}%
@{theory_text "static_test moduloSnippet [(IntVal 32 (1)), (Intval 32 (-2147483648))] (IntVal 32 (1))"}
\EndSnip\<close>

end