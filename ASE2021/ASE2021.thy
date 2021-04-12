theory ASE2021
  imports
    Optimizations.Canonicalization
begin

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

text_raw \<open>\Snip{StepSemantics}%\<close>
text \<open>
\induct{@{thm[mode=Rule] step.SignedRemNode [no_vars]}}{eval:rem}
\<close>
text_raw \<open>\EndSnip\<close>

end