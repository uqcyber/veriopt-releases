subsection \<open>Stuttering\<close>

theory Stuttering
  imports
    Semantics.IRStepObj2
begin

inductive stutter:: "IRGraph \<Rightarrow> MapState \<Rightarrow> FieldRefHeap \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool" ("_ _ _ \<turnstile> _ \<leadsto> _" 55)
  for g m h where

  StutterStep:
  "\<lbrakk>g \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)\<rbrakk>
   \<Longrightarrow> g m h \<turnstile> nid \<leadsto> nid'" |

  Transitive:
  "\<lbrakk>g \<turnstile> (nid,m,h) \<rightarrow> (nid'',m,h);
    g m h \<turnstile> nid'' \<leadsto> nid'\<rbrakk>
   \<Longrightarrow> g m h \<turnstile> nid \<leadsto> nid'"

lemma stuttering_successor:
  assumes "(g \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h))"
  shows "{P'. (g m h \<turnstile> nid \<leadsto> P')} = {nid'} \<union> {nid''. (g m h \<turnstile> nid' \<leadsto> nid'')}"
proof -
  have nextin: "nid' \<in> {P'. (g m h \<turnstile> nid \<leadsto> P')}"
    using assms StutterStep by blast
  have nextsubset: "{nid''. (g m h \<turnstile> nid' \<leadsto> nid'')} \<subseteq> {P'. (g m h \<turnstile> nid \<leadsto> P')}"
    by (metis Collect_mono assms stutter.Transitive)
  have "\<forall>n \<in> {P'. (g m h \<turnstile> nid \<leadsto> P')} . n = nid' \<or> n \<in> {nid''. (g m h \<turnstile> nid' \<leadsto> nid'')}"
    using stepDet
    by (metis (no_types, lifting) Pair_inject assms mem_Collect_eq stutter.simps)
  then show ?thesis
    using insert_absorb mk_disjoint_insert nextin nextsubset by auto
qed

end