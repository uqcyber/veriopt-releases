section \<open>Proof Infrastructure\<close>
subsection \<open>Bisimulation\<close>

theory Bisimulation
imports
  Stuttering
begin

(* WIP strong bisimilar
fun strongly_bisimilar :: "
(IRGraph \<times> ID \<times> MapState \<times> FieldRefHeap) rel
\<Rightarrow> (IRGraph \<times> ID \<times> MapState \<times> FieldRefHeap)
\<Rightarrow> (IRGraph \<times> ID \<times> MapState \<times> FieldRefHeap)
\<Rightarrow> bool"
  where
  "strongly_bisimilar \<R> (g1, nid1, m1, h1) (g2, nid2, m2, h2) =
    ((((g1, nid1, m1, h1), (g2, nid2, m2, h2)) \<in> \<R>) \<longrightarrow>
    ((\<forall>P'. (g1 \<turnstile> (nid1, m1, h1) \<rightarrow> P') \<longrightarrow> (\<exists>Q' . (g2 \<turnstile> (nid2, m2, h2) \<rightarrow> Q') \<and> ((g1,P'), (g2,Q')) \<in> \<R>)) \<and>
    (\<forall>Q'. (g2 \<turnstile> (nid2, m2, h2) \<rightarrow> Q') \<longrightarrow> (\<exists>P' . (g1 \<turnstile> (nid1, m1, h1) \<rightarrow> P') \<and> ((g1,P'), (g2,Q')) \<in> \<R>))))"
*)

inductive weak_bisimilar :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool"
  ("_ . _ \<sim> _") for nid where
  "\<lbrakk>\<forall>P'. (g m h \<turnstile> nid \<leadsto> P') \<longrightarrow> (\<exists>Q' . (g' m h \<turnstile> nid \<leadsto> Q') \<and> P' = Q');
    \<forall>Q'. (g' m h \<turnstile> nid \<leadsto> Q') \<longrightarrow> (\<exists>P' . (g m h \<turnstile> nid \<leadsto> P') \<and> P' = Q')\<rbrakk>
  \<Longrightarrow> nid . g \<sim> g'"

text \<open>A strong bisimilution between no-op transitions\<close>
inductive strong_noop_bisimilar :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool"
  ("_ | _ \<sim> _") for nid where
  "\<lbrakk>\<forall>P'. (g \<turnstile> (nid, m, h) \<rightarrow> P') \<longrightarrow> (\<exists>Q' . (g' \<turnstile> (nid, m, h) \<rightarrow> Q') \<and> P' = Q');
    \<forall>Q'. (g' \<turnstile> (nid, m, h) \<rightarrow> Q') \<longrightarrow> (\<exists>P' . (g \<turnstile> (nid, m, h) \<rightarrow> P') \<and> P' = Q')\<rbrakk>
  \<Longrightarrow> nid | g \<sim> g'"

lemma lockstep_strong_bisimilulation:
  assumes "g' = replace_node nid node g"
  assumes "g \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  assumes "g' \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "nid | g \<sim> g'"
  using assms(2) assms(3) stepDet strong_noop_bisimilar.simps by blast

lemma no_step_bisimulation:
  assumes "\<forall>m h nid' m' h'. \<not>(g \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h'))"
  assumes "\<forall>m h nid' m' h'. \<not>(g' \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h'))"
  shows "nid | g \<sim> g'"
  using assms
  by (simp add: assms(1) assms(2) strong_noop_bisimilar.intros)

end