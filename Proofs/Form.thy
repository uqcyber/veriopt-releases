subsection \<open>Formedness Properties\<close>

theory Form
imports
  Semantics.IREval
begin

definition wff_start where
  "wff_start g = (0 \<in> ids g \<and>
    is_StartNode (kind g 0))"

definition wff_closed where
  "wff_closed g = 
    (\<forall> n \<in> ids g .
      inputs g n \<subseteq> ids g \<and>
      succ g n \<subseteq> ids g \<and>
      kind g n \<noteq> NoNode)"

definition wff_phis where
  "wff_phis g = 
    (\<forall> n \<in> ids g.
      isPhiNodeType (kind g n) \<longrightarrow>
      length (ir_values (kind g n))
       = length (ir_ends 
           (kind g (ir_merge (kind g n)))))"

definition wff_ends where
  "wff_ends g = 
    (\<forall> n \<in> ids g .
      isAbstractEndNodeType (kind g n) \<longrightarrow>
      card (usages g n) > 0)"

text_raw \<open>\Snip{wff_graph}%\<close>
fun wff_graph :: "IRGraph \<Rightarrow> bool" where
  "wff_graph g = (wff_start g \<and> wff_closed g \<and> wff_phis g \<and> wff_ends g)"
text_raw \<open>\EndSnip\<close>

lemmas wff_folds =
  wff_graph.simps
  wff_start_def
  wff_closed_def
  wff_phis_def
  wff_ends_def

fun wff_stamps :: "IRGraph \<Rightarrow> bool" where
  "wff_stamps g = (\<forall> n \<in> ids g . 
    (\<forall> v m . (g m \<turnstile> (kind g n) \<mapsto> v) \<longrightarrow> valid_value (stamp g n) v))"

fun wff_stamp :: "IRGraph \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> bool" where
  "wff_stamp g s = (\<forall> n \<in> ids g . 
    (\<forall> v m . (g m \<turnstile> (kind g n) \<mapsto> v) \<longrightarrow> valid_value (s n) v))"

lemma wff_empty: "wff_graph start_end_graph"
  unfolding start_end_graph_def wff_folds by simp

lemma wff_eg2_sq: "wff_graph eg2_sq"
  unfolding eg2_sq_def wff_folds by simp


fun wff_values :: "IRGraph \<Rightarrow> bool" where
  "wff_values g = (\<forall> n \<in> ids g .
    (\<forall> v m . (g m \<turnstile> kind g n \<mapsto> v) \<longrightarrow> wff_value v))"

lemma wff_value_range:
  "b > 1 \<and> b \<in> int_bits_allowed \<longrightarrow> {v. wff_value (IntVal b v)} = {v. ((-(2^(b-1)) \<le> v) \<and> (v < (2^(b-1))))}"
  unfolding wff_value.simps
  by auto

lemma wff_value_bit_range:
  "b = 1 \<longrightarrow> {v. wff_value (IntVal b v)} = {0, 1}"
  unfolding wff_value.simps
  by auto

end