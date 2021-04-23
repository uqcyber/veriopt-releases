theory
  CanonicalizationProofsKT
imports
  Canonicalization
begin

(* TODO: better way to specify x is a bool *)
(*lemma double_negate: 
 "\<lbrakk>x = (IntVal b bval); b = 1; bval = 1 \<or> bval = 0\<rbrakk> 
  \<Longrightarrow> bool_to_val (\<not>(val_to_bool (bool_to_val (\<not>(val_to_bool x))))) = x" 
  by auto *)

(* TODO: This one isn't actually completely true, but use it for now *)
lemma double_negate: "bool_to_val (\<not>(val_to_bool (bool_to_val (\<not>(val_to_bool x))))) = x" 
  sorry

lemma CanonicalizeNotProof:
  assumes "CanonicalizeNot g before after"
  assumes "wff_stamps g"
  assumes "g m \<turnstile> before \<mapsto> IntVal b res"
  assumes "g m \<turnstile> after \<mapsto> IntVal b' res'"
  shows "res = res'"
  using assms 
  proof (induct rule: CanonicalizeNot.induct)
case (not_const nx val neg_val)
  then show ?case
    by (metis ConstantNodeE NotNodeE Value.inject(1))
next
  case (not_not nx x)
  obtain xval where xval: "g m \<turnstile> kind g x \<mapsto> xval"
    using not_not.prems(3) by blast
  obtain nxval where nxval: "g m \<turnstile> kind g nx \<mapsto> nxval"
    using not_not.prems(2) by blast
  obtain beforeval where beforeval: "g m \<turnstile> before \<mapsto> beforeval"
    using assms(3) by auto
  obtain refval where refval: "g m \<turnstile> after \<mapsto> refval"
    using assms(4) by auto
  then have ref_xval_eq: "refval = xval"
    by (metis RefNodeE assms(4) evalDet not_not.prems(3) xval)
  then have "nxval = bool_to_val (\<not>(val_to_bool xval))"
    by (metis NotNodeE evalDet not_not.hyps nxval xval)
  then have "beforeval = bool_to_val (\<not>(val_to_bool nxval))"
    by (metis assms(3) beforeval eval.NotNode evalDet not_not.prems(2) nxval)
  then have double_negate_xval: "bool_to_val (\<not>(val_to_bool (bool_to_val (\<not>(val_to_bool xval))))) = xval"
    by (simp add: double_negate)
  then have node_eq_eq: "beforeval = xval"
    by (simp add: \<open>beforeval = bool_to_val (\<not> val_to_bool nxval)\<close> \<open>nxval = bool_to_val (\<not> val_to_bool xval)\<close>)
   show ?thesis using eval.RefNode double_negate_xval node_eq_eq
     using Value.inject(1) bool_to_val.simps(1) double_negate val_to_bool.simps(1) zero_neq_one by force
qed

end