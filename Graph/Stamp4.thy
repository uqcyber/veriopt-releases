theory Stamp4
imports
  Values2
  HOL.Lattices
begin


fun less_eq_alt :: "'a::ord \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "less_eq_alt (l1, u1) (l2, u2) = 
    (if l1 \<le> u1 \<and> l2 \<le> u2 then ((l1 \<ge> l2) \<and> (u1 \<le> u2)) else False)"

lemma 
  fixes l1 l2 u1 u2 :: int
  assumes "l1 \<le> u1 \<and> l2 \<le> u2"
  shows "{l1..u1} \<subseteq> {l2..u2} = ((l1 \<ge> l2) \<and> (u1 \<le> u2))"
  by (simp add: assms)

lemma 
  fixes l1 l2 u1 u2 :: int
  assumes "l1 \<le> u1 \<and> l2 \<le> u2"
  shows "{l1..u1} \<subseteq> {l2..u2} = less_eq_alt (l1, u1) (l2, u2)"
  by (simp add: assms)

  

datatype stamp =
  intstamp int64 int64

(*
fun join :: "stamp \<Rightarrow> stamp \<Rightarrow> stamp" (infix "\<squnion>" 60) where
  "join (intstamp l1 u1) (intstamp l2 u2) = intstamp (max l1 l2) (min u1 u2)"

fun meet :: "stamp \<Rightarrow> stamp \<Rightarrow> stamp" (infix "\<sqinter>" 60) where
  "meet (intstamp l1 u1) (intstamp l2 u2) = intstamp (min l1 l2) (max u1 u2)"

fun less :: "stamp \<Rightarrow> stamp \<Rightarrow> bool" (infix "<" 50) where
  "less (intstamp l1 u1) (intstamp l2 u2) = ({l1..u1} \<subset> {l2..u2})"

fun lesseq :: "stamp \<Rightarrow> stamp \<Rightarrow> bool" (infix "\<le>" 50) where
  "lesseq (intstamp l1 u1) (intstamp l2 u2) = ({l1..u1} \<subseteq> {l2..u2})"

definition empty_stamp ("\<bottom>" 50) where
  "empty_stamp = intstamp 0 0"

definition unrestricted_stamp ("\<top>" 50) where
  "unrestricted_stamp = intstamp 0 1"
*)

instantiation stamp :: order
begin

fun less_eq_stamp :: "stamp \<Rightarrow> stamp \<Rightarrow> bool" where
  "less_eq_stamp (intstamp l1 u1) (intstamp l2 u2) = ({l1..u1} \<subseteq> {l2..u2})"

fun less_stamp :: "stamp \<Rightarrow> stamp \<Rightarrow> bool" where
  "less_stamp (intstamp l1 u1) (intstamp l2 u2) = ({l1..u1} \<subset> {l2..u2})"

lemma less_le_not_le:
  fixes x y :: stamp
  shows "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  using less_eq_stamp.simps less_stamp.simps
  using stamp.exhaust subset_not_subset_eq by metis

lemma order_refl:
  fixes x :: stamp
  shows "x \<le> x"
  using less_eq_stamp.simps less_stamp.simps
  using dual_order.refl stamp.exhaust by metis

lemma order_trans:
  fixes x y z :: stamp
  shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
proof -
  fix x :: stamp and y :: stamp and z :: stamp
  assume "x \<le> y"
  assume "y \<le> z"
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust 
    by blast
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust 
    by blast
  obtain l3 u3 where zdef: "z = intstamp l3 u3"
    using stamp.exhaust 
    by blast
  have s1: "{l1..u1} \<le> {l2..u2}"
    using \<open>x \<le> y\<close> less_eq_stamp.simps xdef ydef by blast
  have s2: "{l2..u2} \<le> {l3..u3}"
    using \<open>y \<le> z\<close> less_eq_stamp.simps ydef zdef by blast
  from s1 s2 have "{l1..u1} \<le> {l3..u3}"
    by (meson dual_order.trans)
  then show "x \<le> z"
    using less_eq_stamp.simps
    using xdef zdef by presburger
qed

lemma antisym:
  fixes x y :: stamp
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
proof -
  fix x :: stamp
  fix y :: stamp
  assume xlessy: "x \<le> y"
  assume ylessx: "y \<le> x"
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by blast
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by blast
  
  from xlessy have s1: "{l1..u1} \<subseteq> {l2..u2}"
    using less_eq_stamp.simps
    using xdef ydef by blast
  from ylessx have s2: "{l2..u2} \<subseteq> {l1..u1}"
    using less_eq_stamp.simps
    using xdef ydef by blast
  have "{l1..u1} \<subseteq> {l2..u2} \<Longrightarrow> {l2..u2} \<subseteq> {l1..u1} \<Longrightarrow> {l1..u1} = {l2..u2}"
    by fastforce
  then have s3: "{l1..u1} = {l2..u2} \<Longrightarrow> (l1 = l2) \<and> (u1 = u2)"
    (* not true *)
    (* consider: 
       {1..0} = {-1..-1}
    *)
    sorry
  then have "(l1 = l2) \<and> (u1 = u2) \<Longrightarrow> x = y"
    using xdef ydef by fastforce
  then show "x = y"
    using s1 s2 s3 by fastforce
qed

instance
  apply standard
  using less_le_not_le apply simp
  using order_refl apply simp
  using order_trans apply simp
  using antisym by simp
end


instantiation stamp :: semilattice_inf
begin

notation inf (infix "\<sqinter>" 65)

fun inf_stamp :: "stamp \<Rightarrow> stamp \<Rightarrow> stamp" where
  "inf_stamp (intstamp l1 u1) (intstamp l2 u2) = intstamp (max l1 l2) (min u1 u2)"

lemma inf_le1: 
  fixes x y :: stamp
  shows "(x \<sqinter> y) \<le> x"
proof -
  fix x :: stamp
  fix y :: stamp
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by blast
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by blast
  have joindef: "x \<sqinter> y = intstamp (max l1 l2) (min u1 u2)"
    (is "?join = intstamp ?l3 ?u3")
    using inf_stamp.simps xdef ydef
    by force
  have leq: "{?l3..?u3} \<subseteq> {l1..u1}"
    by force
  have "(x \<sqinter> y) \<le> x = ({?l3..?u3} \<subseteq> {l1..u1})"
    using xdef joindef inf_stamp.simps
    by force
  then show "(x \<sqinter> y) \<le> x"
    using leq
    by fastforce
qed

lemma inf_le2:
  fixes x y :: stamp
  shows "(x \<sqinter> y) \<le> y"
proof -
  fix x :: stamp
  fix y :: stamp
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by blast
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by blast
  have joindef: "x \<sqinter> y = intstamp (max l1 l2) (min u1 u2)"
    (is "?join = intstamp ?l3 ?u3")
    using inf_stamp.simps xdef ydef
    by force
  have leq: "{?l3..?u3} \<subseteq> {l2..u2}"
    by force
  have "(x \<sqinter> y) \<le> y = ({?l3..?u3} \<subseteq> {l2..u2})"
    using ydef joindef
    by force
  then show "(x \<sqinter> y) \<le> y"
    using leq
    by fastforce
qed

lemma inf_greatest:
  fixes x y z :: stamp
  shows "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> (y \<sqinter> z)"
proof -
  fix x y z :: stamp
  assume xlessy: "x \<le> y"
  assume xlessz: "x \<le> z"
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by blast
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by blast
  obtain l3 u3 where zdef: "z = intstamp l3 u3"
    using stamp.exhaust by blast
  obtain l4 u4 where yzdef: "y \<sqinter> z = intstamp l4 u4"
    by (meson inf_stamp.elims)
  have max4: "l4 = max l2 l3"
    using yzdef ydef zdef inf_stamp.simps by simp
  have min4: "u4 = min u2 u3"
    using yzdef ydef zdef inf_stamp.simps by simp
  have "{l1..u1} \<subseteq> {l2..u2}"
    using xlessy xdef ydef
    using less_eq_stamp.simps by blast
  have "{l1..u1} \<subseteq> {l3..u3}"
    using xlessz xdef zdef
    using less_eq_stamp.simps by blast
  have leq: "{l1..u1} \<subseteq> {l4..u4}"
    using \<open>{l1..u1} \<subseteq> {l2..u2}\<close> \<open>{l1..u1} \<subseteq> {l3..u3}\<close> max4 min4 by auto
  have "x \<le> (y \<sqinter> z) = ({l1..u1} \<subseteq> {l4..u4})"
    by (simp add: xdef yzdef)
  then show "x \<le> (y \<sqinter> z)"
    using leq
    by fastforce
qed

instance
  apply standard
  using inf_le1 apply simp
  using inf_le2 apply simp
  using inf_greatest by simp
end

instantiation stamp :: semilattice_sup
begin

notation sup (infix "\<squnion>" 65)

fun sup_stamp :: "stamp \<Rightarrow> stamp \<Rightarrow> stamp" where
  "sup_stamp (intstamp l1 u1) (intstamp l2 u2) = intstamp (min l1 l2) (max u1 u2)"

lemma sup_ge1: 
  fixes x y :: stamp
  shows "x \<le> x \<squnion> y"
proof -
  fix x :: stamp
  fix y :: stamp
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by blast
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by blast
  have joindef: "x \<squnion> y = intstamp (min l1 l2) (max u1 u2)"
    (is "?join = intstamp ?l3 ?u3")
    using inf_stamp.simps xdef ydef
    by force
  have leq: "{l1..u1} \<subseteq> {?l3..?u3}"
    by simp
  have "x \<le> x \<squnion> y = ({l1..u1} \<subseteq> {?l3..?u3})"
    using xdef joindef inf_stamp.simps
    by force
  then show "x \<le> x \<squnion> y"
    using leq
    by fastforce
qed

lemma sup_ge2:
  fixes x y :: stamp
  shows "y \<le> x \<squnion> y"
proof -
  fix x :: stamp
  fix y :: stamp
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by blast
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by blast
  have joindef: "x \<squnion> y = intstamp (min l1 l2) (max u1 u2)"
    (is "?join = intstamp ?l3 ?u3")
    using inf_stamp.simps xdef ydef
    by force
  have leq: "{l2..u2} \<subseteq> {?l3..?u3}" (is "?subset_thesis")
    by simp
  have "?thesis = (?subset_thesis)"
    using ydef joindef sup_stamp.simps less_eq_stamp.simps
    by (metis Stamp4.sup_ge1 max.commute min.commute sup_stamp.elims)
  then show "?thesis"
    using leq
    by fastforce
qed

lemma sup_least:
  fixes x y z :: stamp
  shows "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> (y \<squnion> z) \<le> x"
proof -
  fix x y z :: stamp
  assume xlessy: "y \<le> x"
  assume xlessz: "z \<le> x"
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by blast
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by blast
  obtain l3 u3 where zdef: "z = intstamp l3 u3"
    using stamp.exhaust by blast
  have yzdef: "y \<squnion> z = intstamp (min l2 l3) (max u2 u3)"
    (is "?meet = intstamp ?l4 ?u4")
    using sup_stamp.simps
    by (simp add: ydef zdef)
  have s1: "{l2..u2} \<subseteq> {l1..u1}"
    using xlessy xdef ydef
    using less_eq_stamp.simps by blast
  have s2: "{l3..u3} \<subseteq> {l1..u1}"
    using xlessz xdef zdef
    using less_eq_stamp.simps by blast
  have leq: "{?l4..?u4} \<subseteq> {l1..u1}" (is ?subset_thesis)
    using s1 s2 sorry
  have "?thesis = ?subset_thesis"
    using yzdef xdef less_eq_stamp.simps sorry
  then show ?thesis
    using leq
    by fastforce
qed

instance
  apply standard
  using sup_ge1 apply simp
  using sup_ge2 apply simp
  using sup_least by simp
end

instantiation stamp :: bounded_lattice
begin

notation bot ("\<bottom>" 50)
notation top ("\<top>" 50)

definition width_min :: "nat \<Rightarrow> int64" where
  "width_min bits = ((2 ^ bits) div 2) * -1"

definition width_max :: "nat \<Rightarrow> int64" where
  "width_max bits = ((2 ^ bits) div 2) - 1"

lemma
  fixes x y :: int64
  assumes "x = (((2 ^ 64) div 2) * -1)"
  assumes "y = (((2 ^ 64) div 2) - 1)"
  shows "x < y"
  using assms sorry

definition "bot_stamp = intstamp (width_max 64) (width_min 64)"
definition "top_stamp = intstamp (width_min 64) (width_max 64)"

lemma bot_least:
  fixes a :: stamp
  shows "(\<bottom>) \<le> a"
  proof -
  obtain min max where bot_def:"\<bottom> = intstamp max min"
    (is "\<bottom> = intstamp ?max ?min")
    using bot_stamp_def 
    by force
  have "min < max"
    using bot_def
    unfolding bot_stamp_def
    width_min_def width_max_def
    sorry
  have "{?max..?min} = {}"
    sorry
  then show ?thesis
    sorry
qed

lemma top_greatest:
  fixes a :: stamp
  shows "a \<le> (\<top>)"
  sorry

instance
  apply standard
  using bot_least apply simp
  using top_greatest by simp
end


definition is_unrestricted :: "stamp \<Rightarrow> bool" where
  "is_unrestricted s = (\<top> = s)"

fun is_empty :: "stamp \<Rightarrow> bool" where
  "is_empty s = (\<bottom> = s)"

fun as_constant :: "stamp \<Rightarrow> Value option" where
  "as_constant (intstamp l u) = (if (card {l..u}) = 1
    then Some (IntVal64 (SOME x. x \<in> {l..u}))
    else None)"

definition always_distinct :: "stamp \<Rightarrow> stamp \<Rightarrow> bool" where
  "always_distinct stamp1 stamp2 = (\<bottom> = (stamp1 \<sqinter> stamp2))"

definition never_distinct :: "stamp \<Rightarrow> stamp \<Rightarrow> bool" where
  "never_distinct stamp1 stamp2 = 
    (as_constant stamp1 = as_constant stamp2 \<and> as_constant stamp1 \<noteq> None)"

fun valid_value :: "stamp => Value => bool" where
  "valid_value (intstamp l u) (IntVal64 v) = (v \<in> {l..u})"

lemma disjoint_empty:
  fixes x_stamp y_stamp :: stamp
  assumes "\<bottom> = x_stamp \<squnion> y_stamp"
  shows "\<not>(\<exists>x y. valid_value x_stamp x \<and> valid_value y_stamp y)"
  using assms sorry

end