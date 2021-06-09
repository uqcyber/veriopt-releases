section \<open>Stamps: Type and Range Information\<close>

theory Stamp4
imports
  Values2
  HOL.Lattices
begin

subsection \<open>Void Stamp\<close>
text \<open>
The VoidStamp represents a type with no associated values.
The VoidStamp lattice is therefore a simple single element lattice.
\<close>
datatype void =
  VoidStamp

instantiation void :: order
begin

definition less_eq_void :: "void \<Rightarrow> void \<Rightarrow> bool" where
  "less_eq_void a b = True"

definition less_void :: "void \<Rightarrow> void \<Rightarrow> bool" where
  "less_void a b = False"

instance
  apply standard
     apply (simp add: less_eq_void_def less_void_def)
    apply (simp add: less_eq_void_def)
   apply (simp add: less_eq_void_def)
  by (metis (full_types) void.exhaust)

end

instantiation void :: semilattice_inf
begin

definition inf_void :: "void \<Rightarrow> void \<Rightarrow> void" where
  "inf_void a b = VoidStamp"

instance
  apply standard
    apply (simp add: less_eq_void_def)
   apply (simp add: less_eq_void_def)
  by (metis (mono_tags) void.exhaust)

end

instantiation void :: semilattice_sup
begin

definition sup_void :: "void \<Rightarrow> void \<Rightarrow> void" where
  "sup_void a b = VoidStamp"

instance
  apply standard
    apply (simp add: less_eq_void_def)
   apply (simp add: less_eq_void_def)
  by (metis (mono_tags) void.exhaust)

end

instantiation void :: bounded_lattice
begin

definition bot_void :: "void" where
  "bot_void = VoidStamp"

definition top_void :: "void" where
  "top_void = VoidStamp"

instance
  apply standard
   apply (simp add: less_eq_void_def)
  by (simp add: less_eq_void_def)

end

text \<open>Definition of the stamp type\<close>
datatype stamp =
  intstamp int64 int64 \<comment>\<open>Type: Integer; Range: Lower Bound \& Upper Bound\<close>
(*
  | floatstamp \<comment>\<open>Type: Float; Range: Lower Bound \& Upper Bound\<close>
  | objectstamp classname \<comment>\<open>Type: Object Instance; Range: Upper Bound Superclass\<close>
*)

subsection \<open>Stamp Lattice\<close>

text_raw \<open>\input{lattice}\\\<close>

subsubsection \<open>Stamp Order\<close>
text \<open>
Defines an ordering on the stamp type.

One stamp is less than another if the valid values
for the stamp are a strict subset of the other stamp.
\<close>
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

subsubsection \<open>Stamp Join\<close>
text \<open>
Defines the @{emph \<open>join\<close>} operation for stamps.

For any two stamps, the @{emph \<open>join\<close>} is defined as the intersection
of the valid values for the stamp.
\<close>
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


subsubsection \<open>Stamp Meet\<close>
text \<open>
Defines the @{emph \<open>meet\<close>} operation for stamps.

For any two stamps, the @{emph \<open>meet\<close>} is defined as the union
of the valid values for the stamp.
\<close>
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
  shows "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> ((y \<squnion> z) \<le> x)"
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
    using s1 s2 unfolding atLeastatMost_subset_iff
    (* why is this such a hard proof? *)
    by (metis (no_types, hide_lams) inf.orderE inf_stamp.simps max.bounded_iff max.cobounded2 min.bounded_iff min.cobounded2 stamp.inject xdef xlessy xlessz ydef zdef)
  have "(y \<squnion> z \<le> x) = ?subset_thesis"
    using yzdef xdef less_eq_stamp.simps 
    by simp
  then show "(y \<squnion> z \<le> x)"
    using leq by fastforce
qed

instance
  apply standard
  using sup_ge1 apply simp
  using sup_ge2 apply simp
  using sup_least by simp
end


subsubsection \<open>Stamp Bounds\<close>
text \<open>
Defines the top and bottom elements of the stamp lattice.

This poses an interesting question as our stamp type is a
union of the various @{emph \<open>Stamp\<close>} subclasses, e.g.
@{emph \<open>IntegerStamp\<close>}, @{emph \<open>ObjectStamp\<close>}, etc.

Each subclass should preferably have its own unique
top and bottom element, i.e. An @{emph \<open>IntegerStamp\<close>}
would have the top element of the full range of integers
allowed by the bit width and a bottom of a range with no integers.
While the @{emph \<open>ObjectStamp\<close>} should have @{emph \<open>Object\<close>}
as the top and @{emph \<open>Void\<close>} as the bottom element.
\<close>
instantiation stamp :: bounded_lattice
begin

notation bot ("\<bottom>" 50)
notation top ("\<top>" 50)

definition width_min :: "nat \<Rightarrow> int64" where
  "width_min bits = -(2^(bits-1))"

definition width_max :: "nat \<Rightarrow> int64" where
  "width_max bits = (2^(bits-1)) - 1"

value "(sint (width_min 64), sint (width_max 64))"
value "max_word::int64"

lemma
  assumes "x = width_min 64"
  assumes "y = width_max 64"
  shows "sint x < sint y"
  using assms unfolding width_min_def width_max_def by simp

text \<open>
Note that this definition is valid for unsigned integers only.

The bottom and top element for signed integers would be
(- 9223372036854775808, 9223372036854775807).

For unsigned we have
(0, 18446744073709551615).

For Java we are likely to be more concerned with signed integers.
To use the appropriate bottom and top for signed integers we
would need to change our definition of less\_eq from
{l1..u1} <= {l2..u2}
to
{sint l1..sint u1} <= {sint l2..sint u2}

We may still find an unsigned integer stamp useful.
I plan to investigate the Java code to see if this is useful
and then apply the changes to switch to signed integers.
\<close>
definition "bot_stamp = intstamp max_word 0"
definition "top_stamp = intstamp 0 max_word"

lemma bot_least:
  fixes a :: stamp
  shows "(\<bottom>) \<le> a"
proof -
  obtain min max where bot_def:"\<bottom> = intstamp max min"
    using bot_stamp_def 
    by force
  have "min < max"
    using bot_def
    unfolding bot_stamp_def width_min_def width_max_def
    using word_gt_0 by fastforce
  then have "{max..min} = {}"
    using bot_def
    unfolding bot_stamp_def width_min_def width_max_def
    by auto
  then show ?thesis
    unfolding bot_stamp_def
    using less_eq_stamp.simps
    by (simp add: stamp.induct)
qed

lemma top_greatest:
  fixes a :: stamp
  shows "a \<le> (\<top>)"
proof -
  obtain min max where top_def:"\<top> = intstamp min max"
    using top_stamp_def 
    by force
  have max_is_max: "\<not>(\<exists> n. n > max)"
    by (metis stamp.inject top_def top_stamp_def word_order.extremum_strict)
  have min_is_min: "\<not>(\<exists> n. n < min)"
    by (metis not_less_iff_gr_or_eq stamp.inject top_def top_stamp_def word_coorder.not_eq_extremum)
  have "\<not>(\<exists> l u. {min..max} < {l..u})"
    using max_is_max min_is_min
    by (metis atLeastatMost_psubset_iff not_less)
  then show ?thesis
    unfolding top_stamp_def
    using less_eq_stamp.simps
    using less_eq_stamp.elims(3) by fastforce
qed

instance
  apply standard
  using bot_least apply simp
  using top_greatest by simp
end


subsection \<open>Java Stamp Methods\<close>
text \<open>
The following are methods from the Java Stamp class,
they are the methods primarily used for optimizations.
\<close>
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


subsection \<open>Mapping to Values\<close>
fun valid_value :: "stamp => Value => bool" where
  "valid_value (intstamp l u) (IntVal64 v) = (v \<in> {l..u})" |
  "valid_value (intstamp l u) _ = False"

text \<open>
The @{const valid_value} function is used to map a stamp instance
to the values that are allowed by the stamp.

It would be nice if there was a slightly more integrated way
to perform this mapping as it requires some infrastructure
to prove some fairly simple properties.
\<close>
lemma bottom_range_empty:
  "\<not>(valid_value (\<bottom>) v)"
  unfolding bot_stamp_def
  using valid_value.elims(2) by fastforce

lemma join_values:
  assumes "joined = x_stamp \<sqinter> y_stamp"
  shows "valid_value joined x \<longleftrightarrow> (valid_value x_stamp x \<and> valid_value y_stamp x)"
proof (cases x)
  case UndefVal
  then show ?thesis
    using valid_value.elims(2) by blast
next
  case (IntVal32 x2)
  then show ?thesis
    using valid_value.elims(2) by blast
next
  case (IntVal64 x3)
  obtain lx ux where xdef: "x_stamp = intstamp lx ux"
    using stamp.exhaust by blast
  obtain ly uy where ydef: "y_stamp = intstamp ly uy"
    using stamp.exhaust by blast
  obtain v where "x = IntVal64 v"
    using IntVal64 by blast
  have "joined = intstamp (max lx ly) (min ux uy)"
    (is "joined = intstamp ?lj ?uj")
    by (simp add: xdef ydef assms)
  then have "valid_value joined (IntVal64 v) = (v \<in> {?lj..?uj})"
    by simp
  then show ?thesis
    using \<open>x = IntVal64 v\<close> xdef ydef by force
next
  case (FloatVal x4)
  then show ?thesis
    using valid_value.elims(2) by blast
next
  case (ObjRef x5)
  then show ?thesis
    using valid_value.elims(2) by blast
next
  case (ObjStr x6)
  then show ?thesis
    using valid_value.elims(2) by blast
qed

lemma disjoint_empty:
  fixes x_stamp y_stamp :: stamp
  assumes "\<bottom> = x_stamp \<sqinter> y_stamp"
  shows "\<not>(valid_value x_stamp x \<and> valid_value y_stamp x)"
  using assms bottom_range_empty join_values
  by blast


experiment begin
text \<open>A possible equivalent alternative to the definition of less\_eq\<close>
fun less_eq_alt :: "'a::ord \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "less_eq_alt (l1, u1) (l2, u2) = ((\<not> l1 \<le> u1) \<or> l2 \<le> l1 \<and> u1 \<le> u2)"

text \<open>Proof equivalence\<close>
lemma 
  fixes l1 l2 u1 u2 :: int
  assumes "l1 \<le> u1 \<and> l2 \<le> u2"
  shows "{l1..u1} \<subseteq> {l2..u2} = ((l1 \<ge> l2) \<and> (u1 \<le> u2))"
  by (simp add: assms)

lemma 
  fixes l1 l2 u1 u2 :: int
  shows "{l1..u1} \<subseteq> {l2..u2} = less_eq_alt (l1, u1) (l2, u2)"
  by simp
end



subsection \<open>Generic Integer Stamp\<close>

text \<open>
Experimental definition of integer stamps generically,
restricting the datatype to only allow valid ranges and
the bottom integer element (max_int..min_int).
\<close>

definition int_bottom :: "'a::len word \<times> 'a word" where
  "int_bottom = ((2 ^ (LENGTH('a) - 1)) - 1, -(2 ^ (LENGTH('a) - 1)))"

definition int_top :: "'a::len word \<times> 'a word" where
  "int_top = (-(2 ^ (LENGTH('a) - 1)), (2 ^ (LENGTH('a) - 1)) - 1)"

value "int_bottom::(32 word \<times> 32 word)"
value "sint (2147483647::32 word)"
value "sint (2147483648::32 word)"


typedef (overloaded) ('a::len) intstamp = 
  "{bounds :: ('a word, 'a word) prod . (sint (fst bounds) < sint (snd bounds) \<or> bounds = int_bottom)}"
proof -
  show ?thesis
    by (smt (z3) mem_Collect_eq prod.sel(1) prod.sel(2) signed_minus_1 sint_0)
qed

setup_lifting type_definition_intstamp

lift_definition lower :: "('a::len) intstamp \<Rightarrow> 'a word"
  is "prod.fst \<circ> Rep_intstamp" .

lift_definition upper :: "('a::len) intstamp \<Rightarrow> 'a word"
  is "prod.snd \<circ> Rep_intstamp" .

lift_definition lower_int :: "('a::len) intstamp \<Rightarrow> int"
  is "sint \<circ> prod.fst" .

lift_definition upper_int :: "('a::len) intstamp \<Rightarrow> int"
  is "sint \<circ> prod.snd" .

lift_definition range :: "('a::len) intstamp \<Rightarrow> int set"
  is "\<lambda> (l, u). {sint l..sint u}" .

lift_definition bounds :: "('a::len) intstamp \<Rightarrow> ('a word \<times> 'a word)"
  is Rep_intstamp .

lift_definition is_bottom :: "('a::len) intstamp \<Rightarrow> bool"
  is "\<lambda> x. x = int_bottom" .

lift_definition from_bounds :: "('a::len word \<times> 'a word) \<Rightarrow> 'a intstamp"
  is "Abs_intstamp" .

instantiation intstamp :: (len) order
begin

definition less_eq_intstamp :: "'a intstamp \<Rightarrow> 'a intstamp \<Rightarrow> bool" where
  "less_eq_intstamp s1 s2 = (range s1 \<subseteq> range s2)"

definition less_intstamp :: "'a intstamp \<Rightarrow> 'a intstamp \<Rightarrow> bool" where
  "less_intstamp s1 s2 = (range s1 \<subset> range s2)"

lemma bottom_is_bottom:
  assumes "is_bottom s"
  shows "s \<le> a"
proof -
  have "bounds s = int_bottom"
    by (metis assms bounds.transfer is_bottom.rep_eq)
  obtain min max where "bounds s = (max, min)"
    by fastforce
  have "sint min < sint max"
    sorry
  then have "range s = {}"
    unfolding range_def bounds_def
    by (simp add: \<open>bounds s = (max, min)\<close> bounds.transfer)
  then show ?thesis
    by (simp add: Stamp4.less_eq_intstamp_def)
qed

lemma bounds_has_value:
  fixes x y :: int
  assumes "x < y"
  shows "card {x..y} > 0"
  using assms by auto

lemma bounds_has_no_value:
  fixes x y :: int
  assumes "x < y"
  shows "card {y..x} = 0"
  using assms by auto

lemma bottom_unique: 
  fixes a s :: "'a intstamp"
  assumes "is_bottom s"
  shows "a \<le> s \<longleftrightarrow> is_bottom a"
proof -
  have "\<forall>x. sint (fst (bounds x)) < sint (snd (bounds x)) \<or> is_bottom x"
    unfolding bounds_def is_bottom_def
    using Rep_intstamp by auto
  then have "\<forall>x. (card (range x)) > 0 \<or> is_bottom x"
    unfolding range_def using bounds_has_value
    by (smt (z3) bounds.abs_eq case_prod_beta' range.rep_eq range_def)
  obtain min max where boundsdef: "bounds s = (max, min)"
    by fastforce
  have nooverlap: "sint min < sint max"
    sorry
  have "range s = {sint max..sint min}"
    by (simp add: bounds.transfer boundsdef range.rep_eq)
  then have "card (range s) = 0"
    using nooverlap bounds_has_no_value by simp
  then have "\<forall>x. (card (range x)) > 0 \<longrightarrow> s < x"
    using \<open>Stamp4.range s = {sint max..sint min}\<close> atLeastatMost_empty less_intstamp_def by auto
  then show ?thesis
    by (meson \<open>\<forall>x. 0 < card (Stamp4.range x) \<or> is_bottom x\<close> bottom_is_bottom leD less_eq_intstamp_def less_intstamp_def)
qed


lemma bottom_antisym:
  assumes "is_bottom x"
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  using assms proof (cases "is_bottom y")
case True
  then show ?thesis
    by (metis Rep_intstamp_inverse assms is_bottom.rep_eq)
next
  case False
  assume "y \<le> x"
  have "\<not>(y \<le> x)"
    using bottom_unique False assms
    by simp
  then show ?thesis
    using \<open>y \<le> x\<close> by auto
qed

lemma int_antisym:
  fixes x y :: "'a intstamp"
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
proof -
  fix x :: "'a intstamp"
  fix y :: "'a intstamp"
  assume xlessy: "x \<le> y"
  assume ylessx: "y \<le> x"
  obtain l1 u1 where xdef: "bounds x = (l1, u1)"
    by fastforce
  obtain l2 u2 where ydef: "bounds y = (l2, u2)"
    by fastforce
  
  from xlessy have s1: "{sint l1..sint u1} \<subseteq> {sint l2..sint u2}" (is "?xlessy")
    using xdef ydef unfolding bounds_def range_def less_eq_intstamp_def
    by simp
  from ylessx have s2: "{sint l2..sint u2} \<subseteq> {sint l1..sint u1}" (is "?ylessx")
    using xdef ydef unfolding bounds_def range_def less_eq_intstamp_def
    by simp
  show "x = y" proof (cases "is_bottom x")
    case True
    then show ?thesis using bottom_antisym xlessy ylessx
      by simp
  next
    case False
    then show ?thesis sorry
  qed
qed

instance
  apply standard
     apply (simp add: less_eq_intstamp_def less_intstamp_def less_le_not_le)
  apply blast
  using less_eq_intstamp_def apply force
  using less_eq_intstamp_def apply force
  by (simp add: int_antisym)
end


instantiation intstamp :: (len) semilattice_inf
begin

notation inf (infix "\<sqinter>" 65)

definition join_bounds :: "'a intstamp \<Rightarrow> 'a intstamp \<Rightarrow> ('a word \<times> 'a word)" where
  "join_bounds s1 s2 = (word_of_int (max (lower_int s1) (lower_int s2)), word_of_int (min (upper_int s1) (upper_int s2)))"

definition join_or_bottom :: "'a intstamp \<Rightarrow> 'a intstamp \<Rightarrow> ('a word \<times> 'a word)" where
  "join_or_bottom s1 s2 = (let bound = (join_bounds s1 s2) in 
    if sint (fst bound) \<ge> sint (snd bound) then int_bottom else bound)"

definition inf_intstamp :: "'a intstamp \<Rightarrow> 'a intstamp \<Rightarrow> 'a intstamp" where
  "inf_intstamp s1 s2 = from_bounds (join_or_bottom s1 s2)"

lemma always_valid:
  fixes s1 s2 :: "'a intstamp"
  shows "Rep_intstamp (Abs_intstamp (join_or_bottom s1 s2)) = join_or_bottom s1 s2"
  unfolding join_or_bottom_def join_bounds_def
  by (simp add: Abs_intstamp_inverse)

lemma invalid_join:
  fixes s1 s2 :: "'a intstamp"
  assumes "bound = join_bounds s1 s2"
  assumes "sint (fst bound) \<ge> sint (snd bound)"
  shows "from_bounds int_bottom = s1 \<sqinter> s2"
  using assms(1) assms(2) inf_intstamp_def join_or_bottom_def by presburger

lemma unfold_bounds:
  "bounds x = (lower x, upper x)"
  by (simp add: bounds.transfer lower.rep_eq upper.rep_eq)

lemma int_inf_le1: 
  fixes x y :: "'a intstamp"
  shows "(x \<sqinter> y) \<le> x"
proof (cases "is_bottom (x \<sqinter> y)")
  case True
  then show ?thesis
    by (simp add: bottom_is_bottom)
next
  case False
  then show ?thesis
  using False proof -
  obtain l1 u1 where xdef: "lower_int x = l1 \<and> upper_int x = u1"
    by fastforce
  obtain l2 u2 where ydef: "lower_int y = l2 \<and> upper_int y = u2"
    by fastforce
  have unwrappingl: "sint (word_of_int (max l1 l2)) = max l1 l2"
    using xdef unfolding lower_int_def upper_int_def sorry
  have unwrappingu: "sint (word_of_int (max u1 u2)) = max u1 u2"
    using xdef unfolding lower_int_def upper_int_def sorry
  have joindef: "x \<sqinter> y = from_bounds (word_of_int (max l1 l2), word_of_int (min u1 u2))"
    (is "?join = from_bounds (word_of_int ?l3, word_of_int ?u3)")
    using False
    by (smt (z3) Stamp4.join_or_bottom_def always_valid from_bounds.abs_eq inf_intstamp_def is_bottom.rep_eq join_bounds_def xdef ydef)
  have leq: "{?l3..?u3} \<subseteq> {l1..u1}"
    by simp
  have "(x \<sqinter> y) \<le> x = ({?l3..?u3} \<subseteq> {l1..u1})"
    using xdef joindef range_def less_eq_intstamp_def sorry
  then show "(x \<sqinter> y) \<le> x"
    using leq
    by fastforce
qed
qed

lemma int_inf_le2: 
  fixes x y :: "'a intstamp"
  shows "(x \<sqinter> y) \<le> y"
  sorry  

lemma int_inf_greatest:
  fixes x y :: "'a intstamp"
  shows "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
  sorry

instance
  apply standard
    apply (simp add: local.int_inf_le1)
   apply (simp add: local.int_inf_le2)
  by (simp add: local.int_inf_greatest)

end

end