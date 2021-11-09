theory TheoryTesting
  imports Main "HOL-Library.Word"
begin


(*datatype UnknownNumer =
  Unknown (down: "64 word") (up: "64 word")*)

value "NOT (0::64 word)"

typedef IntegerHole = "{(down::64 word, up::64 word) . ((NOT down) OR up = NOT 0)}"
proof -
  have "((NOT 0::64 word) OR 0 = NOT 0)"
    by simp
  then show ?thesis
    by blast
qed

fun valid_number :: "IntegerHole \<Rightarrow> 64 word \<Rightarrow> bool" where
  "valid_number hole num = (let (down, up) = Rep_IntegerHole hole in 
    down AND num = down \<and>
    (NOT up) AND num = 0
  )"

code_datatype Abs_IntegerHole


lemma only_set: "valid_number (Abs_IntegerHole (-1, -1)) x \<Longrightarrow> x = -1"
  unfolding valid_number.simps
  by (simp add: Abs_IntegerHole_inverse)

lemma none_set: "valid_number (Abs_IntegerHole (0, 0)) x \<Longrightarrow> x = 0"
  unfolding valid_number.simps
  by (simp add: Abs_IntegerHole_inverse)


lemma
  assumes "Rep_IntegerHole xhole = (xdown, xup)"
  assumes "Rep_IntegerHole yhole = (ydown, yup)"
  assumes "valid_number xhole x"
  assumes "valid_number yhole y"
  assumes "(NOT xdown) AND yup = 0"
  shows "x AND y = y"
  using assms unfolding valid_number.simps
  apply (simp add: Abs_IntegerHole_inverse)
  by (metis (no_types, hide_lams) bit.conj_disj_distrib2 bit.disj_cancel_left or.left_neutral word_ao_absorbs(2) word_oa_dist)
  

end