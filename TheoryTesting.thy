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


definition shiftl (infix "<<" 75) where 
  "shiftl w n = (shiftl1 ^^ n) w"

lemma shiftl_power[simp]: "(x::('a::len) word) * (2 ^ j) = x << j"
  unfolding shiftl_def apply (induction j)
  apply simp unfolding funpow_Suc_right
  by (metis (no_types, lifting) comp_def funpow_swap1 mult.left_commute power_Suc shiftl1_eq_mult_2)

lemma "(x::('a::len) word) * ((2 ^ j) + 1) = x << j + x"
  by (simp add: distrib_left)

lemma "(x::('a::len) word) * ((2 ^ j) - 1) = x << j - x"
  by (simp add: right_diff_distrib)

lemma "(x::('a::len) word) * ((2^j) + (2^k)) = x << j + x << k"
  by (simp add: distrib_left)

lemma "(x::('a::len) word) * ((2^j) - (2^k)) = x << j - x << k"
  by (simp add: right_diff_distrib)


definition signed_shiftr (infix ">>" 75) where 
  "signed_shiftr w n = (sshiftr1 ^^ n) w"

definition shiftr (infix ">>>" 75) where 
  "shiftr w n = (shiftr1 ^^ n) w"

lemma shiftr_power[simp]: "(x::('a::len) word) div (2 ^ j) = x >>> j"
  unfolding shiftr_def apply (induction j)
  apply simp unfolding funpow_Suc_right
  by (metis (no_types, lifting) comp_apply div_exp_eq funpow_swap1 power_Suc2 power_add power_one_right shiftr1_eq_div_2)



end