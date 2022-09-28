subsection \<open>LeftShiftNode Phase\<close>

theory LeftShiftPhase
  imports
    Common
begin

phase LeftShiftNode
  terminating size
begin

(*

fun shift_amount :: "iwidth \<Rightarrow> int64 \<Rightarrow> nat" where
  "shift_amount b val = unat (and val (if b = 64 then 0x3F else 0x1f))"

*)

(* Value level proofs *)

(* Need to transform to 32-bit only *)
lemma val_EliminateRHS:
  assumes "(val[y & (new_int 32 (31))] = new_int 32 0)"
  and     "val[x << y] \<noteq> UndefVal"
shows   "val[x << y] = x"
  using assms apply (cases x; cases y; auto)
  subgoal premises p for x22 x21a x22a
  proof -
      have "val_to_bool(val[(IntVal 32 31 < y)])"
       using assms  sorry
     then have "take_bit LENGTH(64) ((x22 << unat (and x22a (63))) :: 64 word) = x22"
       unfolding Word.take_bit_length_eq 
 (* Values.shift_amount.simps *) (*Values.shiftl_def*)
        sorry
    then show ?thesis
        by simp
    qed

  subgoal premises p for x21 x22 x21a x22a
    proof -
      have "take_bit x21 (x22 << unat (and x22a (31::64 word))) = x22"
        sorry
      then show ?thesis
        sorry
    qed
  done

(* Exp level proofs *)
lemma exp_EliminateRHS:
  assumes "val[y & (new_int 32 (31))] = new_int 32 0"
  shows   "exp[x << const(y)] \<ge> x"
  unfolding bin_eval.simps(8) apply auto
  subgoal premises p for m p xa
    proof -
      obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
        using p by blast
      then have 1: "wf_value y"
        using p(3) by auto
      then have 2: "val[xa << y] \<noteq> UndefVal"
        using evalDet p(1) p(2) xa by blast
      then have "val[xa << y] = xa" 
        using assms val_EliminateRHS by auto  
      then show ?thesis
        using evalDet p(1) xa by fastforce
    qed
  done

text \<open>Optimisations\<close>
(* Need to prove val_EliminateRHS*)
optimization EliminateRHS: "(x << const(y)) \<longmapsto> x when 
                            (val[y & (new_int 32 (31))] = new_int 32 0)"
  using exp_EliminateRHS  by auto

end (* End of ShiftNode *)

end (* End of file *)