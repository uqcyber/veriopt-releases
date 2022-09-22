subsection \<open>BinaryNode Phase\<close>

theory BinaryNode
  imports
    Common
begin

phase BinaryNode 
  terminating size
begin

optimization BinaryFoldConstant: "BinaryExpr op (const v1) (const v2) \<longmapsto> ConstantExpr (bin_eval op v1 v2)"
  unfolding le_expr_def
  apply (rule allI impI)+
  subgoal premises bin for m p v
    print_facts
    apply (rule BinaryExprE[OF bin])
    subgoal premises prems for x y
      print_facts
(* backward refinement:
      apply (subgoal_tac "x = v1 \<and> y = v2")
        using prems apply auto
      apply (rule ConstantExpr)
      apply (rule validIntConst)
      using bin_eval_int int_stamp_both by auto
*)
(* or forward proof: *)
    proof -
      have x: "x = v1" using prems by auto
      have y: "y = v2" using prems by auto
      have xy: "v = bin_eval op x y" using prems x y by simp
      have int: "\<exists> b vv . v = new_int b vv" using bin_eval_new_int prems by fast
      show ?thesis
        unfolding prems x y xy (* get it in form: ConstantExpr c \<longmapsto> c *)
        apply (rule ConstantExpr)
        using prems x y xy int sorry
      qed
    done
  done

print_facts

end

end