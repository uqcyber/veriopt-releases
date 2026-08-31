subsection \<open>BinaryNode Phase\<close>

theory BinaryNode
  imports
    Common
begin

phase BinaryNode
  terminating size
begin

optimization BinaryFoldConstant: "BinaryExpr op (const v1) (const v2) \<longmapsto> const (bin_eval op v1 v2)"
  unfolding le_expr_def apply (rule allI impI)+
  subgoal premises bin for m p v
    apply (rule BinaryExprE[OF bin])
    subgoal premises p for x y
    proof -
      have x: "x = v1"
        using p by auto
      have y: "y = v2"
        using p by auto
      have "\<exists> b vv . v = new_int b vv"
        using bin_eval_new_int p by fast
      then show ?thesis
        by (metis ConstantExpr bin eval_bits_1_64 new_int.elims p(1) validIntConst wf_value_def x y)
      qed
    done
  done

end

end