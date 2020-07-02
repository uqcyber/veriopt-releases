theory ExpandLogicPhase
imports AbsGraph
begin

(* One transformation from the ExpandLogicPhase optimisation. *)

fun opt_expand_logic :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "opt_expand_logic gin gout =
    (\<exists> shortCircuitOr \<in> g_ids gin. is_ShortCircuitOrNode(g_nodes gin shortCircuitOr) \<and>
    (\<exists> x \<in> g_ids gin.
    (\<exists> y \<in> g_ids gin. g_inputs gin shortCircuitOr = [x, y] \<and>
    (\<exists> ifNode \<in> g_ids gin. g_nodes gin ifNode = IfNode \<and>
       g_inputs gin ifNode = [shortCircuitOr] \<and>
    (\<exists> trueTarget \<in> g_ids gin.
    (\<exists> falseTarget \<in> g_ids gin. g_successors gin ifNode = [trueTarget, falseTarget] \<and>

    (\<exists> firstIf firstTrueTarget firstTrueEnd secondIfBegin
       secondIf secondTrueTarget secondTrueEnd trueTargetMerge . 
      [firstIf, firstTrueTarget, firstTrueEnd, secondIfBegin,
       secondIf, secondTrueTarget, secondTrueEnd, trueTargetMerge] = next_ids gin 8 \<and>
    gout =
      (add_node firstIf          IfNode    [x]  [secondIfBegin]
      (add_node firstTrueTarget  BeginNode []   [firstTrueEnd]
      (add_node firstTrueEnd     EndNode   []   []
      (add_node secondIfBegin    BeginNode []   [secondIf]
      (add_node secondIf         IfNode    [y]  [secondTrueTarget]
      (add_node secondTrueTarget BeginNode []   [secondTrueEnd]
      (add_node secondTrueEnd    EndNode   []   []
      (add_node trueTargetMerge  MergeNode [firstTrueEnd,secondTrueEnd] [trueTarget]
      (del_node ifNode
      (del_node shortCircuitOr
       gin)))
    ))))))))))))))"


(* ShortCutOr Example 1: (based on Figure 2 from Graal_IR_2013_10)
  ================================================================
  f(bool x, bool y) { if (x || y) result=42 else result=0; return result; }

          [1 Param(0)]   [2 Param(1)]
                     \  /
  [0 Start]  [3 ShortCutOr xNeg=False yNeg=False]
     |      /
     V     /
  [5 IfNode]
      /    \
     V      V
  [6 Begin] [8 Begin]
     |      |
     V      V
  [7 End]   [9 End]
     |     / 
  [10 Merge]  [11 Constant 42] [12 Constant 0]
     |    \  |              /
     |    [13 Phi           ]
     V    /
  [14 Return]
*)
definition eg_short_cut_or1 :: IRGraph where
  "eg_short_cut_or1 =
    (add_node 14 ReturnNode [13] []
    (add_node 13 PhiNode [10, 11, 12] []
    (add_node 12 (ConstantNode 0) [] []
    (add_node 11 (ConstantNode 42) [] []
    (add_node 10 MergeNode [7, 9] [14]
    (add_node 9 EndNode [] []
    (add_node 8 BeginNode [] [9]
    (add_node 7 EndNode [] []
    (add_node 6 BeginNode [] [7]
    (add_node 5 IfNode [3] [6, 8]
    (add_node 3 (ShortCircuitOrNode False False) [1, 2] []
    (add_node 2 (ParameterNode 1) [] []
    (add_node 1 (ParameterNode 0) [] []
    (add_node 0 StartNode [] [5]
    empty_graph))))))))))))))"

lemma "\<forall> n \<in> g_ids eg_short_cut_or1.
        wff_node 
          (g_nodes eg_short_cut_or1 n)
          (g_inputs eg_short_cut_or1 n)
          (g_successors eg_short_cut_or1 n)"
  unfolding eg_short_cut_or1_def by simp

lemma "wff_graph eg_short_cut_or1"
  unfolding eg_short_cut_or1_def empty_graph_def
  (* nitpick [verbose, card=1-20] *)
  by auto

(*
schematic_goal opt1: "opt_expand_logic eg_short_cut_or1 ?OUT"
  unfolding eg_short_cut_or1_def
  apply (simp add: insert_Diff_if)   (* takes about 15 minutes! *)
  done

thm opt1
*)

(* This calculated ?OUT as follows: *)
definition out1 :: IRGraph where
  "out1 =  (Graph {15, 16, 17, 18, 19, 20, 21, 22, 0, 14, 13, 12, 11, 10, 9, 8, 7, 6, 2, Suc 0, 0}
   ((\<lambda>i. StartNode)
    (0 := StartNode, Suc 0 := ParameterNode 0, 2 := ParameterNode 1, 6 := BeginNode, 7 := EndNode,
     8 := BeginNode, 9 := EndNode, 10 := MergeNode, 11 := ConstantNode 42, 12 := ConstantNode 0,
     13 := PhiNode, 14 := ReturnNode, 3 := StartNode, 5 := StartNode, 22 := MergeNode,
     21 := EndNode, 20 := BeginNode, 19 := IfNode, 18 := BeginNode, 17 := EndNode, 16 := BeginNode,
     15 := IfNode))
   ((\<lambda>i. [])
    (0 := [], Suc 0 := [], 2 := [], 6 := [], 7 := [], 8 := [], 9 := [], 10 := [7, 9], 11 := [],
     12 := [], 13 := [10, 11, 12], 14 := [13], 3 := [], 5 := [], 22 := [17, 21], 21 := [],
     20 := [], 19 := [2], 18 := [], 17 := [], 16 := [], 15 := [Suc 0]))
   ((\<lambda>i. [])
    (0 := [5], Suc 0 := [], 2 := [], 6 := [7], 7 := [], 8 := [9], 9 := [], 10 := [14], 11 := [],
     12 := [], 13 := [], 14 := [], 3 := [], 5 := [], 22 := [6], 21 := [], 20 := [21], 19 := [20],
     18 := [19], 17 := [], 16 := [17], 15 := [18])))"

lemma check1: "opt_expand_logic eg_short_cut_or1 out1"
  unfolding eg_short_cut_or1_def out1_def
  (* apply code_simp --- gives wellsortedness error *)
  apply (simp add: Let_def)   
  
  (* takes about 4:30 mins *)

  apply (simp add: insert_Diff_if)
  done

end
