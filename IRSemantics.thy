theory IRSemantics 
  imports
    AbsGraph
    "HOL-Word.More_Word"
begin

(*
datatype IRGraph =
  Graph
    (g_ids: "ID set")
    (g_nodes: "ID \<Rightarrow> IRNode")
    (g_inputs: "InputEdges")
    (g_successors: "SuccessorEdges")
*)

datatype Value =
  UndefinedValue |
  IntegerValue int | 
  StringValue string |
  ExceptionValue string

fun bool :: "Value \<Rightarrow> bool" where
  "bool (IntegerValue a) = (a \<noteq> 0)" |
  "bool a = False"

fun get_successor :: "ID \<Rightarrow> IRGraph \<Rightarrow> ID" where
"get_successor n g = 
  (if (size (g_successors g n) > 0) then
    (hd (g_successors g n))
  else
    (the_elem (g_usages g n)))"

fun get_nth_successor :: "ID \<Rightarrow> nat \<Rightarrow> IRGraph \<Rightarrow> ID" where
"get_nth_successor n which g = (nth (g_successors g n) which)"

fun get_input1 :: "ID \<Rightarrow> IRGraph \<Rightarrow> ID" where 
"get_input1 n g = (nth (g_inputs g n) 0)"

fun get_input2 :: "ID \<Rightarrow> IRGraph \<Rightarrow> ID" where 
"get_input2 n g = (nth (g_inputs g n) 1)"

fun get_input3 :: "ID \<Rightarrow> IRGraph \<Rightarrow> ID" where 
"get_input3 n g = (nth (g_inputs g n) 3)"

fun nth_input :: "ID \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> ID" where 
"nth_input n node graph = (nth (g_inputs graph node) n)"

fun get_dependent_phi :: "ID set \<Rightarrow> IRGraph \<Rightarrow> ID option" where
"get_dependent_phi s g = 
  (let res = {n. n \<in> s \<and> (case ((g_nodes g) n) of PhiNode \<Rightarrow> True | _ \<Rightarrow> False)} in
  (if card(res) = 1 then Some (the_elem (res)) else None))"


definition some_elem :: "'a set \<Rightarrow> 'a" where [code del]:
  "some_elem = (\<lambda>S. SOME x. x \<in> S)"
code_printing
  constant some_elem \<rightharpoonup> (SML) "(case/ _ of/ Set/ xs/ =>/ hd/ xs)"

fun get_next_phi :: "ID set \<Rightarrow> IRGraph \<Rightarrow> (ID \<Rightarrow> Value option) \<Rightarrow> ID option" where
"get_next_phi s g cur = 
  (let the_phis = {n. 
   n \<in> s \<and> 
   (case ((g_nodes g) n) of PhiNode \<Rightarrow> True | _ \<Rightarrow> False) \<and>
   (case (cur n) of None \<Rightarrow> True | _ \<Rightarrow> False)} in
   (if (card the_phis) > 0 then Some (some_elem the_phis) else None))"

primrec first_pos :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
"first_pos a [] = None" |
"first_pos a (x # xs) = 
  (if a = x then 
    Some 0
  else
    (let n = first_pos a xs in 
      (case n of
        Some nn \<Rightarrow> Some (nn + 1) |
        None \<Rightarrow> None)))"


type_synonym State = "string \<Rightarrow> Value"
type_synonym Parameters = "int \<Rightarrow> Value"

datatype EvalState = 
  EvalState 
    (s_graph: "IRGraph")
    (s_phi: "ID \<Rightarrow> Value" )
    (s_params: "Value list")
   
fun applyUnaryOp :: "IRNode \<Rightarrow> Value \<Rightarrow> Value" where
"applyUnaryOp NegateNode (IntegerValue a) = (IntegerValue (-a))" |
"applyUnaryOp AbsNode (IntegerValue a) = IntegerValue (if a < 0 then -a else a)" |
"applyUnaryOp LogicNegationNode (IntegerValue a) = IntegerValue (if a = 0 then 1 else 0)" |
"applyUnaryOp _ _ = UndefinedValue"

fun applyBinop :: "IRNode \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
"applyBinop AddNode (IntegerValue a) (IntegerValue b) = IntegerValue (a + b)" |
"applyBinop MulNode (IntegerValue a) (IntegerValue b) = IntegerValue (a * b)" |
"applyBinop SubNode (IntegerValue a) (IntegerValue b) = IntegerValue (a - b)" |
"applyBinop IntegerEqualsNode (IntegerValue a) (IntegerValue b) = IntegerValue (if a = b then 1 else 0)" |
"applyBinop IntegerLessThanNode (IntegerValue a) (IntegerValue b) = IntegerValue (if a < b then 1 else 0)" |
"applyBinop XorNode (IntegerValue a) (IntegerValue b) = IntegerValue (if (a \<noteq> 0 \<and> b = 0) \<or> (a = 0 \<and> b \<noteq> 0) then 1 else 0)" | 
"applyBinop _ _ _ = UndefinedValue"
(* TODO: short circuit or *)

function
  eval :: "ID \<Rightarrow> EvalState \<Rightarrow> Value" and
  evalNode :: "ID \<Rightarrow> IRNode \<Rightarrow> EvalState \<Rightarrow> Value" and
  evalSuccessor :: "ID \<Rightarrow> EvalState \<Rightarrow> Value" and
  evalBinop :: "ID \<Rightarrow> EvalState \<Rightarrow> Value" and
  evalUnaryOp :: "ID \<Rightarrow> EvalState \<Rightarrow> Value" and
  evalMergeNode :: "ID \<Rightarrow> ID \<Rightarrow> EvalState \<Rightarrow> Value" and
  evalLoopBeginNode :: "ID \<Rightarrow> ID \<Rightarrow> EvalState \<Rightarrow> Value" and
  evalPhiNode :: "ID \<Rightarrow> nat \<Rightarrow> EvalState \<Rightarrow> Value" and
  evalLoopBeginNodeHelp :: "ID \<Rightarrow> nat \<Rightarrow> EvalState \<Rightarrow> (ID \<Rightarrow> Value option) \<Rightarrow> Value" and
  evalMergeNodeHelp :: "ID \<Rightarrow> nat \<Rightarrow> EvalState \<Rightarrow> (ID \<Rightarrow> Value option) \<Rightarrow> Value"
where
"eval n state = evalNode n ((g_nodes (s_graph state)) n) state" |

"evalSuccessor n state = 
  (case (g_nodes (s_graph state) (get_successor n (s_graph state))) of
      MergeNode \<Rightarrow> evalMergeNode (get_successor n (s_graph state)) n state |
      LoopBeginNode \<Rightarrow> evalLoopBeginNode (get_successor n (s_graph state)) n state |
      _ \<Rightarrow> eval (get_successor n (s_graph state)) state)" |

"evalMergeNode n pred state =
  (case (first_pos pred (g_inputs (s_graph state) n)) of
  Some branch \<Rightarrow> evalMergeNodeHelp n (branch + 1) state (\<lambda>id. None) |
  None \<Rightarrow> UndefinedValue)" |

"evalMergeNodeHelp n branch state cur =
  (let next_phi = get_next_phi (g_usages (s_graph state) n) (s_graph state) cur in
  (case (next_phi) of
    None \<Rightarrow> (evalSuccessor 
            n 
            (EvalState
              (s_graph state)
              (\<lambda> id. case (cur id) of 
                None \<Rightarrow> (s_phi state) id
                | Some v \<Rightarrow> v)
              (s_params state))) |
    Some phi_id \<Rightarrow> 
      (let res = evalPhiNode phi_id branch state in
      evalMergeNodeHelp n branch state (\<lambda>id. if id = phi_id then Some res else cur id))))" |

"evalLoopBeginNode n pred state =
  (let branch = (case (g_nodes (s_graph state) pred) of
     LoopEndNode \<Rightarrow> 2 |
     _ \<Rightarrow> 1) in
  evalLoopBeginNodeHelp n branch state (\<lambda>id. None))" | 

"evalLoopBeginNodeHelp n branch state cur =
  (let next_phi = get_next_phi (g_usages (s_graph state) n) (s_graph state) cur in
  (case (next_phi) of
    None \<Rightarrow> (evalSuccessor 
            n 
            (EvalState
              (s_graph state)
              (\<lambda> id. case (cur id) of 
                None \<Rightarrow> (s_phi state) id
                | Some v \<Rightarrow> v)
              (s_params state))) |
    Some phi_id \<Rightarrow> 
      (let res = evalPhiNode phi_id branch state in
      evalLoopBeginNodeHelp n branch state (\<lambda>id. if id = phi_id then Some res else cur id))))"  |

"evalPhiNode n branch state = eval (nth_input branch n (s_graph state)) state" |

"evalNode n PhiNode state = (s_phi state) n" |
"evalNode n LoopEndNode state = evalLoopBeginNode (get_input1 n (s_graph state)) n state" |

(* TODO: do constants need to be ints? *)
"evalNode n (ConstantNode v) state = IntegerValue v" |
"evalNode n (ParameterNode k) state = nth (s_params state) (nat k) " |
"evalBinop n state = applyBinop (g_nodes (s_graph state) n) (eval (get_input1 n (s_graph state)) state) (eval (get_input2 n (s_graph state)) state)" |
"evalUnaryOp n state = applyUnaryOp (g_nodes (s_graph state) n) (eval (get_input1 n (s_graph state)) state)" |

"evalNode n IfNode (EvalState graph phis params) = 
  evalSuccessor 
    (get_nth_successor n (if (bool (eval (get_input1 n graph) (EvalState graph phis params))) then 0 else 1) graph)
    (EvalState graph phis params)" |
"evalNode n BeginNode state = evalSuccessor n state" |
"evalNode n EndNode state = evalSuccessor n state" |
"evalNode n StartNode state = evalSuccessor n state" |
"evalNode n ReturnNode state = eval (get_input1 n (s_graph state)) state" |

"evalNode n ConditionalNode state =
  (if (bool (eval (get_input1 n (s_graph state)) state)) then
    (eval (get_input2 n (s_graph state)) state)
  else 
    (eval (get_input3  n (s_graph state)) state))" |

"evalNode n AddNode state = evalBinop n state" |
"evalNode n MulNode state = evalBinop n state" |
"evalNode n SubNode state = evalBinop n state" |
"evalNode n XorNode state = evalBinop n state" |
"evalNode n IntegerEqualsNode state = evalBinop n state" |
"evalNode n IntegerLessThanNode state = evalBinop n state" |

"evalNode n NegateNode state = evalUnaryOp n state" |
"evalNode n AbsNode state = evalUnaryOp n state" |
"evalNode n LogicNegationNode state = evalUnaryOp n state"
sorry
termination by auto

fun evalGraph :: "IRGraph \<Rightarrow> Value list \<Rightarrow>  Value" where
"evalGraph g params = eval 0 (EvalState g (\<lambda>x. UndefinedValue) params)"

definition eg3 :: IRGraph where
  "eg3 =
    (add_node 12 ReturnNode [11] []
    (add_node 11 PhiNode [10,9,7] []
    (add_node 10 MergeNode [5,6] [12]
    (add_node 9 AddNode [7,8] []
    (add_node 8 (ParameterNode 2) [] []
    (add_node 7 (ParameterNode 1) [] []
    (add_node 6 EndNode [] []
    (add_node 5 EndNode [] []
    (add_node 4 BeginNode [] [6]
    (add_node 3 BeginNode [] [5]
    (add_node 2 IfNode [1] [3,4] 
    (add_node 1 (ParameterNode 0) [] []
    (add_node 0 StartNode [] [2]
    empty_graph)))))))))))))"

value "evalGraph eg3 [IntegerValue 1, IntegerValue 66, IntegerValue 5]"

definition eg4 :: IRGraph where
  "eg4 =
    (add_node 14 (ParameterNode 0) [] []
    (add_node 13 ReturnNode [2] []
    (add_node 12 EndNode [] [13]
    (add_node 11 BeginNode [] [12]
    (add_node 10 LoopEndNode [7] []
    (add_node 9 BeginNode [] [10]
    (add_node 8 IfNode [3] [9,11]
    (add_node 7 LoopBeginNode [1] [8]
    (add_node 6 (ConstantNode 4) [] []
    (add_node 5 (ConstantNode 0) [] []
    (add_node 4 AddNode [2,6] []
    (add_node 3 IntegerLessThanNode [2,14] []
    (add_node 2 PhiNode [7,5,4] [] 
    (add_node 1 EndNode [] []
    (add_node 0 StartNode [] [1]
    empty_graph)))))))))))))))"

value "eval 0 (EvalState eg4 (\<lambda>x. UndefinedValue) [IntegerValue 117])"

end