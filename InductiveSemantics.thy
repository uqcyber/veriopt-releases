theory InductiveSemantics 
  imports
    "AbsGraph"
    "HOL-Library.LaTeXsugar"
    "HOL-Library.OptionalSugar"
begin

datatype Value =
  UndefVal |
  IntVal int

datatype EvalState = 
  EvalState 
    (s_graph: "IRGraph")
    (s_phi: "ID \<Rightarrow> Value")
    (s_params: "Value list")
    (s_scope: "string \<Rightarrow> Value")

fun get_node :: "ID \<Rightarrow> EvalState \<Rightarrow> IRNode" where
  "get_node n state = ((g_nodes (s_graph state)) n)"

fun get_input :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID" where 
  "get_input nid state i = (nth (g_inputs (s_graph state) nid) i)"

fun input :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID \<times> IRNode \<times> EvalState" where
  "input nid state i = 
    (let next_id = (get_input nid state i) in
    (next_id, (get_node next_id state), state))"

fun get_successor :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID" where
"get_successor n state i = 
  (let g = s_graph state in
  (if (size (g_successors g n) > 0) then
    (nth (g_successors g n) i)
  else
    (the_elem (g_usages g n))))"

fun 
  successor :: "ID \<Rightarrow> EvalState \<Rightarrow> ID \<times> IRNode \<times> EvalState" and
  successori :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID \<times> IRNode \<times> EvalState"
  where
  "successor nid state =
    (let next_id = (get_successor nid state 0) in
    (next_id, (get_node next_id state), state))" |
  "successori nid state i = 
    (let next_id = (get_successor nid state i) in
    (next_id, (get_node next_id state), state))"

fun binary_expr :: "IRNode \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" ("_[[_ _]]" 89) where
  "binary_expr AddNode (IntVal x) (IntVal y) = (IntVal (x + y))" |
  "binary_expr SubNode (IntVal x) (IntVal y) = (IntVal (x - y))" |
  "binary_expr _ _ _ = UndefVal"

fun bool_expr :: "Value \<Rightarrow> bool" where
  "bool_expr (IntVal x) = (if x = 0 then False else True)" |
  "bool_expr (UndefVal) = False"

fun is_binary_node :: "IRNode \<Rightarrow> bool" where
  "is_binary_node AddNode = True" |
  "is_binary_node SubNode = True" |
  "is_binary_node x = False"

fun update_state :: "(string \<Rightarrow> Value) \<Rightarrow> string \<Rightarrow> Value \<Rightarrow> (string \<Rightarrow> Value)" where
  "update_state scope ident val = (\<lambda> x. (if x = ident then val else (scope x)))"
fun add_value :: "EvalState \<Rightarrow> string \<Rightarrow> Value \<Rightarrow> EvalState" 
  ("_[_\<rightarrow>_]" 55)
  where
  "add_value (EvalState graph phi params scope) ident val = 
      (EvalState graph phi params (update_state scope ident val))"

inductive
  eval :: "ID \<times> IRNode \<times> EvalState \<Rightarrow> EvalState \<times> Value \<Rightarrow> bool" ("_\<mapsto>_" 55)
  where

  StartNode: "\<lbrakk>(successori num s 0) \<mapsto> succ\<rbrakk> \<Longrightarrow> (num, StartNode, s) \<mapsto> succ" |

  ParameterNode: "(num, (ParameterNode i), s) \<mapsto> (s, (IntVal i))" |

  ConstantNode: "(num, (ConstantNode c), s) \<mapsto> (s, (IntVal c))" |

  BinaryNode: "\<lbrakk>is_binary_node node;
                (input num s 0) \<mapsto> (s1, v1);
                (input num s1 1) \<mapsto> (s2, v2)\<rbrakk> 
                \<Longrightarrow> (num, node, s) \<mapsto> (s2, node[[v1 v2]])" |

  IfNodeTrue: "\<lbrakk>(input num s 0) \<mapsto> (s1, v1);
                (bool_expr v1);
                (successori num s1 0) \<mapsto> s2\<rbrakk> 
                \<Longrightarrow> (num, IfNode, s) \<mapsto> s2" |

  IfNodeFalse: "\<lbrakk>(input num s 0) \<mapsto> (s1, v1);
                 (\<not>(bool_expr v1));
                 (successori num s1 1) \<mapsto> s2\<rbrakk> 
                 \<Longrightarrow> (num, IfNode, s) \<mapsto> s2" |

  ReturnNode: "\<lbrakk>(input n s 0) \<mapsto> (s1, v1)\<rbrakk> 
                \<Longrightarrow> (n, ReturnNode, s) \<mapsto> (s1[''RETURN''\<rightarrow>v1], v1)"

(* Format as inference rules *)
text \<open>@{thm[mode=Rule] (sub, prem 2) eval.induct} {\sc StartNode}\<close>

text \<open>@{thm[mode=Axiom] (sub, prem 3) eval.induct} {\sc ParameterNode}\<close>
text \<open>@{thm[mode=Axiom] (sub, prem 4) eval.induct} {\sc ConstantNode}\<close>

text \<open>@{thm[mode=Rule] (sub, prem 5) eval.induct} {\sc AddNode}\<close>
text \<open>@{thm[mode=Rule] (sub, prem 6) eval.induct} {\sc SubNode}\<close>

text \<open>@{thm[mode=Rule] (sub, prem 7) eval.induct} {\sc IfNodeTrue}\<close>
text \<open>@{thm[mode=Rule] (sub, prem 8) eval.induct} {\sc IfNodeFalse}\<close>

text \<open>@{thm[mode=Rule] (sub, prem 9) eval.induct} {\sc ReturnNode}\<close>

(* Example graph evaluation *)
fun new_state :: "IRGraph \<Rightarrow> EvalState" where
  "new_state graph = (EvalState graph (\<lambda> x. UndefVal) [] (\<lambda> x. UndefVal))"

definition ex_graph :: IRGraph where
  "ex_graph =
    (add_node 3 ReturnNode [2] []
    (add_node 2 AddNode [1, 1] []
    (add_node 1 (ParameterNode 5) [] []
    (add_node 0 StartNode [] [2]
    empty_graph))))"
lemma "wff_graph ex_graph"
  unfolding ex_graph_def by simp

definition ex_graph2 :: IRGraph where
  "ex_graph2 =
    (add_node 5 ReturnNode [1] []
    (add_node 4 ReturnNode [2] []
    (add_node 3 IfNode [1] [4, 5]
    (add_node 2 (ConstantNode 30) [] []
    (add_node 1 (ConstantNode 1) [] []
    (add_node 0 StartNode [] [3]
    empty_graph))))))"
lemma "wff_graph ex_graph2"
  unfolding ex_graph2_def by simp

code_pred eval .
values "{(s, v). (0, StartNode, (new_state ex_graph)) \<mapsto> (s, v)}"

values "{(s, v). (0, StartNode, (new_state ex_graph2)) \<mapsto> (s, v)}"

end