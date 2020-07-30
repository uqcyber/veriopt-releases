theory inductive_snip 
  imports
    "AbsGraph"
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

fun get_input_node :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> IRNode" where
  "get_input_node nid state i = (get_node (get_input nid state i) state)"

fun get_input_pair :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID \<times> IRNode" where
  "get_input_pair nid state i = 
    (let next_id = (get_input nid state i) in
    (next_id, (get_node next_id state)))"

fun get_input_eval :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID \<times> IRNode \<times> EvalState" where
  "get_input_eval nid state i = 
    (let next_id = (get_input nid state i) in
    (next_id, (get_node next_id state), state))"

fun get_successor :: "ID \<Rightarrow> EvalState \<Rightarrow> ID" where
"get_successor n state = 
  (let g = s_graph state in
  (if (size (g_successors g n) > 0) then
    (hd (g_successors g n))
  else
    (the_elem (g_usages g n))))"

fun get_successor_node :: "ID \<Rightarrow> EvalState \<Rightarrow> IRNode" where
  "get_successor_node nid state = (get_node (get_successor nid state) state)"

fun get_successor_pair :: "ID \<Rightarrow> EvalState \<Rightarrow> ID \<times> IRNode" where
  "get_successor_pair nid state =
    (let next_id = (get_successor nid state) in
    (next_id, (get_node next_id state)))"

fun get_successor_eval :: "ID \<Rightarrow> EvalState \<Rightarrow> ID \<times> IRNode \<times> EvalState" where
  "get_successor_eval nid state =
    (let next_id = (get_successor nid state) in
    (next_id, (get_node next_id state), state))"

fun binary_expr :: "IRNode \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" ("_[_._]" 89)
  where
  "binary_expr AddNode (IntVal x) (IntVal y) = (IntVal (x + y))" |
  "binary_expr _ _ _ = UndefVal"

fun update_state :: "(string \<Rightarrow> Value) \<Rightarrow> string \<Rightarrow> Value \<Rightarrow> (string \<Rightarrow> Value)" where
  "update_state scope ident val = (\<lambda> x. (if x = ident then val else (scope x)))"
fun add_value :: "EvalState \<Rightarrow> string \<Rightarrow> Value \<Rightarrow> EvalState" 
  ("_[_\<rightarrow>_]" 55)
  where
  "add_value (EvalState graph phi params scope) ident val = 
      (EvalState graph phi params (update_state scope ident val))"

fun unwrap :: "('a \<times> 'b) \<times> 'c \<Rightarrow> ('a \<times> 'b \<times> 'c)" where
  "unwrap ((a, b), c) = (a, b, c)"

inductive
  eval :: "ID \<times> IRNode \<times> EvalState \<Rightarrow> EvalState \<times> Value \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
  StartNode: "\<lbrakk>(get_successor_eval n s) \<Rightarrow> succ\<rbrakk> \<Longrightarrow> (n, StartNode, s) \<Rightarrow> succ" |

  ParameterNode: "(n, (ParameterNode i), s) \<Rightarrow> (s, (IntVal i))" |

  AddNode: "\<lbrakk>(get_input_eval n s 0) \<Rightarrow> (s1, v1);
             (get_input_eval n s 1) \<Rightarrow> (s2, v2)\<rbrakk>
            \<Longrightarrow> (n, AddNode, s) \<Rightarrow> (s, (binary_expr AddNode v1 v2))" |

  ReturnNode: "\<lbrakk>(get_input_eval n s 0) \<Rightarrow> (s1, v1)\<rbrakk> 
            \<Longrightarrow> (n, ReturnNode, s) \<Rightarrow> (s[''RETURN''\<rightarrow>v1], v1)" |

  IfNode: "\<lbrakk>(n, AddNode, s) \<Rightarrow> s'\<rbrakk> \<Longrightarrow> (n, IfNode, s) \<Rightarrow> s'"

definition ex_graph :: IRGraph where
  "ex_graph =
    (add_node 3 ReturnNode [2] []
    (add_node 2 AddNode [1, 1] []
    (add_node 1 (ParameterNode 2) [] []
    (add_node 0 StartNode [] [2]
    empty_graph))))"
definition ex_state :: EvalState where
  "ex_state = (EvalState ex_graph (\<lambda> x. UndefVal) [] (\<lambda> x. UndefVal))"

fun lookup :: "EvalState \<Rightarrow> string \<Rightarrow> Value" (infix "::" 56) where
  "lookup (EvalState _ _ _ scope) ident = (scope ident)"

value "(ex_state[''hi'' \<rightarrow> (IntVal 3)]) :: ''hi''"

code_pred eval .
values "{(s, v). (0, StartNode, ex_state) \<Rightarrow> (s, v)}"

end