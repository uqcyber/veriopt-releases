section "Traversal"
text "Theory for traversals of the IR structure"

theory Traversal
  imports Semantics
begin

fun subnodes :: "ControlNode \<Rightarrow> ControlNode set" where
  "subnodes (EndNode) = {}" |
  "subnodes (IfNode _ x y) = (subnodes x) \<union> (subnodes y)" |
  "subnodes (WhileNode _ x y) = (subnodes x) \<union> (subnodes y)" |
  "subnodes (AssignNode _ _ x) = (subnodes x)" |
  "subnodes (WriteNode _ x) = (subnodes x)"

fun expression_nodes :: "ControlNode \<Rightarrow> Node set" where
  "expression_nodes (EndNode) = {}" |
  "expression_nodes (IfNode x _ _) = {x}" |
  "expression_nodes (WhileNode x _ _) = {x}" |
  "expression_nodes (AssignNode _ x _) = {x}" |
  "expression_nodes (WriteNode x _) = {x}"

fun expressions :: "ControlNode \<Rightarrow> Node list" where
  "expressions (EndNode) = []" |
  "expressions (IfNode x true false) = [x] @ (expressions true) @ (expressions false)" |
  "expressions (WhileNode x body next) = [x] @ (expressions body) @ (expressions next)" |
  "expressions (AssignNode _ expr next) = [expr] @ (expressions next)" |
  "expressions (WriteNode x next) = [x] @ (expressions next)"

fun usages :: "Node \<Rightarrow> ControlNode \<Rightarrow> Node list" where
  "usages node control = [expr . expr <- (expressions control), expr = node]"

fun usage :: "Node \<Rightarrow> ControlNode \<Rightarrow> nat" where
  "usage node control = size (usages node control)"

fun used :: "Node \<Rightarrow> ControlNode \<Rightarrow> bool" where
  "used node control = (size (usages node control) > 0)"

fun contains :: "ControlNode \<Rightarrow> ControlNode \<Rightarrow> bool" where
  "contains search program = (\<exists> node \<in> (subnodes program) . node = search)"

fun ids :: "ControlNode \<Rightarrow> String.string set" where
  "ids prog = {id :: String.string . (exec prog emptyState)(id) \<noteq> UndefinedValue}"

fun vals :: "ControlNode \<Rightarrow> Value set" where
  "vals prog = {val :: Value . (\<exists> id \<in> ids(prog) . (exec prog emptyState)(id) = val)}"

lemma "(ids (AssignNode ''r'' (ConstNode (IntegerValue 1)) EndNode)) = {''r'', ''stdout''}"
  by auto

lemma "(vals (AssignNode ''r'' (ConstNode (IntegerValue 1)) EndNode)) 
        = {(IntegerValue 1), (StringValue '''')}"
  by auto

value "(used
(ConstNode (IntegerValue 1))
(AssignNode ''r'' (ConstNode (IntegerValue 1)) EndNode)
)"

value "(used
(ConstNode (IntegerValue 1))
(AssignNode ''r'' (ConstNode (IntegerValue 2)) EndNode)
)"

value "(used
(ConstNode (IntegerValue 1))
(AssignNode ''r'' (ConstNode (IntegerValue 2))
  (WriteNode (ConstNode (IntegerValue 2))
  (WriteNode (ConstNode (IntegerValue 1))
  EndNode)))
)"

value "(usages
(ConstNode (IntegerValue 1))
(AssignNode ''r'' (ConstNode (IntegerValue 2))
  (WriteNode (ConstNode (IntegerValue 1))
  (WriteNode (ConstNode (IntegerValue 1))
  EndNode)))
)"

value "(usage
(ConstNode (IntegerValue 1))
(AssignNode ''r'' (ConstNode (IntegerValue 2))
  (WriteNode (ConstNode (IntegerValue 2))
  (WriteNode (ConstNode (IntegerValue 1))
  EndNode)))
)"
end