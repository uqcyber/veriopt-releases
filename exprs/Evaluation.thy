theory Evaluation
  imports Semantics
begin

interpretation evaluation: Eval
  done

interpretation semantics: Semantic
  done

value "''hello''"
value "Eval.int_to_str 573 ''''"
value "Eval.int_to_str 342542523 ''''"
value "Eval.int_to_str 5342373 ''''"
value "Eval.int_to_str 3 ''''"

value "(exec (WriteNode (ConstNode (IntegerValue 5)) EndNode) emptyState) x"

value "(exec
  (WriteNode (ConstNode (StringValue ''The magic number is ''))
    (WriteNode (ConstNode (IntegerValue 56)) EndNode))
  emptyState) ''stdout''"

value "(exec
(AssignNode ''i'' (ConstNode (IntegerValue 0))
  (WhileNode (BinaryNode LessOp (LookupNode ''i'') (ConstNode (IntegerValue 4)))
    (AssignNode ''i'' (BinaryNode AddOp (LookupNode ''i'') (ConstNode (IntegerValue 1)))
    (WriteNode (LookupNode ''i'')
    (WriteNode (ConstNode (StringValue '' Fight me Emily ''))
  EndNode)))
 EndNode)) emptyState) ''stdout''"

end