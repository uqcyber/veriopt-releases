section "Semantics"
text \<open>Encoding of the semantics for each of the expression and statements nodes.

For expression nodes their semantics are defined by the definition of their associated
evaluation in the eval function.

For statement nodes their semantics are defined by the definition of their associated
evaluation in the exec function.
\<close>

theory Semantics
  imports
    Base
    "HOL-Word.Word_Bitwise"
begin 

text \<open>
Locale collection of functions which represent the semantics of specific expressions.
\<close>
locale Semantic
begin
fun add :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "add (IntegerValue a) (IntegerValue b) = (IntegerValue (a + b))" |
  "add a b = (UndefinedValue)"

fun divide :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "divide (IntegerValue a) (IntegerValue b) = (IntegerValue (a div b))" |
  "divide a b = (UndefinedValue)"

fun mul :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "mul (IntegerValue a) (IntegerValue b) = (IntegerValue (a * b))" |
  "mul a b = (UndefinedValue)"

fun sub :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "sub (IntegerValue a) (IntegerValue b) = (IntegerValue (a - b))" |
  "sub a b = (UndefinedValue)"

fun equal :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "equal (IntegerValue a) (IntegerValue b) = (BooleanValue (a = b))" |
  "equal (BooleanValue a) (BooleanValue b) = (BooleanValue (a = b))" |
  "equal a b = UndefinedValue"

fun less :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "less (IntegerValue a) (IntegerValue b) = (BooleanValue (sint a < sint b))" |
  "less a b = (UndefinedValue)"

fun logicAnd :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "logicAnd (BooleanValue a) (BooleanValue b) = (BooleanValue (a \<and> b))" |
  "logicAnd a b = (UndefinedValue)"

fun logicOr :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "logicOr (BooleanValue a) (BooleanValue b) = (BooleanValue (a \<or> b))" |
  "logicOr a b = (UndefinedValue)"

fun logicXor :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "logicXor (BooleanValue a) (BooleanValue b) 
      = (BooleanValue ((a \<and> b) \<or> ((\<not>a) \<and> (\<not>b))))" |
  "logicXor a b = (UndefinedValue)"



fun uminus :: "Value \<Rightarrow> Value" where
  "uminus (IntegerValue a) = (IntegerValue (-a))" |
  "uminus a = (UndefinedValue)"

fun logicNot :: "Value \<Rightarrow> Value" where
  "logicNot (BooleanValue a) = (BooleanValue (\<not>a))" |
  "logicNot a = (UndefinedValue)"

fun abs :: "Value \<Rightarrow> Value" where
  "abs (IntegerValue a) = (
    if (sint a < 0)
      then (IntegerValue (-a))
      else (IntegerValue a))" |
  "abs a = (UndefinedValue)"

end

subsection "Expression Evaluation"
text \<open>
An evaluation function which evaluates an expression node within a state.
Uses the semantics defined within the Semantic locale.

The eval function is that function which defines the semantics of expressions.
\<close>
fun eval :: "Node \<Rightarrow> State \<Rightarrow> Value" where
  "eval (ConstNode a) s = a" |

  "eval (BinaryNode AddOp a b) s = (Semantic.add (eval a s) (eval b s))" |
  "eval (BinaryNode SubOp a b) s = (Semantic.sub (eval a s) (eval b s))" |
  "eval (BinaryNode MulOp a b) s = (Semantic.mul (eval a s) (eval b s))" |
  "eval (BinaryNode DivOp a b) s = (Semantic.divide (eval a s) (eval b s))" |
  "eval (BinaryNode EqualOp a b) s = (Semantic.equal (eval a s) (eval b s))" |
  "eval (BinaryNode LessOp a b) s = (Semantic.less (eval a s) (eval b s))" |
  "eval (BinaryNode AndOp a b) s = (Semantic.logicAnd (eval a s) (eval b s))" |
  "eval (BinaryNode OrOp a b) s = (Semantic.logicOr (eval a s) (eval b s))" |
  "eval (BinaryNode XorOp a b) s = (Semantic.logicXor (eval a s) (eval b s))" |

  "eval (UnaryNode MinusOp e) s = (Semantic.uminus (eval e s))" |
  "eval (UnaryNode NotOp e) s = (Semantic.logicNot (eval e s))" |
  "eval (UnaryNode AbsOp e) s = (Semantic.abs (eval e s))" |

  "eval (LookupNode a) s = (s a)" |
 
  "eval (ConditionalNode cond true false) s =
    (if (Eval.bool (eval cond s))
      then (eval true s)
      else (eval false s))"


subsection "Statement Evaluation"
text \<open>
Statements or control nodes are evaluated using the exec function which
executes the node and performs some actions.
\<close>
function exec :: "ControlNode \<Rightarrow> State \<Rightarrow> State" where
  "exec (EndNode) s = s" |
  "exec (IfNode cond trueBranch falseBranch) s = 
    (if (Eval.bool (eval cond s)) 
      then (exec trueBranch s) 
      else (exec falseBranch s))" |
  "exec (AssignNode ident expr next) s = (exec next (update ident (eval expr s) s))" |
  "exec (WriteNode expr next) s = (exec next
  (update
    ''stdout''
    (StringValue ((Eval.str (s ''stdout'')) @ (Eval.str (eval expr s)))) s
  ))" |
  "exec (WhileNode cond body next) s = 
    (if (Eval.bool (eval cond s))
      then (exec (WhileNode cond body next) (exec body s))
      else (exec next s))"
  by (metis ControlNode.exhaust surj_pair) auto
termination
  sorry

end
