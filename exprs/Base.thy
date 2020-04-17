(* These theories of expression trees and rewrite rules
   originally came from Brae Webb's BSc honours thesis:

     "Verifying Semantics Preservation of Optimisation Passes"
     by Brae Webb
     School of Information Technology and Electrical Engineering,
     The University of Queensland,
     November 2019.
*)

section "Intermediate Representation"
text \<open>This defines the IR of expressions and statements
within a generic imperative programming language.

Expressions such as multiplication and variable look-up are expressed as nodes
which evaluate to a primitive value type. An expression node may contain further
nested expression nodes, forming a tree like structure.

Statements such as if and assignment are expressed as control nodes which store
their successor control node and any expression nodes they require as input.

The structure of program as a whole is a directed acyclic graph which
represents both the data flow and control flow of the program.

This is not dis-similar to the Graal IR
excluding the ability of the Graal IR to have a node pointed to from
multiple locations as a form of representation optimisation.
\<close>

theory Base
  imports
    Main
    "HOL-Word.Word_Bitwise"
begin

subsection "Values"
text \<open>
Primitive data types such as integers and booleans. Undefined values occur during
an evaluation of non type-correct expressions.
\<close>

(* This is unsigned, but we convert it to signed where needed. *)
type_synonym int32 = "32 word"


datatype Value =
  UndefinedValue |
  IntegerValue int32 |  (* just the 32-bit Java 'int' for the moment *)
  BooleanValue bool |
  StringValue string

subsection "Operations"
text \<open>
Operations are metadata for nodes, a binary node, for example, needs a BinaryOp
\<close>
datatype UnaryOp =
  AbsOp |
  MinusOp |
  NotOp

datatype BinaryOp =
  AddOp |
  SubOp |
  MulOp |
  DivOp |
  EqualOp |
  LessOp |
  AndOp |
  OrOp |
  XorOp

subsection "Nodes"
text \<open>
Data flow nodes are nodes which represent expressions that can be evaluated.
\<close>

text_raw \<open>\DefineSnippet{ir:data-node}{\<close>
datatype Node =
  ConstNode Value |
  BinaryNode BinaryOp Node Node |
  UnaryNode UnaryOp Node |
  LookupNode String.string |
  ConditionalNode Node Node Node
text_raw \<open>}%EndSnippet\<close>

text \<open>
Control flow nodes are nodes which represent the control structure of a program
that can be run, these correspond loosely to statements.
\<close>
text_raw \<open>\DefineSnippet{ir:control-node}{\<close>
datatype ControlNode =
  EndNode |
  IfNode Node ControlNode ControlNode |
  WhileNode Node ControlNode ControlNode |
  AssignNode String.string Node ControlNode |
  WriteNode Node ControlNode
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{ir:example}{\<close>
value "(IfNode
  (BinaryNode LessOp (LookupNode ''max'') (LookupNode ''value''))
  (WriteNode (ConstNode (BooleanValue True)) next)
  (WriteNode (ConstNode (BooleanValue False)) next)
)"
text_raw \<open>}%EndSnippet\<close>

value "(IfNode (ConstNode x) (EndNode) (EndNode))"

subsection "State"
text \<open>
State is a type for storing the local variable state of an executing program.
A state consists of a mapping of identifier strings to values.
\<close>
type_synonym State = "String.string \<Rightarrow> Value"

text \<open>The update function inserts a new identifier-value pair into an existing state.\<close>
fun update :: "String.string \<Rightarrow> Value \<Rightarrow> State \<Rightarrow> State" where
  "update ident value state = (\<lambda>id2.(if (id2 = ident) then value else state id2))"

text \<open>
emptyState defines a state with an empty stdout and all other values map to undefined value.
\<close>
fun emptyState :: "String.string \<Rightarrow> Value" where
  "emptyState ident = (
  if (ident = ''stdout'')
    then (StringValue '''')
    else UndefinedValue)"

text \<open>
A state within this system can be used as in the example below where an empty state
is used to create an initial state function before a new variable mapping is added.

Later the value of the variable is looked up by calling the resulting state function.
\<close>
value "(update answer (IntegerValue 42) emptyState) answer"



section "Refinement"
text \<open>
Definition of a refinement relationship of values.

A refinement relationship here means that either the values are equal or 
the value being refined is an undefined value.

Every value can be refined by the undefined value. Allowing for rewriting rules
to account for the possibility of a node evaluating to the UndefinedValue type.
\<close>
fun refines :: "Value \<Rightarrow> Value \<Rightarrow> bool" (infixl "\<tturnstile>" 50) where
  "refines UndefinedValue y = True" |
  "refines x y = (x = y)"

lemma refines_def:
  assumes "a \<tturnstile> b"
  shows "(a = UndefinedValue) \<or> (a = b)"
  using assms refines.elims(2) by auto


section "Evaluation"
text \<open>Coercion evaluations of values into specific primitive types.\<close>
locale Eval
begin
fun bool :: "Value \<Rightarrow> bool" where
  "bool (BooleanValue a) = a" |
  "bool a = False"

fun int :: "Value \<Rightarrow> int" where
  "int (IntegerValue a) = sint a" |
  "int a = -1"

fun int_to_str :: "int \<Rightarrow> string \<Rightarrow> string" where
  "int_to_str x r = (if (x \<ge> 10) 
    then (int_to_str (x div 10) ([char_of (48 + x mod 10)] @ r))
    else ([char_of (48 + x)] @ r))"

fun bool_to_str :: "bool \<Rightarrow> string" where
  "bool_to_str True = ''True''" |
  "bool_to_str False = ''False''"

fun str :: "Value \<Rightarrow> string" where
  "str (IntegerValue a) = (int_to_str (sint a) '''')" |
  "str (BooleanValue a) = (bool_to_str a)" |
  "str (StringValue a) = a" |
  "str (UndefinedValue) = ''Undef''"

end

end
