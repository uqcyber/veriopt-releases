theory Base
(* These theories of expression trees and rewrite rules
   come from Brae Webb's BSc honours thesis:

     "Verifying Semantics Preservation of Optimisation Passes"
     by Brae Webb
     School of Information Technology and Electrical Engineering,
     The University of Queensland,
     November 2019.
*)
imports
  Main
begin

datatype Value =
  UndefinedValue |
  IntegerValue int |
  BooleanValue bool |
  StringValue string

(* Operations are metadata for nodes, a binary node, for example, needs a BinaryOp *)

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

(* Data flow nodes are nodes which represent expressions that can be evaluated. *)
datatype Node =
  ConstNode Value |
  BinaryNode BinaryOp (left:Node) (right:Node) |
  UnaryNode UnaryOp Node |
  LookupNode string |
  ConditionalNode Node Node Node

(* Control flow nodes represent the control structure of a program that
can be run.  These correspond loosely to statements. *)
datatype ControlNode =
  EndNode |
  IfNode Node ControlNode ControlNode |
  WhileNode Node ControlNode ControlNode |
  AssignNode String.string Node ControlNode |
  WriteNode Node ControlNode 


value "(IfNode
  (BinaryNode LessOp (LookupNode ''max'') (LookupNode ''value''))
  (WriteNode (ConstNode (BooleanValue True)) next)
  (WriteNode (ConstNode (BooleanValue False)) next)
  )"

value "(IfNode (ConstNode x) (EndNode) (EndNode))"




end
