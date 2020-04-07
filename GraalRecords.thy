theory GraalRecords
  imports Main
begin

record "IRNode" =
  dummy :: int

record IR2 = IRNode +
  successors :: "IRNode list"
  inputs :: "IRNode list"

record ConstNode = IR2 +
  val :: "int"


(* Some example node values. *)
definition node0 :: "IRNode" where
  "node0 = \<lparr> dummy = 0 \<rparr>"

definition node1 :: IR2 where
  "node1 = \<lparr> dummy = 0, successors = [], inputs = [] \<rparr>"

definition one_node :: "ConstNode" where
  "one_node = \<lparr> dummy = 0, successors = [node0], inputs = [], val = 1 \<rparr>"


(* Unfortunately, the record type system does not seem to allow
   different closed subtypes of records to appear where the supertype is expected.
*)
definition polymorphic_node :: "ConstNode" where
  "polymorphic_node = \<lparr> dummy = 0, successors = [node1], inputs = [], val = 1 \<rparr>"
(*
Type unification failed: Clash of types "\<lparr>successors :: IRNode list, inputs :: IRNode list,
                                            \<dots> :: _\<rparr>" and "unit"

Type error in application: incompatible operand type

Operator:  IR2_ext ::
  IRNode list \<Rightarrow> IRNode list \<Rightarrow> ??'a \<Rightarrow> \<lparr>successors :: IRNode list, inputs :: IRNode list, \<dots> :: ??'a\<rparr>
Operand:   [node1] :: IR2 list
*)


(* And even 'open' records like n here get automatically closed by
   the typechecker, presumably because lists must a mono-typed.
 *)
value "(\<lambda> n . (\<lambda> c::ConstNode . [n, c])) one_node one_node" (* OK *)
value "(\<lambda> n . (\<lambda> c::ConstNode . [n, c]))    node1 one_node" (* Error *)
(*
Type unification failed

Failed to meet type constraint:

Term:  \<lambda>n c. [n, c] :: ConstNode \<Rightarrow> ConstNode \<Rightarrow> ConstNode list
Type:  'a IR2_scheme \<Rightarrow> ??'a
*)

end
