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

definition node0 :: "IRNode" where
  "node0 = \<lparr> dummy = 0 \<rparr>"

definition node1 :: "IR2" where
  "node1 = \<lparr> dummy = 0, successors = [], inputs = [] \<rparr>"

definition one_node :: "ConstNode" where
  "one_node = \<lparr> dummy = 0, successors = [node0], inputs = [], val = 1 \<rparr>"

(* Unfortunately, the record type system does not seem to allow
   different subtypes of records to appear where the supertype is expected.
*)
definition polymorphic_node :: "ConstNode" where
  "polymorphic_node = \<lparr> dummy = 0, successors = [node1], inputs = [], val = 1 \<rparr>"

end
