theory GraalIR2
  imports Main

begin

type_synonym ID = "int"

class IRNode =
  fixes successors :: "'a \<Rightarrow> 'a list"
  fixes inputs :: "'a \<Rightarrow> 'a list"

class ConstNode = IRNode +
  fixes val :: "'a \<Rightarrow> int"

class BinaryNode = IRNode +
  assumes is_binary: "\<forall>n. length(inputs(n)) = 2"

(*
class AddNode = BinaryNode +
  assumes ...
*)

class PhiNode = IRNode +
  fixes xxx :: "'a"

class IRGraph =
  fixes start :: "'a" 
  fixes nodes :: "'a set"
  fixes node :: "'a \<Rightarrow> IRNode"
  fixes succ_seq :: "'a \<Rightarrow> 'a list"
  fixes input_seq :: "'a \<Rightarrow> 'a list"
  fixes succ_set :: "'a \<Rightarrow> 'a set"
  fixes input_set :: "'a \<Rightarrow> 'a set"
  assumes start_a_node: "start \<in> nodes"
  assumes succ_nodes: "\<forall>n. n \<in> nodes \<Longrightarrow> succ_set(n) \<subseteq> nodes"
  assumes input_nodes: "\<forall>n. n \<in> nodes \<Longrightarrow> input_set(n) \<subseteq> nodes"
  assumes succ_list_set: "\<forall>n. n \<in> nodes \<Longrightarrow> succ_set(n) = elems(succ_seq(n))"
  assumes input_list_set: "\<forall>n. n \<in> node \<Longrightarrow> input_set(n) = elems(input_seq(n))"

instantiation int :: IRGraph
begin

end
