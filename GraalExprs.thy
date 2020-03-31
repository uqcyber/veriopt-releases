theory GraalExprs
imports Main
begin

type_synonym Stamp = int  (* TODO: build a representation of types *)

section expressions
(*========================================================================
This section takes a 'value-oriented' view of expressions.

It ignores Node IDs, and treats nodes just as values, with
'inputs' that correspond to the Graal IR inputs.
So equality of these nodes is value-based, so roughly corresponds to
the global value numbering equivalence that is done in Graal.
 
The Graal IR 'Node' type is an abstract class with many subclasses.
We define it as a datatype comprised of the *leaf* classes.
If we need to know the set of intermediate abstract classes (like FixedNode or FloatingNode), 
we define those as predicates, named 'isa_<AbstractClassName>(n)'.
========================================================================== *)


(* TODO: could we build up this hierarchy using type classes?
   With this concrete datatype as the instantiation?
*)

datatype IRNode =
  ConstantNode (*String? value*) int
  | ParameterNode (*index*) int
  | AddNode (*x*) IRNode (*y*) IRNode
  | SubNode (*x*) IRNode (*y*) IRNode
  (* and hundreds of other Node subclasses!... *)

(* Next we need some predicates for abstract superclasses. *)
definition isa_BinaryArithmeticNode :: "IRNode \<Rightarrow> bool" where
  "isa_BinaryArithmeticNode node = (\<exists> x y. node = (AddNode x y) \<or> node = (SubNode x y))"

(* ValueNode.isConstant() *)
definition isConstant :: "IRNode \<Rightarrow> bool" where
  "isConstant node = (\<exists> val. node = (ConstantNode val))"



(* These two functions will model our two kinds of edges. *)

(* TODO: type_synonym SuccessorEdges = "IRNode \<Rightarrow> IRNode list" *)
fun inputEdges :: "IRNode \<Rightarrow> IRNode list" where
  "inputEdges (ConstantNode i) = []" |
  "inputEdges (ParameterNode i) = []" |
  "inputEdges (AddNode x y) = [x, y]" |
  "inputEdges (SubNode x y) = [x, y]"



(* An example expression: (aa + 1) - aa *)
abbreviation eg_aa :: IRNode where
  "eg_aa \<equiv> (ParameterNode 5)"

(* Example of value equivalence of expressions. *)
lemma aa1_eq: "(AddNode eg_aa (ConstantNode 2)) = (AddNode eg_aa (ConstantNode (1+1)))"
  apply(simp)
  done

abbreviation eg_a1a :: IRNode where
  "eg_a1a \<equiv> (SubNode (AddNode eg_aa (ConstantNode 1)) eg_aa)"

lemma expr_a1a_binary [simp]: "isa_BinaryArithmeticNode(eg_a1a)"
  apply(simp add: isa_BinaryArithmeticNode_def)
  done

lemma const_is_constant [simp]: "isConstant(ConstantNode i)"
  apply(simp add: isConstant_def)
  done



section canonical
(*========================================================================
This section is a translation of the 'AddNode/SubNode.canonical' optimization.

An example goal is to prove that canonical("(aa + 1) - aa)") returns "1".
========================================================================== *)



end
