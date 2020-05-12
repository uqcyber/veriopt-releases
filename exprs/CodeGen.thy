section "Code Generation"
text \<open>Mechanism for exporting rewriting rules as executable code.\<close>

theory CodeGen
  imports
    ExpressionRewrites
    StatementRewrites
begin 

typedef TypeCorrectNode = "{node :: Node . (\<forall>s::State . ((eval node s) \<noteq> UndefinedValue))}"
proof -
  have "\<exists>n. \<forall>f. eval n f \<noteq> UndefinedValue"
    by (metis (full_types) Value.simps(6) eval.simps(1))
  then show ?thesis
    by blast
qed

text \<open>
The Rewrite locale is a series of code lemmas that are translations of the theories
expressed in the collection of rewriting rules.

As code lemmas need to be in the function form which expresses equality, the
rewrite locale assumes that no nodes evaluate to UndefinedValue to prove equality.
This is possible as refinement is defined as the values being equal or one node
being an UndefinedValue, if we are to assume that no nodes may evaluate to UndefinedValue
then it is implicitly true given a rewriting rule and this assumption that the
nodes are semantically equal.

The definition rewrite is used within lemmas to bind the lemma to the rewrite
definition for code generation.
\<close>
text_raw \<open>\DefineSnippet{codegen:rewrite-locale}{\<close>
locale Rewrite =
  assumes noUndef: "\<forall> node::Node . \<forall> state::State . (eval node state \<noteq> UndefinedValue)"
begin

definition rewrite :: "Node \<Rightarrow> Node" where
  "rewrite Node = Node"
text_raw \<open>}%EndSnippet\<close>


lemma rewrite_conditional_true_code [code]:
  "rewrite (ConditionalNode (ConstNode (BooleanValue True)) trueBranch falseBranch)
    = trueBranch"
  using noUndef rewrite_conditional_true apply auto
  using refines_def by (meson eval.simps(1))

lemma rewrite_conditional_false_code [code]:
  "rewrite (ConditionalNode (ConstNode (BooleanValue False)) trueBranch falseBranch)
    = falseBranch"
  using noUndef rewrite_conditional_false apply auto
  using refines_def by (meson eval.simps(1))

(* TODO:
lemma rewrite_conditional_equal_code [code]:
  "rewrite (ConditionalNode (BinaryNode EqualOp a b) c d) = (
    if (a = c \<and> b = d)
      then b
      else (ConditionalNode (BinaryNode EqualOp a b) a b)
    )"
  using noUndef rewrite_conditional_equal apply auto
  using refines_def apply (meson eval.simps(14))
  using rewrite_def rewrite_conditional_false_code apply force
  by (meson eval.simps(14))
*)

lemma rewrite_add_sub_code [code]:
  "rewrite (BinaryNode AddOp (BinaryNode SubOp x y) z) = (
    if (y = z)
      then x
      else (BinaryNode AddOp (BinaryNode SubOp x y) z)
    )"
  using noUndef rewrite_add_sub apply auto
  using refines_def apply (meson eval.simps(14))
  by (simp add: rewrite_def)

lemma rewrite_add_sub2_code [code]:
  "rewrite (BinaryNode AddOp x (BinaryNode SubOp y z)) = (
    if (x = z)
      then y
      else (BinaryNode AddOp x (BinaryNode SubOp y z))
    )"
  using noUndef rewrite_add_sub2 apply auto
  using refines_def apply (meson eval.simps(14))
  by (simp add: rewrite_def)

text_raw \<open>\DefineSnippet{codegen:lemma-example}{\<close>
lemma rewrite_neutral_add_code [code]:
  "rewrite (BinaryNode AddOp e (ConstNode (IntegerValue 0))) = e"
text_raw \<open>}%EndSnippet\<close>
  using noUndef rewrite_neutral_add apply auto
  using refines_def by (meson eval.simps(1))

lemma rewrite_neutral_sub_code [code]:
  "rewrite (BinaryNode SubOp e (ConstNode (IntegerValue 0))) = e"
  using noUndef rewrite_neutral_sub apply auto
  using refines_def by (meson eval.simps(1))

(* TODO:
lemma rewrite_neutral_or_code [code]:
  "rewrite (BinaryNode OrOp e (ConstNode (BooleanValue False))) = e"
  using noUndef rewrite_neutral_or apply auto
  using refines_def by (meson eval.simps(1))
*)

(* TODO:
lemma rewrite_neutral_and_code [code]:
  "rewrite (BinaryNode AndOp e (ConstNode (BooleanValue True))) = e"
  using noUndef rewrite_neutral_and apply auto
  using refines_def by (meson eval.simps(1))
*)

end

text \<open>The interpretation of a rewrite as code cannot be generated for the
abstract locale.

In order to prove this interpretation we must find a way to express the conditions
under which no nodes would evaluation to an undefined value, i.e. we need to express
type correctness of all nodes.
\<close>
lemma type_correct:
  fixes result :: TypeCorrectNode
  shows "\<forall>s::State . (eval (Rep_TypeCorrectNode result) s) \<noteq> UndefinedValue"
  using Rep_TypeCorrectNode by auto

interpretation rewrite_interpretation: Rewrite
  sorry

text \<open>The export code mechanism of Isabelle used to export all rewriting rules
under the Rewrite locale.
\<close>

(* 
Temporarily disabled, due to the following codegen error:
This seems to be caused by Word.zero_word being a lifted "0" rather than a constructor.

"Word.zero_word_inst.zero_word" is not a constructor, on left hand side of equation, in theorem:
rewrite_interpretation.rewrite
 (BinaryNode SubOp ?e (ConstNode (IntegerValue zero_word_inst.zero_word))) \<equiv>
?e

text_raw \<open>\DefineSnippet{codegen:export}{\<close>
export_code Rewrite.rewrite in Scala module_name Compiler
export_code Rewrite.rewrite in Haskell module_name Compiler
text_raw \<open>}%EndSnippet\<close>
*)

end