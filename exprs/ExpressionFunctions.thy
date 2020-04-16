(*  Title:      ExpressionFunctions.thy
    Author:     Brae Webb

Definitions for expression rewrite rules expressed as functions
*)

theory ExpressionFunctions
  imports
    Semantics
    ExpressionRewrites
begin 

section \<open>Rewrite Rules\<close>

(*
inductive binary_induction :: "BinaryOp \<Rightarrow> Node \<Rightarrow> Node \<Rightarrow> Node \<Rightarrow> bool" where
  "binary_induction EqualOp a a (ConstNode (BooleanValue True))" |
  "binary_induction AddOp (BinaryNode SubOp x y) y x" | (* x - y + y = x *)
  "binary_induction AddOp x (BinaryNode SubOp y x) y" |
  "binary_induction AddOp e (ConstNode (IntegerValue 0)) e" |
  "binary_induction MulOp e (ConstNode (IntegerValue 0)) (ConstNode (IntegerValue 0))"
  (*"binary_induction f a b (BinaryNode f a b)"*)

fun binary_refinement_set :: "BinaryOp \<Rightarrow> Node \<Rightarrow> Node \<Rightarrow> Node set" where
  "binary_refinement_set op a b = {r . (binary_induction op a b r)}"

fun test :: "Node \<Rightarrow> Node \<Rightarrow> Node" where
  "test (BinaryNode op a b) n2 = (ConstNode (IntegerValue 2))" |
  "test (ConstNode x) n2 = (ConstNode (IntegerValue 3))" |
  "test n1 n2 = (ConstNode (IntegerValue 4))"

value "test r (ConstNode (IntegerValue 1))"
*)
(*
value "{r::Node . (test r (ConstNode (IntegerValue 1)))}"

value "{r::Node . (binary_induction  MulOp (ConstNode (IntegerValue 5)) (ConstNode (IntegerValue 0)) r)}"

value "binary_refinement_set MulOp (ConstNode (IntegerValue 5)) (ConstNode (IntegerValue 0))"
*)
(*
fun binary_refinement :: "BinaryOp \<Rightarrow> Node \<Rightarrow> Node \<Rightarrow> Node" where
  "binary_refinement op a c = (if (b op a c d) then d else (BinaryNode op a c))"
*)

(* Inductive relations *)
fun binary_refinement :: "BinaryOp \<Rightarrow> Node \<Rightarrow> Node \<Rightarrow> Node" where
  (* x - y + x - y *)

  (* e - y + y = e *)
  (* (x + y) - y = x *)
  (* x + y - y + y = ? *)

  (* x - y + z if x - y + y = x if x - y + x = y *)
  "binary_refinement AddOp (BinaryNode SubOp x y) z =
    (if (y = z)
      then x
      else
    (if (x = z)
      then y
      else (BinaryNode AddOp (BinaryNode SubOp x y) z)))" | (* x + y - x = y *)
  (*"binary_refinement AddOp e (ConstNode (IntegerValue i)) =
    (if (i = 0)
      then e
      else (BinaryNode AddOp e (ConstNode (IntegerValue i))))" |*)
  (*"binary_refinement MulOp e (ConstNode (IntegerValue 0)) = (ConstNode (IntegerValue 0))" |*)
  "binary_refinement f a b = (BinaryNode f a b)"


fun unary_refinement :: "UnaryOp \<Rightarrow> Node \<Rightarrow> Node" where
  "unary_refinement f a = (UnaryNode f a)"

theorem equality_by_refinement [simp]:
  fixes condition trueBranch falseBranch refinement :: Node
  assumes refines:
    "(ConditionalNode condition trueBranch falseBranch) \<turnstile> refinement"
  assumes undef:
    "eval (ConditionalNode condition trueBranch falseBranch) s \<noteq> UndefinedValue"
  shows
  "(ConditionalNode condition trueBranch falseBranch) = refinement"
  sorry

function conditional_refinement :: "Node \<Rightarrow> Node \<Rightarrow> Node \<Rightarrow> Node" where
  "conditional_refinement (ConstNode (BooleanValue True)) t f = t" |
  "conditional_refinement (ConstNode (BooleanValue False)) t f = f" |
  (*"conditional_refinement (BinaryNode EqualOp a b) t f = f" |*)
  "conditional_refinement c t f = (ConditionalNode c t f)"
  sorry
termination by (relation "{}") simp


fun refinement :: "Node \<Rightarrow> Node" where
  (*"refinement (BinaryNode f a b) = (binary_refinement f (refinement a) (refinement b))" |*)
  (*"refinement (BinaryNode f a b) = (binary_refinement f (refinement a) (refinement b))" |
  "refinement (UnaryNode f a) = (unary_refinement f (refinement a))" |*)
  "refinement (ConditionalNode c t f) = (conditional_refinement (refinement c) (refinement t) (refinement f))" |
  "refinement (ConstNode v) = (ConstNode v)" |
  "refinement (LookupNode v) = (LookupNode v)"

export_code refinement in Scala module_name Compiler

(*
value "(refinement (AbsNode (AbsNode (ConstNode (IntegerValue 2)))))"

value "(refinement (BinaryNode MulOp
                      (ConstNode (IntegerValue 5))
                      (ConstNode (IntegerValue 0))
       ))"

value "(refinement
  (ConditionalNode (BinaryNode EqualOp 
                      (BinaryNode MulOp
                        (ConstNode (IntegerValue 5)) 
                        (ConstNode (IntegerValue 0)))
                      (ConstNode (IntegerValue 0)))
    (ConstNode (IntegerValue 1))
    (ConstNode (IntegerValue 2))))
"
*)

(*
subsection "Neutral Constants"
theorem rewrite_neutral_add [simp]:
  fixes e :: Node
  shows "BinaryNode add e (ConstNode (IntegerValue 0)) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "add (eval e s) (IntegerValue 0) \<tturnstile> eval e s"
    by (cases "eval e s"; simp)
qed

theorem rewrite_neutral_sub [simp]:
  fixes e :: Node
  shows "(BinaryNode minus e (ConstNode (IntegerValue 0))) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "Base.minus (eval e s) (IntegerValue 0) \<tturnstile> eval e s"
    by (cases "eval e s"; simp)
qed

theorem rewrite_neutral_mul [simp]:
  fixes e :: Node
  shows "(BinaryNode times e (ConstNode (IntegerValue 1))) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "Base.times (eval e s) (IntegerValue 1) \<tturnstile> eval e s"
    by (cases "eval e s"; simp)
qed

theorem rewrite_neutral_div [simp]:
  fixes e :: Node
  shows "(BinaryNode divide e (ConstNode (IntegerValue 1))) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "Base.divide (eval e s) (IntegerValue 1) \<tturnstile> eval e s"
    by (cases "eval e s"; simp)
qed

theorem rewrite_neutral_or [simp]:
  fixes e :: Node
  shows "(BinaryNode logicOr e (ConstNode (BooleanValue False))) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "logicOr (eval e s) (BooleanValue False) \<tturnstile> eval e s"
    by (cases "eval e s"; simp)
qed

theorem rewrite_neutral_and [simp]:
  fixes e :: Node
  shows "(BinaryNode logicAnd e (ConstNode (BooleanValue True))) \<turnstile> e"
  apply auto
proof -
  fix s :: State
  show "logicAnd (eval e s) (BooleanValue True) \<tturnstile> eval e s"
    by (cases "eval e s"; simp)
qed
*)

end
