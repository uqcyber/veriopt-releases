theory SemanticsTest
  imports ExpressionRewrites
  (* This theory tests the wrapping around of the int32 values. *)
begin


print_locale! Semantic

context Semantic
begin
lemma Test1: "Semantic.add (IntegerValue 3) (IntegerValue 6) = (IntegerValue 9)"
  apply(simp)
  done

abbreviation big :: Value where "big \<equiv> IntegerValue (1024 * 1024)"
abbreviation maxint :: Value where "maxint \<equiv> IntegerValue (2^31-1)"

lemma TestMul: "mul big big = (IntegerValue 0)"
  apply(simp)
  done

lemma TestWrap: "add maxint maxint = (IntegerValue (-2))"
  by simp

lemma TestAbsNeg: "abs (IntegerValue (-3)) = (IntegerValue 3)"
  by simp

lemma TestAbsPos: "abs (IntegerValue 3) = (IntegerValue 3)"
  by simp

value "(2^31-1) div 1::int"

print_locale! Semantic

(* Division by zero is curious! But should never be allowed... *)
lemma TestDiv0: "divide maxint (IntegerValue 0) = (IntegerValue 0)"
  by (simp add: word_div_def)

lemma neg1_all_bits_set: "(NOT (-1 :: int32)) = 0"
  by auto

lemma "rewrite_add_1_5":
  shows "(BinaryNode AddOp (ConstNode (IntegerValue 1)) (ConstNode (IntegerValue 5)))
    \<turnstile>  (ConstNode (IntegerValue 6))"
  by auto

theorem "evaluate_1":
  shows "(BinaryNode AddOp (ConstNode (IntegerValue 1)) (ConstNode (IntegerValue 5)))
    \<turnstile>  ConstNode (IntegerValue 6)"
  by auto

theorem "negative":
  shows "(BinaryNode SubOp (ConstNode (IntegerValue 1)) (ConstNode (IntegerValue 2)))
    \<turnstile>  ConstNode (IntegerValue (-1))"
  by auto

theorem "overflow":
  shows "(BinaryNode MulOp (BinaryNode MulOp (BinaryNode MulOp (ConstNode (IntegerValue 1024)) (ConstNode (IntegerValue 1024))) (ConstNode (IntegerValue 1024))) (ConstNode (IntegerValue 10)))
    \<turnstile>  ConstNode (IntegerValue (-2147483648))"
  by auto

theorem "round":
  shows "(UnaryNode MinusOp (BinaryNode MulOp (BinaryNode DivOp (ConstNode (IntegerValue 123)) (ConstNode (IntegerValue 10))) (ConstNode (IntegerValue 10))))
    \<turnstile>  ConstNode (IntegerValue (-120))"
  by auto

end
end

