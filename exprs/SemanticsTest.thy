theory SemanticsTest
  imports Semantics
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
  apply(simp)
  done

lemma TestAbsNeg: "abs (IntegerValue (-3)) = (IntegerValue 3)"
  apply(simp)
  done

lemma TestAbsPos: "abs (IntegerValue 3) = (IntegerValue 3)"
  apply(simp)
  done

value "(2^31-1) div 1::int"

print_locale! Semantic

(* Division by zero is curious! But should never be allowed... *)
lemma TestDiv0: "divide maxint (IntegerValue 0) = (IntegerValue 0)"
  apply(simp add: word_div_def)
  done

end
end

