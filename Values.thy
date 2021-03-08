theory Values
  imports
    "HOL-Library.Word"
    "HOL-Library.Float"
    "HOL-Library.LaTeXsugar"
begin

type_synonym objref = "nat option"

datatype Value  =
  UndefVal |
  IntVal (v_bits: int) (v_int: int) |
  FloatVal (v_bits: int) (v_float: float) |
  ObjRef objref |
  ObjStr string

end