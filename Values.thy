theory Values
  imports
    "HOL-Word.Word"
    "HOL-Library.Float"
begin

type_synonym objref = "nat option"

datatype UnstampedValue =
  UnstampedFloat (uv_m: int) (uv_e: int) |
  UnstampedInt (uv_i: int) |
  UnstampedObj (uv_n: objref)

datatype Value  =
  UndefVal |
  IntVal (v_bits: int) (v_int: int) |
  FloatVal (v_bits: int) (v_float: float) |
  ObjRef objref

end