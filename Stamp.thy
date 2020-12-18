theory Stamp
imports "HOL-Word.Word"
begin

fun bit_bounds :: "nat \<Rightarrow> (int \<times> int)" where
  "bit_bounds bits = (((2 ^ bits) div 2) * -1, ((2 ^ bits) div 2) - 1)"

datatype Stamp = 
  FloatStamp
  | IllegalStamp
  | IntegerStamp (stp_bits: nat) (stp_lower: int) (stp_upper: int)
  | KlassPointerStamp
  | MethodCountersPointerStamp
  | MethodPointersStamp
  | ObjectStamp
  | RawPointerStamp
  | VoidStamp


fun meet :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "meet (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (IntegerStamp b1 (min l1 l2) (max u1 u2))
  )" | 
  "meet s1 s2 = IllegalStamp"

fun join :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "join (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (IntegerStamp b1 (max l1 l2) (min u1 u2))
  )" | 
  "join s1 s2 = IllegalStamp"

fun unrestricted :: "Stamp \<Rightarrow> Stamp" where
  "unrestricted (IntegerStamp bits lower upper) = (IntegerStamp bits (fst (bit_bounds bits)) (snd (bit_bounds bits)))" | 
  "unrestricted _ = IllegalStamp"

fun empty :: "Stamp \<Rightarrow> Stamp" where
  "empty (IntegerStamp bits lower upper) = (IntegerStamp bits (snd (bit_bounds bits)) (fst (bit_bounds bits)))" |
  "empty stamp = IllegalStamp"


value "unrestricted (IntegerStamp 8 0 10)"
value "unrestricted (IntegerStamp 16 0 10)"
value "unrestricted (IntegerStamp 32 0 10)"

value "empty (IntegerStamp 8 0 10)"
value "empty (IntegerStamp 16 0 10)"
value "empty (IntegerStamp 32 0 10)"

value "join (IntegerStamp 32 0 20) (IntegerStamp 32 (-100) 10)"
value "meet (IntegerStamp 32 0 20) (IntegerStamp 32 (-100) 10)"

end