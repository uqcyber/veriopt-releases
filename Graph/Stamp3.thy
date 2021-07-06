section \<open>Stamp Typing\<close>

theory Stamp3
  imports Values2
begin

text \<open>
The GraalVM compiler uses the Stamp class to store range and type information
for a given node in the IR graph.
We model the Stamp class as a datatype, Stamp, and provide a number of functions
on the datatype which correspond to the class methods within the compiler.

Stamp information is used in a variety of ways in optimizations, and so, we
additionally provide a number of lemmas which help to prove future optimizations.
\<close>


class stamp =
  fixes srange :: "'a \<Rightarrow> Value set"
  fixes sunrestricted :: "'a \<Rightarrow> Value set"
  (*fixes empty :: "Value set"*)
begin
definition range :: "'a \<Rightarrow> Value set" where
  "range s = srange s"
definition unrestricted :: "'a \<Rightarrow> Value set" where
  "unrestricted s = sunrestricted s"
definition meet :: "'a \<Rightarrow> 'a \<Rightarrow> Value set" where
  "meet s1 s2 = (srange s1) \<union> (srange s2)"
definition join :: "'a \<Rightarrow> 'a \<Rightarrow> Value set" where
  "join s1 s2 = (srange s1) \<inter> (srange s2)"
definition is_unrestricted :: "'a \<Rightarrow> bool" where
  "is_unrestricted s = (srange s = unrestricted s)"
definition is_empty :: "'a \<Rightarrow> bool" where
  "is_empty s = (srange s = empty)"
definition as_constant :: "'a \<Rightarrow> Value option" where
  "as_constant s = (if (card (srange s)) = 1
    then Some (SOME x. x \<in> srange s)
    else None)"
definition always_distinct :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "always_distinct stamp1 stamp2 = ((join stamp1 stamp2) = empty)"
definition never_distinct :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "never_distinct stamp1 stamp2 = 
    (as_constant stamp1 = as_constant stamp2 \<and> as_constant stamp1 \<noteq> None)"

definition valid_value :: "'a => Value => bool" where
  "valid_value stamp value = (value \<in> (srange stamp))"

lemma is_constant:
  assumes "srange s = {x}"
  shows "as_constant s = Some x"
  by (simp add: as_constant_def assms)

lemma is_not_constant:
  assumes "\<forall>x. srange s \<noteq> {x}"
  shows "as_constant s = None"
  using assms card_1_singletonE as_constant_def
  by metis

lemma valid_constant_equal:
  assumes "valid_value s x"
  assumes "as_constant s = Some v"
  shows "v = x"
  by (metis assms(1) assms(2) is_constant is_not_constant option.discI singletonD stamp.valid_value_def these_empty these_insert_Some)
  
end

\<comment> \<open>IntegerStamp implementation\<close>
datatype IntStamp = 
  Int8Stamp (lower_bound: int64) (upper_bound: int64) |
  Int16Stamp (lower_bound: int64) (upper_bound: int64) |
  Int32Stamp (lower_bound: int64) (upper_bound: int64) |
  Int64Stamp (lower_bound: int64) (upper_bound: int64)

fun narrow :: "int64 \<Rightarrow> int32" where
  "narrow bits = (word_of_int (Word.the_int bits))"
fun widen :: "int32 \<Rightarrow> int64" where
  "widen bits = (word_of_int (Word.the_int bits))"

fun int_range :: "IntStamp \<Rightarrow> Value set" where
  "int_range (Int8Stamp lower upper) = {IntVal32 (narrow x) | x . x \<in> {lower..upper}}" |
  "int_range (Int16Stamp lower upper) = {IntVal32 (narrow x) | x . x \<in> {lower..upper}}" |
  "int_range (Int32Stamp lower upper) = {IntVal32 (narrow x) | x . x \<in> {lower..upper}}" |
  "int_range (Int64Stamp lower upper) = {IntVal64 x | x . x \<in> {lower..upper}}"

fun bit_bounds :: "nat \<Rightarrow> ('a::len word \<times> 'a word)" where
  "bit_bounds bits = (((2 ^ bits) div 2) * -1, ((2 ^ bits) div 2) - 1)"

fun bit_range :: "nat \<Rightarrow> ('a::len word set)" where
  "bit_range bits = {((2 ^ bits) div 2) * -1 .. ((2 ^ bits) div 2) - 1}"

fun unrestricted_int :: "IntStamp \<Rightarrow> Value set" where
  "unrestricted_int (Int8Stamp lower upper) = 
    {IntVal32 x | x . x \<in> bit_range 32}" |
  "unrestricted_int (Int16Stamp lower upper) = 
    {IntVal32 x | x . x \<in> bit_range 32}" |
  "unrestricted_int (Int32Stamp lower upper) = 
    {IntVal32 x | x . x \<in> bit_range 32}" |
  "unrestricted_int (Int64Stamp lower upper) =
    {IntVal64 x | x . x \<in> bit_range 64}"

interpretation IntStamp : stamp
  "int_range :: IntStamp \<Rightarrow> Value set"
  "unrestricted_int :: IntStamp \<Rightarrow> Value set"
  done

instantiation IntStamp :: stamp
begin
instance proof qed
end

\<comment> \<open>VoidStamp implementation\<close>
typedecl VoidStamp

interpretation VoidStamp : stamp
  "(\<lambda>x. {}) :: VoidStamp \<Rightarrow> Value set"
  "(\<lambda>x. {}) :: VoidStamp \<Rightarrow> Value set"
  done

instantiation VoidStamp :: stamp
begin
instance proof qed
end

\<comment> \<open>IllegalStamp implementation\<close>
typedecl IllegalStamp

interpretation IllegalStamp : stamp
  "(\<lambda>x. {}) :: VoidStamp \<Rightarrow> Value set"
  "(\<lambda>x. {}) :: VoidStamp \<Rightarrow> Value set"
  done

instantiation IllegalStamp :: stamp
begin
instance proof qed
end

\<comment> \<open>Reference stamp implementations\<close>
datatype ReferenceStamp =
  RawPointerStamp (nonNull: bool) (alwaysNull: bool) |
  KlassPointerStamp (nonNull: bool) (alwaysNull: bool) |
  ObjectStamp (objType: string) (exactType: bool) (nonNull: bool) (alwaysNull: bool)

fun exclude_null :: "bool \<Rightarrow> Value set" where
  "exclude_null True = {ObjRef None}" |
  "exclude_null False = {}"

fun ref_range :: "ReferenceStamp \<Rightarrow> Value set" where
  "ref_range ref = (case (alwaysNull ref) of
    True \<Rightarrow> {ObjRef None} |
    False \<Rightarrow> {ObjRef x | x. True} - (exclude_null (nonNull ref)))"

definition unrestricted_ref :: "ReferenceStamp \<Rightarrow> Value set" where
  "unrestricted_ref ref = {ObjRef x | x. True}"

interpretation ReferenceStamp : stamp
  "ref_range :: ReferenceStamp \<Rightarrow> Value set"
  "unrestricted_ref :: ReferenceStamp \<Rightarrow> Value set"
  done

instantiation ReferenceStamp :: stamp
begin
instance proof qed
end

datatype Stamp =
  IntegerStamp (int: IntStamp) |
  ReferenceStamp (reference: ReferenceStamp) |
  VoidStamp |
  IllegalStamp

fun stamp_range :: "Stamp \<Rightarrow> Value set" where
  "stamp_range (IntegerStamp intstamp) = range intstamp" |
  "stamp_range (ReferenceStamp refstamp) = range refstamp" |
  "stamp_range (VoidStamp) = {}" |
  "stamp_range (IllegalStamp) = {}"

fun unrestricted_stamp :: "Stamp \<Rightarrow> Value set" where
  "unrestricted_stamp (IntegerStamp intstamp) = unrestricted intstamp" |
  "unrestricted_stamp (ReferenceStamp refstamp) = unrestricted refstamp" |
  "unrestricted_stamp (VoidStamp) = {}" |
  "unrestricted_stamp (IllegalStamp) = {}"

interpretation Stamp : stamp
  "stamp_range :: Stamp \<Rightarrow> Value set"
  "unrestricted_stamp :: Stamp \<Rightarrow> Value set"
  done

instantiation Stamp :: stamp
begin
instance proof qed
end


fun constant_as_stamp :: "Value \<Rightarrow> Stamp" where
  "constant_as_stamp (IntVal32 v) = IntegerStamp (Int32Stamp (widen v) (widen v))" |
  "constant_as_stamp (IntVal64 v) = IntegerStamp (Int64Stamp v v)" |
  "constant_as_stamp (UndefVal) = IllegalStamp" |
  "constant_as_stamp _ = IllegalStamp"  


definition default_stamp :: "Stamp" where
  "default_stamp = 
    (IntegerStamp (Int32Stamp (fst (bit_bounds 32)) (snd (bit_bounds 32))))"


(* new proofs *)
lemma (in stamp) disjoint_empty:
  assumes "joined = (join x_stamp y_stamp)"
  assumes "joined = {}"
  shows "(srange x_stamp) \<inter> (srange y_stamp) = {}"
  using assms(1) assms(2) join_def by force

lemma (in stamp) always_distinct_unequal:
  assumes "always_distinct x_stamp y_stamp"
  shows "\<forall> x y . (valid_value x_stamp x \<and> valid_value y_stamp y) \<longrightarrow> x \<noteq> y"
  using assms
  by (metis Set.set_insert insert_disjoint(1) local.always_distinct_def local.join_def local.valid_value_def)


lemma (in stamp) never_distinct_equal:
  assumes "never_distinct x_stamp y_stamp"
  shows "\<forall> x y . (valid_value x_stamp x \<and> valid_value y_stamp y) \<longrightarrow> x = y"
  using assms
proof -
  obtain x_const where "as_constant x_stamp = Some x_const"
    using never_distinct_def
    by (meson assms stamp.as_constant_def)
  then obtain y_const where "as_constant y_stamp = Some y_const"
    using never_distinct_def assms
    by fastforce  
  then show ?thesis
    using assms local.never_distinct_def local.valid_constant_equal by fastforce
qed

end