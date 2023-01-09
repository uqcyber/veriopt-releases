theory Class
  imports Canonicalizations.Common
begin

text \<open> Representation of a Generic Class \<close>

(** For now, make fields, methods and constructors just strings (their name) **)

(* Use lists for fields, methods and constructors *)
(* TODO change to more detailed type soon *)
type_synonym Fields = "string"
type_synonym Methods = "string"
type_synonym Constructors = "string"

(* Use strings for class & superclass name *)
type_synonym ClassName = "string"
type_synonym ParentClass = "string"

(** Extremely simple class representation **)
datatype Classz = 
  NewClass (name: ClassName) 
           (fields: Fields) 
           (methodsz: Methods) 
           (constructors: Constructors)  
           (parent: ParentClass)

(* Functions, based on the Class.java class functions *)

(* Retrieves the name of this class *)
fun class_name :: "Classz \<Rightarrow> string" where
  "class_name (NewClass c_name _ _ _ _) = c_name"

(* Retrieves this class' superclass *)
fun class_super :: "Classz \<Rightarrow> string" where
  "class_super (NewClass _ _ _ _ c_super) = c_super"

(* Retrieves the fields of this class (currently, as a string) *)
fun class_fields :: "Classz \<Rightarrow> string" where
  "class_fields (NewClass _ c_fields _ _ _) = c_fields"

(* Retrieves the methods of this class (currently, as a string) *)
fun class_methods :: "Classz \<Rightarrow> string" where
  "class_methods (NewClass _ _ c_methods _ _) = c_methods"

(* Retrieves the constructors of this class (currently, as a string) *)
fun class_constructors :: "Classz \<Rightarrow> string" where
  "class_constructors (NewClass _ _ _ c_constructors _) = c_constructors"

(* Testing implementation *)
value "class_name (NewClass ''hello1'' ''hello2'' ''hello3'' ''hello4'' ''hello5'')"
value "class_super (NewClass ''hello1'' ''hello2'' ''hello3'' ''hello4'' ''hello5'')"
value "class_fields (NewClass ''hello1'' ''hello2'' ''hello3'' ''hello4'' ''hello5'')"
value "class_methods (NewClass ''hello1'' ''hello2'' ''hello3'' ''hello4'' ''hello5'')"
value "class_constructors (NewClass ''hello1'' ''hello2'' ''hello3'' ''hello4'' ''hello5'')"


end