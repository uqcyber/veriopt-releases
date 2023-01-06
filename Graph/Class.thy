theory Class
  imports Canonicalizations.Common
begin

text \<open> Representation of a Generic Class \<close>

(** For now, make fields, methods and constructors just strings (their name) **)

(* Use lists for fields, methods and constructors *)
type_synonym Fields = "string list"
type_synonym Methods = "string list"
type_synonym Constructors = "string list"

(* Use strings for class & superclass name *)
type_synonym ClassName = "string"
type_synonym ParentClass = "string"

(** Extremely simple class representation **)
datatype Classz = 
  Classz (name: ClassName) 
         (fields: Fields) 
         (methodsz: Methods) 
         (constructors: Constructors)  
         (parent: ParentClass)

end