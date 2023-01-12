theory Class
  imports Canonicalizations.Common
begin

text \<open> Representation of a Generic Class containing fields, methods and constructors \<close>

text \<open> _____ Representation of a Field _____ \<close>

type_synonym FieldName = "string"
type_synonym FieldType = "string"

datatype JVMField = 
  NewField (field_name: FieldName)
           (field_type: FieldType)

text \<open> _____ Representation of a Method _____ \<close>

type_synonym MethodName = "string"
type_synonym ReturnType = "string"
type_synonym MethodParameters = "string" (* TODO change to more detailed type containing type information perhaps *)
type_synonym MethodUniqueName = "string"

(* TODO could extend this to include exceptions throwable? *)
datatype JVMMethod = 
  NewMethod (method_name: MethodName)
            (method_returnType: ReturnType)
            (method_parameters: MethodParameters) 
            (method_unique_name: MethodUniqueName)

text \<open> _____ Representation of a Constructor _____ \<close>

type_synonym ConstructorParameters = "string" (* TODO change to more detailed type containing type information perhaps *)

datatype JVMConstructor = 
  NewConstructor (constructor_params: ConstructorParameters)

text \<open> Representation of a standard class \<close>

type_synonym Fields = "JVMField list"
type_synonym Methods = "JVMMethod list"
type_synonym Constructors = "JVMConstructor list"

type_synonym ClassName = "string"
type_synonym ParentClass = "string"

datatype JVMClass = 
  NewClass (class_name: ClassName) 
           (class_fields: Fields) 
           (class_methods: Methods) 
           (class_constructors: Constructors)  
           (class_parent: ParentClass)

(* Testing simple implementation *)

(*

public class bestClassEver extends Object {

    private int x;
    private float y;

    public bestClassEver(int x) {
        this.x = x;
    }
    
    public bestClassEver(float y) {
        this.y = y;
    }
    
    public int getX() {
        return this.x;
    }
    
    public void setY(float newY) {
        this.y = newY;
    }
}

*)

definition bestClassEver :: "JVMClass" where 
  "bestClassEver = 
    NewClass ''bestClassEver'' 
             [NewField ''x'' ''I'', NewField ''y'' ''float''] 
             [NewMethod ''getX'' ''I'' ''null'' ''bestClassEver_getXI(n)'', NewMethod ''setY'' ''null'' ''float'' ''bestClassEver_SetYn(f)''] 
             [NewConstructor ''I'', NewConstructor ''float''] 
             ''Object''"

(* Testing class-based functions *)
value "class_name bestClassEver"
value "class_parent bestClassEver"
value "class_fields bestClassEver"
value "class_methods bestClassEver"
value "class_constructors bestClassEver"

(* Testing field-based functions *)
value "field_name (hd (class_fields bestClassEver))"
value "field_type (hd (class_fields bestClassEver))"

value "field_name (hd (tl (class_fields bestClassEver)))"
value "field_type (hd (tl (class_fields bestClassEver)))"

(* Testing method-based functions *)
value "method_name (hd (class_methods bestClassEver))"
value "method_returnType (hd (class_methods bestClassEver))"
value "method_parameters (hd (class_methods bestClassEver))"
value "method_unique_name (hd (class_methods bestClassEver))"

value "method_name (hd (tl (class_methods bestClassEver)))"
value "method_returnType (hd (tl (class_methods bestClassEver)))"
value "method_parameters (hd (tl (class_methods bestClassEver)))"
value "method_unique_name (hd (tl (class_methods bestClassEver)))"

(* Testing constructor-based functions *)
value "constructor_params (hd (class_constructors bestClassEver))"

value "constructor_params (hd (tl (class_constructors bestClassEver)))"

end