theory Class
  imports Canonicalizations.Common
begin

text \<open> Representation of a standard class containing fields, methods and constructors \<close>

text \<open> _____ Representation of Fields and Parameters _____ \<close>

type_synonym FieldName = "string"
type_synonym FieldType = "string"
type_synonym ParameterType = "string"

datatype JVMField = 
  NewField (field_name: FieldName)
           (field_type: FieldType) |
  NewParameter (parameter_type: ParameterType)

text \<open> _____ Representation of a Method _____ \<close>

type_synonym MethodName = "string"
type_synonym ReturnType = "string"
type_synonym MethodParameters = "JVMField list"
type_synonym MethodUniqueName = "string"

(* TODO could extend this to include exceptions throwable? *)
datatype JVMMethod = 
  NewMethod (method_name: MethodName)
            (method_returnType: ReturnType)
            (method_parameters: MethodParameters)
            (method_unique_name: MethodUniqueName)

text \<open> _____ Representation of a Constructor _____ \<close>

type_synonym ConstructorParameters = "JVMField list"

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
             [NewMethod ''getX'' ''I'' [NewParameter ''null''] ''bestClassEver_getXI(n)'', NewMethod ''setY'' ''null'' [NewParameter ''float''] ''bestClassEver_SetYn(f)''] 
             [NewConstructor [NewParameter ''I''], NewConstructor [NewParameter ''float'']] 
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

(* Testing parameter-based functions *)
value "parameter_type (hd (method_parameters (hd (class_methods bestClassEver))))"
value "parameter_type (hd (method_parameters (hd (tl (class_methods bestClassEver)))))"

value "parameter_type (hd (constructor_params (hd (class_constructors bestClassEver))))"
value "parameter_type (hd (constructor_params (hd (tl (class_constructors bestClassEver)))))"


(* Samples from Java translator *)
definition unit_InstanceOfTest_instanceOfSnippet4_mapping :: "JVMClass list" where
	"unit_InstanceOfTest_instanceOfSnippet4_mapping = [
	NewClass ''org.graalvm.compiler.core.test.InstanceOfTest$B''
		[]
		[]
		[NewConstructor []]
		''org.graalvm.compiler.core.test.InstanceOfTest$A'',

	NewClass ''org.graalvm.compiler.core.test.InstanceOfTest$A''
		[]
		[]
		[NewConstructor []]
		''java.lang.Object'']"

definition unit_InvokeVirtual_01_test_mapping :: "JVMClass list" where
	"unit_InvokeVirtual_01_test_mapping = [
	NewClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B''
		[]
		[NewMethod ''plus'' ''I'' [NewParameter ''I''] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B.plus(I)I'']
		[NewConstructor []]
		''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'',

	NewClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$C''
		[]
		[NewMethod ''plus'' ''I'' [NewParameter ''I''] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$C.plus(I)I'']
		[NewConstructor []]
		''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'',

	NewClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A''
		[]
		[NewMethod ''plus'' ''I'' [NewParameter ''I''] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I'']
		[NewConstructor []]
		''java.lang.Object'']"

value "unit_InstanceOfTest_instanceOfSnippet4_mapping"
value "unit_InvokeVirtual_01_test_mapping"

end