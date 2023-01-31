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

text \<open> _____ Representation of a standard class _____ \<close>

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


(* Empty class to indicate that the class being queried does not exist in the JVMClass mapping *)
definition emptyClass :: "JVMClass" where 
  "emptyClass = NewClass ''empty'' [] [] [] ''empty''"

(* Not true generally, but true for now *)
lemma ownParent:
  assumes "class = NewClass n f m c p"
  shows "n \<noteq> p" sorry

text \<open> _____ General Functions _____ \<close>

(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index v (x # xs) = (if (x=v) then 0 else find_index v xs + 1)"

text \<open> _____ Functions to interact with JVMClasses _____ \<close>

(* Returns the index of a class in the JVMClass list *)
fun find_class_index :: "string \<Rightarrow> JVMClass list \<Rightarrow> nat" where
  "find_class_index name cl = find_index name (map class_name (cl))"

(* Returns a JVMClass given its name and the JVMClass mapping *)
fun get_JVMClass :: "string \<Rightarrow> JVMClass list \<Rightarrow> JVMClass" where 
  "get_JVMClass cName cList = 
    (if ((find_class_index cName cList) = (length cList)) 
      then emptyClass 
      else (nth cList (find_class_index cName cList)))" 

(* Returns the methods belonging to a particular class, given its name and the JVMClass mapping *)
fun get_Methods :: "string \<Rightarrow> JVMClass list \<Rightarrow> JVMMethod list" where
  "get_Methods cname clist = class_methods (get_JVMClass cname clist)"

(* Returns the simple signature of a method (e.g., "plus(I)I") given its fully-qualified name *)
fun get_simple_signature :: "string \<Rightarrow> string" where
  "get_simple_signature fqn = rev (take (find_index (CHR ''.'') (rev fqn)) (rev fqn))"

(* Returns the simple signatures of all the methods belonging to a given class *)
fun simple_signatures :: "string \<Rightarrow> JVMClass list \<Rightarrow> string list" where
  "simple_signatures cname clist = (map get_simple_signature (map method_unique_name (get_Methods cname clist)))"

(* Either you are the Top (parent of java.lang.Object: ''None'') or you inherit from someone *)
datatype 'a inherit = Top | Node  'a "'a inherit"

(* Returns the parent of a given JVMClass *)
fun climb :: "JVMClass inherit \<Rightarrow> JVMClass inherit" where 
  "climb Top = Top" |
  "climb (Node class parent) = parent"

(* Returns a path from the given JVMClass to the Top of the class hierarchy tree, based on the 
   JVMClass list given *)
function toInherit :: "JVMClass \<Rightarrow> JVMClass list \<Rightarrow> JVMClass inherit" where
  "toInherit class cl = (
    if ((get_JVMClass (class_name class) cl) = emptyClass)
      then (Top)
      else (Node class (toInherit (get_JVMClass (class_parent class) cl) cl))
  )" 
  by auto  
termination using ownParent by blast


(** _____ Testing _____ **)

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
             [NewMethod ''getX'' ''I'' [NewParameter ''null''] ''bestClassEver_getXI(n)'', 
              NewMethod ''setY'' ''null'' [NewParameter ''float''] ''bestClassEver_SetYn(f)''] 
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
		[NewMethod ''plus'' ''I'' [NewParameter ''I''] ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I'', 
     NewMethod ''name'' ''I'' [NewParameter ''I''] ''UniqueName'']
		[NewConstructor []]
		''java.lang.Object'']"

(* Testing out functions *)
value "find_class_index ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' unit_InvokeVirtual_01_test_mapping"
value "get_JVMClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B'' unit_InvokeVirtual_01_test_mapping"
value "get_simple_signature ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I''"

end