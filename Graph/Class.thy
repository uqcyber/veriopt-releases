theory Class
  imports Main
begin

text \<open> Representation of a standard class containing fields, methods and constructors \<close>

text \<open> ----- Representation of Fields and Parameters ----- \<close>

type_synonym FieldName = "string"
type_synonym FieldType = "string"
type_synonym ParameterType = "string"

datatype JVMField = 
  NewField (field_name: FieldName)
           (field_type: FieldType) |
  NewParameter (parameter_type: ParameterType)

text \<open> ----- Representation of a Method ----- \<close>

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

text \<open> ----- Representation of a Constructor ----- \<close>

type_synonym ConstructorParameters = "JVMField list"

datatype JVMConstructor = 
  NewConstructor (constructor_params: ConstructorParameters)

text \<open> ----- Representation of a standard class ----- \<close>

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

(* Empty placeholder class *)
definition emptyClass :: "JVMClass" where 
  "emptyClass = NewClass ''name_empty'' [] [] [] ''parent_empty''"

(* java.lang.Object *)
definition jlObject :: "JVMClass" where
  "jlObject = NewClass 
     ''java.lang.Object''
		[]
		[NewMethod ''finalize'' ''V'' [] ''java.lang.Object.finalize()V'', 
     NewMethod ''wait'' ''V'' [NewParameter ''J'', NewParameter ''I''] ''java.lang.Object.wait(JI)V'', 
     NewMethod ''wait'' ''V'' [] ''java.lang.Object.wait()V'', 
     NewMethod ''wait'' ''V'' [NewParameter ''J''] ''java.lang.Object.wait(J)V'', 
     NewMethod ''equals'' ''Z'' [NewParameter ''java.lang.Object''] ''java.lang.Object.equals(java.lang.Object)Z'', 
     NewMethod ''toString'' ''java.lang.String'' [] ''java.lang.Object.toString()java.lang.String'', 
     NewMethod ''hashCode'' ''I'' [] ''java.lang.Object.hashCode()I'', 
     NewMethod ''getClass'' ''java.lang.Class'' [] ''java.lang.Object.getClass()java.lang.Class'', 
     NewMethod ''clone'' ''java.lang.Object'' [] ''java.lang.Object.clone()java.lang.Object'', 
     NewMethod ''notify'' ''V'' [] ''java.lang.Object.notify()V'', 
     NewMethod ''notifyAll'' ''V'' [] ''java.lang.Object.notifyAll()V'']
		[NewConstructor []]
		''None''"

text \<open> ----- General Functions ----- \<close>

(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index v (x # xs) = (if (x=v) then 0 else find_index v xs + 1)"

text \<open> ----- Functions to interact with JVMClass lists ----- \<close>

(* Returns the index of a class in the JVMClass list *)
fun find_class_index :: "string \<Rightarrow> JVMClass list \<Rightarrow> nat" where
  "find_class_index name cl = find_index name (map class_name cl)"

(* Returns a JVMClass given its name and the JVMClass mapping *)
fun get_JVMClass :: "string \<Rightarrow> JVMClass list \<Rightarrow> JVMClass" where 
  "get_JVMClass cName cList = 
    (if ((find_class_index cName cList) = (length cList)) 
      then (emptyClass) 
      else (nth cList (find_class_index cName cList)))" 

(* Returns the methods belonging to a particular class, given its name and the JVMClass mapping *)
fun get_Methods :: "string \<Rightarrow> JVMClass list \<Rightarrow> JVMMethod list" where
  "get_Methods cname clist = class_methods (get_JVMClass cname clist)"

(* Returns the simple signature of a method (e.g., "plus(I)I") given its fully-qualified name *)
fun get_simple_signature :: "string \<Rightarrow> string" where
  "get_simple_signature fqn = rev (take (find_index (CHR ''.'') (rev fqn)) (rev fqn))"

(* Returns the simple signatures of all the methods belonging to a given class *)
fun simple_signatures :: "string \<Rightarrow> JVMClass list \<Rightarrow> string list" where
  "simple_signatures cname clist = 
    (map get_simple_signature (map method_unique_name (get_Methods cname clist)))"

fun classNames :: "JVMClass list \<Rightarrow> string set" where
  "classNames cl = set (map class_name cl) \<union> {''java.lang.Object''}"

fun parentRel :: "JVMClass list \<Rightarrow> string rel" where
  "parentRel cl = (set (map (\<lambda>c. (class_name c, class_parent c)) cl))"

fun parentRel2 :: "JVMClass list \<Rightarrow> (string \<times> string) list" where
  "parentRel2 cl = (map (\<lambda>c. (class_name c, class_parent c)) cl)"

fun parentOf :: "JVMClass list \<Rightarrow> (string \<rightharpoonup> string)" where
  "parentOf [] = Map.empty" |
  "parentOf (c#cl) = (parentOf cl)((class_name c) \<mapsto> (class_parent c))"

fun superclassOf :: "JVMClass list \<Rightarrow> (string rel)" where
  "superclassOf cl = trancl (parentRel cl)"

lemma "finite (set (l::('a list)))" 
  by simp

lemma domainUnion: 
  "dom (m(a\<mapsto>b)) = dom (m) \<union> {a}" 
  by simp

lemma "finite (dom (parentOf m))"  
  proof (induction m)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a m)
  then show ?case unfolding parentOf.simps
    by (metis insert_def singleton_conv sup_commute finite.simps domainUnion) 
qed

lemma wellFoundedParent:
  assumes "acyclic (parentRel cl)"
  shows "wf (parentRel cl)" 
    using assms unfolding parentRel.simps  
  by (metis (no_types, lifting) wf_set)

lemma transSuperClassOf[simp]:
  "trans (superclassOf cl)"
  by simp

(** ----- Testing ----- **)

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
value "parentRel unit_InvokeVirtual_01_test_mapping"
value "superclassOf unit_InvokeVirtual_01_test_mapping"
value "classNames unit_InvokeVirtual_01_test_mapping"
value "the (parentOf unit_InvokeVirtual_01_test_mapping ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'')"
value "set (simple_signatures ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' unit_InvokeVirtual_01_test_mapping)"

value "find_class_index ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A'' unit_InvokeVirtual_01_test_mapping"
value "get_JVMClass ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$B'' unit_InvokeVirtual_01_test_mapping"
value "get_simple_signature ''org.graalvm.compiler.jtt.micro.InvokeVirtual_01$A.plus(I)I''"

(* TODO: Extend current Classes definition to include all characteristics *)
(*
typedef Classes = "{cl :: JVMClass list . 
                    acyclic (parentRel cl) \<and> 
                    (\<forall>n y. (n,y) \<in> (parentRel cl) \<longrightarrow> (n, ''None'') \<in> (superclassOf cl))}" 
  morphisms classToJVMList Abs_Classes
proof -
  obtain cl where cl:  
    "cl = [NewClass ''java.lang.Object'' [] [] [] ''None'']" 
    by simp
  then have b: "acyclic (parentRel cl)"
    using acyclic_def cl by fastforce 
  then have c: "(\<forall>x y. (x,y) \<in> (parentRel cl) \<longrightarrow> (x, ''None'') \<in> (superclassOf cl))"
    by auto
  then show ?thesis  
    using a c1 b cl by blast 
qed*)

(* Lemmas to help with Classes invariants *)
lemma containsObjImplies[simp]: 
  shows "List.member cl jlObject \<longrightarrow> 
        (''java.lang.Object'',''None'') \<in> parentRel cl \<longrightarrow> 
        List.member (parentRel2 cl) (''java.lang.Object'',''None'')" 
  using List.member_def by fastforce

lemma containsObjImpliesNonEmpty:
  shows "List.member cl jlObject \<longrightarrow> cl \<noteq> []"
  using List.member_def by force

lemma acyclicDef: 
  fixes cl :: "JVMClass list"
  shows "acyclic (parentRel cl) \<Longrightarrow> (\<forall>j. j \<in> (set cl) \<longrightarrow> (class_name j \<noteq> class_parent j))"
  unfolding parentRel.simps acyclic_def by auto

typedef Classes = "{cl :: JVMClass list . 
                    List.member cl jlObject \<and>
                    cl \<noteq> [] }" 
  morphisms classToJVMList Abs_Classes
proof -
  obtain cl where cl:  
    "cl = [jlObject]" 
    by simp
  then have a: "cl \<noteq> []" 
    by simp
  then have b: "List.member cl jlObject"
    using cl by (simp add: member_rec(1))
  then show ?thesis 
    using cl by blast
qed

(* Equality *)
lemma classes_eq_iff:
  "cl1 = cl2 \<longleftrightarrow> classToJVMList cl1 = classToJVMList cl2" 
  by (simp add: classToJVMList_inject)

lemma classes_eqI:
  "classToJVMList cl1 = classToJVMList cl2 \<Longrightarrow> cl1 = cl2" 
  by (simp add: classToJVMList_inject)

(* Constructor *)
setup_lifting type_definition_Classes

lift_definition JVMClasses :: "JVMClass list \<Rightarrow> Classes" is
  "\<lambda>j. (if (List.member j jlObject) then j else [jlObject])" 
  apply (rule conjI) 
   unfolding List.member_def apply simp 
   using containsObjImpliesNonEmpty
  by auto

(* Maintaining invariant *)
lemma nonempty_cl [simp, intro]:
  "(classToJVMList cl) \<noteq> []" 
  using classToJVMList [of cl] by simp

lemma containsjlobj_cl [simp, intro]:
  "List.member (classToJVMList cl) jlObject"
  using classToJVMList [of cl] by simp

lemma original_jvm [simp]:
  "classToJVMList (JVMClasses cl) = (if (List.member cl jlObject) then cl else [jlObject])"
  using JVMClasses.rep_eq by auto

(* Abstraction transformation *)
lemma classesToClasses [simp, code abstype]:
  "JVMClasses (classToJVMList cl) = cl" 
  by (simp add: JVMClasses_def classToJVMList_inverse)

(* Operations *)
context
begin

(* empty = contains java.lang.Object only *)
qualified definition empty :: "Classes" where
  "empty = JVMClasses []"

qualified definition mapJVMFunc :: "(JVMClass \<Rightarrow> 'b) \<Rightarrow> Classes \<Rightarrow> 'b list" where
  "mapJVMFunc cf cl = List.map cf (classToJVMList cl)"

qualified definition member :: "Classes \<Rightarrow> JVMClass \<Rightarrow> bool" where
  "member cl c = List.member (classToJVMList cl) c"

qualified definition length :: "Classes \<Rightarrow> nat" where
  "length cl = List.length (classToJVMList cl)"

qualified definition nth :: "Classes \<Rightarrow> nat \<Rightarrow> JVMClass" where
  "nth cl n = List.nth (classToJVMList cl) n"

end

(* Code gen version with invariant maintained *)
lemma classToJVM_empty [simp, code abstract]:
  "classToJVMList Class.empty = [jlObject]"
  by (metis JVMClasses.rep_eq containsObjImpliesNonEmpty Class.empty_def)

lemma classToJVM_map [simp, code]:
  "(Class.mapJVMFunc f cl) = List.map f (classToJVMList cl)"
  by (simp add: Class.mapJVMFunc_def)

(* Code gen setup *)
code_datatype JVMClasses

lemma [code]:
  "classToJVMList (JVMClasses cl) = (if (List.member cl jlObject) then cl else [jlObject])"
  using JVMClasses.rep_eq by simp

definition newclass :: "Classes" where
  "newclass = JVMClasses [NewClass ''name'' [] [] [] ''parent'', jlObject]"

(* Testing code gen *)
value "newclass"
value "Class.mapJVMFunc class_name newclass"
value "Class.mapJVMFunc class_parent newclass"
value "classToJVMList newclass" 
value "classToJVMList (JVMClasses [])"

(* Redefining some functions in terms of Classes, not JVMClass list *)
(* TODO update original functions to these *)

(* Returns the index of a class in the Classes list *)
fun CLfind_class_index :: "string \<Rightarrow> Classes \<Rightarrow> nat" where
  "CLfind_class_index name cl = find_index name (Class.mapJVMFunc class_name cl)"

(* Returns a JVMClass given its name and the Classes list *)
fun CLget_JVMClass :: "string \<Rightarrow> Classes \<Rightarrow> JVMClass" where 
  "CLget_JVMClass cName cList = 
    (if ((CLfind_class_index cName cList) = (Class.length cList)) 
      then (emptyClass) 
      else (Class.nth cList (CLfind_class_index cName cList)))" 

(* Returns the methods belonging to a particular class, given its name and the Classes list *)
fun CLget_Methods :: "string \<Rightarrow> Classes \<Rightarrow> JVMMethod list" where
  "CLget_Methods cname clist = class_methods (CLget_JVMClass cname clist)"

(* Returns the simple signatures of all the methods belonging to a given class *)
fun CLsimple_signatures :: "string \<Rightarrow> Classes \<Rightarrow> string list" where
  "CLsimple_signatures cname clist = 
      (map get_simple_signature (map method_unique_name (CLget_Methods cname clist)))"

lemma finiteSuper: 
  fixes cl :: "Classes"
  shows "finite (superclassOf (classToJVMList cl))" 
  by simp

(* TODO fix this, won't work if the parent of classname occurs before classname in the listing *)
fun parentPath :: "(string \<times> string) list \<Rightarrow> string \<Rightarrow> string list" where
  "parentPath [] cn = []" |
  "parentPath ((x, y)#xs) cn = (let fullList = ((x, y)#xs) in
                                  if (x=cn) then ([y] @ (parentPath (remove1 (x, y) fullList) y)) 
                                  else                  (parentPath xs cn))" 

end