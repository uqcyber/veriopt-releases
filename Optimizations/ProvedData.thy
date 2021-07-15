theory ProvedData
  imports Main
keywords
  "data" :: thy_goal_defn and
  "print_data" :: diag
begin


ML \<open>
type data =
  {name: string, expression: term}

signature DATA_LIST =
sig
  val get: theory -> data list
  val add: data -> theory -> theory
  val reset: theory -> theory
end;

structure DataList: DATA_LIST =
struct

structure DataStore = Theory_Data
(
  type T = data list;
  val empty = [];
  val extend = I;
  val merge = Library.merge (fn (_) => true);
);

val get = DataStore.get;

fun add t thy = DataStore.map (cons t) thy

val reset = DataStore.put [];

end;

fun open_data_goal
  ((bind: binding, _), exp: string) ctxt = 
  let
    val prop = Syntax.read_prop ctxt exp;
    val term = Syntax.read_term ctxt exp;
 
    val register = DataList.add {name=Binding.print bind, expression=term}

    fun after_qed _ ctxt =
      (Local_Theory.background_theory register ctxt)
  in
    Proof.theorem NONE after_qed [[(prop, [])]] ctxt
  end

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>data\<close>
    "define an data and open proof obligation"
    (Parse_Spec.thm_name ":"
     -- Parse.term
     >> open_data_goal);


(* Printing *)
fun print_data ctxt =
  let
    fun print_rule tact =
      Pretty.block [
        Pretty.str ((#name tact) ^ ": "),
        Syntax.pretty_term @{context} (#expression tact)
      ];
  in
    [Pretty.big_list "data:" (map print_rule (DataList.get ctxt))]
  end

fun apply_print_data thy =
  (print_data thy |> Pretty.writeln_chunks)


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_data\<close>
    "print data"
    (Scan.succeed
      (Toplevel.keep (apply_print_data o Toplevel.theory_of)));
\<close>

setup \<open>DataList.reset\<close>

print_data
ML_val \<open>DataList.get (Proof_Context.theory_of @{context})\<close>

data example:
  "(x::int) < y \<Longrightarrow> x \<le> y"
  print_data
  ML_val \<open>DataList.get (Proof_Context.theory_of @{context})\<close>
  by simp

data example2:
  "(x::int) > 0 \<Longrightarrow> x \<ge> 0"
  by simp

ML_val \<open>DataList.get (Proof_Context.theory_of @{context})\<close>
print_data

end
