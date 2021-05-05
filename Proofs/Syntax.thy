subsection \<open>Custom Syntax\<close>

theory Syntax
imports
  Semantics.IRStepObj
  MyBisimulation
keywords
  "optimization_phase" :: thy_decl and
  "optimization" :: thy_goal_defn and
  "optimization_tactic" :: thy_goal_defn and
  "perform" "goal" "rewrite" and 
  "analyse" "traverse" "assign" :: quasi_command and
  "print_optimizations" :: diag
begin

(* this theory is still a big WIP *)

definition sound :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "sound g g' = (\<forall>m h nid. (nid \<in> ids g \<longrightarrow> (nid m h | g \<sim> g')))"

ML \<open>
type optimization_tactic =
  {name: string, goals: string list(*, fixes: string,
   goals: string, rewrite: string*)}

structure TacticStore = Theory_Data
(
  type T = optimization_tactic list;
  val empty = [];
  val extend = I;
  val merge = Library.merge (fn (_) => false);
);

val get = TacticStore.get;

fun add t thy = TacticStore.map t thy

val reset = TacticStore.put [];




fun trace_prop str =
Local_Theory.background_theory (fn ctxt => (tracing str; ctxt))

fun goal_prop str ctxt =
  let
    val prop = Syntax.read_prop ctxt str
  in
    Proof.theorem NONE (K I) [[(prop, [])]] ctxt
  end

fun to_prop ctxt str =
  (Syntax.read_prop ctxt str, [])

type thing = (binding * string option * mixfix) list

fun wrap_term t : (term * (term list)) =
  (t, [])

fun partial_conjunct (lhs, rhs) =
  Const ("HOL.conj", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"})
  $ lhs
  $ rhs

fun conjunct (terms:term list) t1 : term =
  List.foldr partial_conjunct t1 terms

fun assign (assignment:term * term) =
  Const ("HOL.eq", @{typ "IRNode \<Rightarrow> IRNode \<Rightarrow> bool"})
  $ fst assignment $ snd assignment;

fun goals
  ((
    name,
    tactic:string),
    assigns:(string * string) list)
   ctxt = 
  let
    val assigns = map (fn a => (Syntax.read_term ctxt ((fst a)^"::IRNode"), Syntax.read_term ctxt (snd a))) assigns;
    val assigns = (map assign assigns);

    fun after_qed thm_name thms lthy =
      let
        val thy' = ((Local_Theory.note (name, (flat thms)) lthy) |> snd)
      in
        (Local_Theory.note (name, flat thms) lthy) |> snd
      end

    (*val compilation = Predicate_Compile_Core.code_pred
      Predicate_Compile_Aux.default_options
      "flip_negation"
      ctxt*)

    val _ = @{print} {name = name, assigns = assigns}
  in
    Proof.theorem NONE (after_qed "mything") [map wrap_term assigns] ctxt
  end

type 'a optimization =
  {name: string, phase: string, class: optimization_tactic,
   rule: thm
(*, code: 'a Predicate.pred*)
}

val parse_optimization_declaration =
  Parse_Spec.thm_name "(" --| Parse.name -- Parse.$$$ ")" --| Parse.$$$ ":"

val parse_assignments =
  Scan.repeat (Parse.$$$ "assign" |-- Parse.name --| Parse.$$$ ":" -- Parse.term)

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>optimization\<close>
    "perform an optimization and open proof obligation"
    (parse_optimization_declaration
     -- parse_assignments
     >> goals);

fun do_nothing _ = (Local_Theory.background_theory I)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>optimization_phase\<close>
    "Whole optimization phase definition"
    (
      Parse.name
      -- Parse.$$$ "analyse"
      -- Parse.$$$ "traverse"
    >> do_nothing);


fun show_sound
  (obligation:term)
  (goals:(term list))
  (rewrite:term) =
  Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"})
  $ (Const ("HOL.implies", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"})
    $ conjunct goals rewrite
    $ obligation);

fun register_tactic thms ctxt =
  let
    val register = TacticStore.put [{name="ahhhh", goals=[""]}, {name="no", goals=[""]}]
  in
    Proof_Context.background_theory (register) ctxt
  end

fun declare_tactic
  (((((
    name:string,
    target:string option),
    fixes:(binding * string option * mixfix) list),
    conditions:string list),
    goal:string),
    rewrite:string)
  thy =
  let
    val conditions = map (Syntax.read_term thy) conditions;
    val goal = Syntax.read_term thy goal;
    val rewrite = Syntax.read_term thy rewrite;

    val _ = @{print} {name = name, target = target, fixes = fixes, conditions = conditions,
                      goal = goal, rewrite = rewrite, thy = thy}
  in
    (Proof.theorem NONE register_tactic [[(wrap_term (show_sound @{term "sound g g'"} [goal] rewrite))]] thy)
  end

val parse_fixes =
  Scan.repeat (Parse.$$$ "fixes" |-- Parse.!!! Parse_Spec.locale_fixes)

val parse_target =
  Scan.option (Parse.$$$ ":" |-- Parse.name)

val parse_conditions =
  Scan.repeat (Parse.$$$ "when" |-- Parse.prop)

val parse_goal =
  (Parse.$$$ "goal" |-- Parse.prop)

val parse_rewrite =
  (Parse.$$$ "rewrite" |-- Parse.prop)

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>optimization_tactic\<close>
    "define a new tactic to specify optimizations"
    (
      Parse.name
      -- parse_target 
      -- (parse_fixes >> flat)
      -- parse_conditions
      -- parse_goal
      -- parse_rewrite
    >> declare_tactic);

fun print_optimizations ctxt =
  Pretty.writeln (Pretty.str "hi");

fun print_optimizations ctxt =
  let
    fun print_goals goal =
      Pretty.str goal;
    fun print_tact tact =
      Pretty.big_list
        ((#name tact) ^ ":")
        ((map print_goals (#goals tact)));
  in
    [Pretty.big_list "optimization_tactics:" (map print_tact (get ctxt))]
  end |> Pretty.writeln_chunks;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_optimizations\<close>
    "print debug information for optimizations"
    (Scan.succeed
      (Toplevel.keep (print_optimizations o Toplevel.theory_of)));
\<close>


optimization_tactic soundness
  fixes g :: IRGraph
  fixes g' :: IRGraph
  goal "sound g g'"
  rewrite "g' = g"
  by simp

ML_val "TacticStore.get (Proof_Context.theory_of @{context})"
print_optimizations

ML \<open>Proof_Context.background_theory (TacticStore.put [{name="hi", goals=[]}])\<close>
print_optimizations

optimization_tactic data : soundness
  fixes before :: IRNode
  fixes after :: IRNode
  goal "(g m \<turnstile> before \<mapsto> res) \<and> (g m \<turnstile> after \<mapsto> res)"
  rewrite "kind g nid = before \<longrightarrow> (g' = replace_node nid after g)"
  sorry

setup \<open>
  TacticStore.put
    [{name="soundness", goals=["sound g g'"]},
    {name="data", goals=["(g m \<turnstile> before \<mapsto> res) \<and> (g m \<turnstile> after \<mapsto> res)"]}]
\<close>

ML_val "TacticStore.get (Proof_Context.theory_of @{context})"

print_optimizations

optimization_phase Canonicalization 
  analyse
  traverse

optimization flip_negation (data):
  assign before : "ConditionalNode cond tb fb"
  assign after : "LogicNegationNode flip"
  sorry

print_theorems

end