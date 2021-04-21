subsection \<open>Custom Syntax\<close>

theory Syntax
imports
  Semantics.IRStepObj
  Bisimulation
keywords
  "optimization_phase" :: thy_decl and
  "optimization" :: thy_goal_defn and
  "perform" "of"
begin

(* this theory is still a big WIP *)

ML \<open>
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

(*
fun conjunct ((top::rest):term list) : term =
  Const ("HOL.conj", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"})
  $ top
  $ (conjunct rest)
  | conjunct (top::[]) = top
  | conjunct [] = @{term n}
*)

fun goals ((((name, f), t), props), action) ctxt = 
  let
    val (_, fixedc) = Variable.add_fixes ["g", "g'"] ctxt

    (*val props = map (to_prop fixedc) props*)
    val act = Syntax.read_term fixedc action
    val combination =   Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"})
                      $ (Const ("HOL.implies", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"})
                      $ conjunct (map (Syntax.read_term ctxt) props)
                        act
                      $ ((Const ("Bisimulation.strong_noop_bisimilar",
                                @{typ "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool"}))
                      $ (Free ("nid", @{typ ID}))
                      $ (Free ("g", @{typ IRGraph}))
                      $ (Free ("g'", @{typ IRGraph}))))
    
    (*val assums = Proof.assume [] [wrap_term combination] []*)

    (*val theory = (Proof.theorem NONE (K I) ([act] :: [(con, [])] :: [props]) fixedc)*)

    fun after_qed thm_name thms lthy =
      Local_Theory.note (name, (flat thms)) lthy |> snd
  in
    (Proof.theorem NONE (after_qed "mything") [[(wrap_term combination)]] fixedc)
    (*Proof.set_facts [@{thm def_Collect_coinduct}] (Proof.begin_block (Proof.init ctxt1))*)
    (*Proof.assume [] [props] [] (Proof.init fixedc)*)
    (* Proof.fix_cmd f (Proof.init ctxt1) *)
    (*Proof.fix_cmd f (Proof.theorem NONE (K I) ([act] :: [(con, [])] :: [props]) fixedc)*)
  end

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>optimization\<close>
    "perform an optimization and open proof obligation"
    (Parse_Spec.thm_name "of" --
      (Parse.params) --
      (Parse.keyword_improper "and" |-- Parse.params) --
      Scan.repeat (Parse.keyword_improper "assumes" |-- Parse.prop) --
      (Parse.keyword_improper "perform" |-- Parse.prop)
     >> goals);

fun do_nothing name = (Local_Theory.background_theory I)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>optimization_phase\<close>
    "quotient type definitions (require equivalence proofs)"
    (Parse.name |-- Parse.begin >> do_nothing);
\<close>

value "Bisimulation.strong_noop_bisimilar A B"

value "HOL.Trueprop (HOL.implies A B)"

optimization_phase Canonicalization begin
  optimization flip_negation of g and g'
    assumes "kind g nid = (ConditionalNode cond tb fb)"
    assumes "kind g cond = LogicNegationNode flip"
    perform "g' = replace_node nid ((ConditionalNode flip fb tb),s) g"
    sorry

  print_theorems

    (*"\<lbrakk>kind g nid = (ConditionalNode cond tb fb);
      kind g cond = LogicNegationNode flip;
      g' = replace_node nid ((ConditionalNode flip fb tb),s) g\<rbrakk>
      \<Longrightarrow> True"*)

(*
      (* FIXME Parse.type_args_constrained and standard treatment of sort constraints *)
      (Parse_Spec.overloaded -- (Parse.type_args -- Parse.binding --
        Parse.opt_mixfix -- (\<^keyword>\<open>=\<close> |-- Parse.typ) -- (\<^keyword>\<open>/\<close> |--
          Scan.optional (Parse.reserved "partial" -- \<^keyword>\<open>:\<close> >> K true) false -- Parse.term) --
        Scan.option (\<^keyword>\<open>morphisms\<close> |-- Parse.!!! (Parse.binding -- Parse.binding)) --
        Scan.option (\<^keyword>\<open>parametric\<close> |-- Parse.!!! Parse.thm))
      >> (fn (overloaded, spec) => quotient_type_cmd {overloaded = overloaded} spec))\<close>
*)

end