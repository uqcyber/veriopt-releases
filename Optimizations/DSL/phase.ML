(*  Title:      Optimizations/DSL/phase.ML
    Author:     Brae Webb

Organisation of rewrites into phases
*)

signature Rule =
sig
  type T
end

signature DSL_PHASE =
sig
type T;

type phase =
  {name: binding,
   trm: term,
   rules: (binding, T) Map.map}

type store = (binding, phase) Map.map

datatype status =
  NoPhase |
  InPhase of binding

type state =
  {store: store,
   status: status}

val state: theory -> state
val current: theory -> phase option
val register: (binding * T) -> theory -> theory

val enter: binding -> string -> theory -> Proof.context
val exit: local_theory -> local_theory

end;

functor DSL_Phase(Rule: Rule): DSL_PHASE =
struct
type T = Rule.T



type phase =
  {name: binding,
   trm: term,
   rules: (binding, T) Map.map}

type store = (binding, phase) Map.map

datatype status =
  NoPhase |
  InPhase of binding

type state =
  {store: store,
   status: status}

val empty = {store=Map.empty, status=NoPhase};

fun merge_statuses (NoPhase, NoPhase) = NoPhase
  | merge_statuses (NoPhase, InPhase name) = InPhase name
  | merge_statuses (InPhase name, NoPhase) = InPhase name
  | merge_statuses (InPhase _, InPhase _) = raise ERROR "oh no"

structure PhaseData = Theory_Data
(
  type T = state;
  val empty = empty;
  fun merge (lhs, rhs) = 
    {status=merge_statuses (#status lhs, #status rhs),
     store= #store lhs}
);

val state = PhaseData.get;

fun phase_name thy = 
  (case #status (state thy) of
    NoPhase => NONE
    | InPhase name => SOME name)

fun phase_by_name data name : phase option =
  let
    val lookup = snd (#store data);
  in
    case name of
      NONE => NONE
      | SOME n => lookup n
  end

fun current thy = 
  let
    val phase = phase_name thy;
  in
    phase_by_name (state thy) phase
  end

fun expand_phase rule (phase: phase): phase =
  {name = (#name phase), trm = (#trm phase),
    rules = Map.insert (#rules phase) rule}

fun insert_rule' t phase data =
  let
    val phase' = expand_phase t phase;
    val data' = Map.insert (#store data) (#name phase, phase')
  in
    {status= #status data, store= data'}
  end

fun insert_rule t data =
  let
    val phase = (case (#status data) of
      NoPhase => raise TERM ("Optimization phase missing", []) |
      InPhase name => phase_by_name data (SOME name)
    );
    val data' = (case phase of
      NONE => raise TERM ("Optimization phase missing", []) |
      SOME phase => insert_rule' t phase data
    );
  in
    data'
  end

fun register t thy = PhaseData.map (insert_rule t) thy

fun new_phase name trm = {name = name, trm = trm, rules = Map.empty};

fun enter' name trm thy = PhaseData.map (fn state =>
  case (#status state) of
    NoPhase => {status=InPhase name, store=Map.insert (#store state) (name, new_phase name trm)} |
    InPhase _ => raise TERM ("optimization phase already established", [])
  ) thy

fun enter name trm thy =
  Proof_Context.init_global (enter' name (Syntax.read_term_global thy trm) thy)

fun exit' thy = PhaseData.map (fn state =>
  case (#status state) of
    NoPhase => raise TERM ("no phase to exit", []) |
    InPhase _ => {status=NoPhase, store=(#store state)}
  ) thy

val exit = Local_Theory.background_theory exit'

end