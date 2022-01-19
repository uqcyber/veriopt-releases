theory Phase
  imports Main
  keywords 
    "phase" :: thy_decl and 
    "trm" :: quasi_command
begin

ML_file "map.ML"
ML_file "phase.ML"

ML \<open>
structure StringRule : Rule =
struct
type T = string;
end

structure StringPhase = DSL_Phase(StringRule);

fun phase_theory_init name trm thy = 
  Local_Theory.init 
    {background_naming = Sign.naming_of thy,
        setup = StringPhase.enter name trm,
        conclude = StringPhase.exit}
    {define = Generic_Target.define Generic_Target.theory_target_foundation,
        notes = Generic_Target.notes Generic_Target.theory_target_notes,
        abbrev = Generic_Target.abbrev Generic_Target.theory_target_abbrev,
        declaration = K Generic_Target.theory_declaration,
        theory_registration =  Generic_Target.theory_registration,
        locale_dependency = fn _ => error "Not possible in instantiation target",
        pretty = fn _ => [Pretty.str "temporary"]}
    thy

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>phase\<close> "open an optimization phase context"
   (Parse.binding --| Parse.$$$ "trm" -- Parse.const --| Parse.begin
     >> (fn (name, trm) => Toplevel.begin_main_target true (phase_theory_init name trm)));
\<close>

phase hello_there
  trm f
begin

end

end