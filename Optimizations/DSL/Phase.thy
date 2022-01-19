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

fun pretty t = Pretty.str t
end

structure StringPhase = DSL_Phase(StringRule);

fun printer _ = [Pretty.str "temporary"]

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>phase\<close> "open an optimization phase context"
   (Parse.binding --| Parse.$$$ "trm" -- Parse.const --| Parse.begin
     >> (fn (name, trm) => Toplevel.begin_main_target true (StringPhase.setup (name, trm))));
\<close>

phase hello_there
  trm size
begin

end

end