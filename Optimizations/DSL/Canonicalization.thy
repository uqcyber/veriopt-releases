subsection \<open>Canonicalization DSL\<close>

theory Canonicalization
  imports
    Markup
    Phase
    "HOL-Eisbach.Eisbach"
  keywords
    "phase" :: thy_decl and 
    "terminating" :: quasi_command and
    "print_phases" :: diag and
    "export_phases" :: thy_decl and
    "optimization" :: thy_goal_defn
begin

print_methods

ML \<open>
datatype 'a Rewrite =
  Transform of 'a * 'a |
  Conditional of 'a * 'a * term |
  Sequential of 'a Rewrite * 'a Rewrite |
  Transitive of 'a Rewrite

type rewrite = {
  name: binding,
  rewrite: term Rewrite,
  proofs: thm list,
  code: thm list,
  source: term
}

structure RewriteRule : Rule =
struct
type T = rewrite;

(*
fun pretty_rewrite ctxt (Transform (from, to)) = 
      Pretty.block [
        Syntax.pretty_term ctxt from,
        Pretty.str " \<mapsto> ",
        Syntax.pretty_term ctxt to
      ]
  | pretty_rewrite ctxt (Conditional (from, to, cond)) = 
      Pretty.block [
        Syntax.pretty_term ctxt from,
        Pretty.str " \<mapsto> ",
        Syntax.pretty_term ctxt to,
        Pretty.str " when ",
        Syntax.pretty_term ctxt cond
      ]
  | pretty_rewrite _ _ = Pretty.str "not implemented"*)

fun pretty_thm ctxt thm =
  (Proof_Context.pretty_fact ctxt ("", [thm]))

fun pretty ctxt obligations t =
  let
    val is_skipped = Thm_Deps.has_skip_proof (#proofs t);

    val warning = (if is_skipped 
      then [Pretty.str "(proof skipped)", Pretty.brk 0]
      else []);

    val obligations = (if obligations
      then [Pretty.big_list 
              "obligations:"
              (map (pretty_thm ctxt) (#proofs t)),
            Pretty.brk 0]
      else []);      

    fun pretty_bind binding =
      Pretty.markup 
        (Position.markup (Binding.pos_of binding))
        [Pretty.str (Binding.name_of binding)];

  in
  Pretty.block ([
    pretty_bind (#name t), Pretty.str ": ",
    Syntax.pretty_term ctxt (#source t), Pretty.fbrk
  ] @ obligations @ warning)
  end
end

structure RewritePhase = DSL_Phase(RewriteRule);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>phase\<close> "enter an optimization phase"
   (Parse.binding --| Parse.$$$ "terminating" -- Parse.const --| Parse.begin
     >> (Toplevel.begin_main_target true o RewritePhase.setup));

fun print_phases print_obligations ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun print phase = RewritePhase.pretty print_obligations phase ctxt
  in 
    map print (RewritePhase.phases thy)
  end

fun print_optimizations print_obligations thy =
  print_phases print_obligations thy |> Pretty.writeln_chunks

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_phases\<close>
    "print debug information for optimizations"
    (Parse.opt_bang >>
      (fn b => Toplevel.keep ((print_optimizations b) o Toplevel.context_of)));

fun export_phases thy name =
  let
    val state = Toplevel.make_state (SOME thy);
    val ctxt = Toplevel.context_of state;          
    val content = Pretty.pure_string_of (Pretty.chunks (print_phases false ctxt));
    (*val cleaned = YXML.content_of content;   *) 
    val cleaned = content; 

    val filename = Path.explode (name^".rules");
    val directory = Path.explode "optimizations";
    val path = Path.binding (
                Path.append directory filename,
                Position.none);
    val thy' = thy |> Generated_Files.add_files (path, (Bytes.string content));

    val _ = Export.export thy' path [YXML.parse cleaned];

    val _ = writeln (Export.message thy' (Path.basic "optimizations"));
  in
    thy'
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>export_phases\<close>
    "export information about encoded optimizations"
    (Parse.path >>
      (fn name => Toplevel.theory (fn state => export_phases state name)))
\<close>

ML_file "rewrites.ML"

subsubsection \<open>Semantic Preservation Obligation\<close>

fun rewrite_preservation :: "IRExpr Rewrite \<Rightarrow> bool" where
  "rewrite_preservation (Transform x y) = (y \<le> x)" |
  "rewrite_preservation (Conditional x y cond) = (cond \<longrightarrow> (y \<le> x))" |
  "rewrite_preservation (Sequential x y) = (rewrite_preservation x \<and> rewrite_preservation y)" |
  "rewrite_preservation (Transitive x) = rewrite_preservation x"

subsubsection \<open>Termination Obligation\<close>

fun rewrite_termination :: "IRExpr Rewrite \<Rightarrow> (IRExpr \<Rightarrow> nat) \<Rightarrow> bool" where
  "rewrite_termination (Transform x y) trm = (trm x > trm y)" |
  "rewrite_termination (Conditional x y cond) trm = (cond \<longrightarrow> (trm x > trm y))" |
  "rewrite_termination (Sequential x y) trm = (rewrite_termination x trm \<and> rewrite_termination y trm)" |
  "rewrite_termination (Transitive x) trm = rewrite_termination x trm"

fun intval :: "Value Rewrite \<Rightarrow> bool" where
  "intval (Transform x y) = (x \<noteq> UndefVal \<and> y \<noteq> UndefVal \<longrightarrow> x = y)" |
  "intval (Conditional x y cond) = (cond \<longrightarrow> (x = y))" |
  "intval (Sequential x y) = (intval x \<and> intval y)" |
  "intval (Transitive x) = intval x"

subsubsection \<open>Standard Termination Measure\<close>

definition cond_cycles :: "nat" where "cond_cycles = 1"

(* Operators whose cycle cost is 0 *)
definition bin_empty_cycles :: "IRBinaryOp set" where
  "bin_empty_cycles = { BinShortCircuitOr }"

definition un_empty_cycles :: "IRUnaryOp set" where
  "un_empty_cycles = { UnaryLogicNegation }"

(* Returns a node's estimated CPU cycles *)
fun bin_cycles :: "IRBinaryOp \<Rightarrow> nat" where
  "bin_cycles BinAdd = 1" |
  "bin_cycles BinAnd = 1" |
  "bin_cycles BinDiv = 16" |
  "bin_cycles BinIntegerBelow = 1" |
  "bin_cycles BinIntegerEquals = 1" |
  "bin_cycles BinIntegerLessThan = 1" |
  "bin_cycles BinIntegerMulHigh = 2" |
  "bin_cycles BinIntegerNormalizeCompare = 2" |
  "bin_cycles BinIntegerTest = 2" |
  "bin_cycles BinLeftShift = 1" |
  "bin_cycles BinMod = 16" |
  "bin_cycles BinMul = 4" |
  "bin_cycles BinOr = 1" |
  "bin_cycles BinRightShift = 1" |
  "bin_cycles BinSub = 1" |
  "bin_cycles BinURightShift = 1" |
  "bin_cycles BinXor = 1" |
  "bin_cycles _ = 0"

fun un_cycles :: "IRUnaryOp \<Rightarrow> nat" where
  "un_cycles UnaryAbs = 2" |
  "un_cycles UnaryBitCount = 4" |
  "un_cycles UnaryIsNull = 2" |
  "un_cycles (UnaryNarrow b r) = 1" |
  "un_cycles UnaryNeg = 2" |
  "un_cycles UnaryNot = 1" |
  "un_cycles UnaryReverseBytes = 1" |
  "un_cycles (UnarySignExtend b r) = 1" |
  "un_cycles (UnaryZeroExtend b r) = 1" |
  "un_cycles _ = 0"

(* Calculates an expression's size in terms of the operands size and the operator's cycles *)
definition bin_exp_size :: "nat \<Rightarrow> IRBinaryOp \<Rightarrow> nat" where
  "bin_exp_size ops_size op = ops_size + bin_cycles op"

definition un_exp_size :: "nat \<Rightarrow> IRUnaryOp \<Rightarrow> nat" where
  "un_exp_size ops_size op = ops_size + un_cycles op"

(* General size calculation *)
fun size :: "IRExpr \<Rightarrow> nat" where
  unary_size:
  "size (UnaryExpr op x) = (un_exp_size ((size x) + 2) op)" |
  bin_const_size:
  "size (BinaryExpr op x (ConstantExpr cy)) = (bin_exp_size ((size x) + 2) op)" |
  bin_size:
  "size (BinaryExpr op x y) = (bin_exp_size ((size x) + (size y) + 2) op)" |
  cond_size:
  "size (ConditionalExpr c t f) = (size c) + (size t) + (size f) + cond_cycles" |
  const_size:
  "size (ConstantExpr c) = 1" |
  param_size:
  "size (ParameterExpr ind s) = 2" |
  leaf_size:
  "size (LeafExpr nid s) = 2" |
  "size (ConstantVar c) = 2" |
  "size (VariableExpr x s) = 2"

subsubsection \<open>Automated Tactics\<close>

named_theorems size_simps "size simplication rules"

method unfold_optimization =
  (unfold rewrite_preservation.simps, unfold rewrite_termination.simps,
    unfold intval.simps,
    rule conjE, simp, simp del: le_expr_def, force?)
  | (unfold rewrite_preservation.simps, unfold rewrite_termination.simps,
    rule conjE, simp, simp del: le_expr_def, force?)

method unfold_size =
  (((unfold size.simps, simp add: size_simps del: le_expr_def)?
  ; (simp add: size_simps del: le_expr_def)?
  ; (unfold bin_exp_size_def un_exp_size_def cond_cycles_def, auto simp: size_simps)?
  ; (unfold size.simps)?)[1])
  

print_methods

ML \<open>
structure System : RewriteSystem =
struct
val preservation = @{const rewrite_preservation};
val termination = @{const rewrite_termination};
val intval = @{const intval};
end

structure DSL = DSL_Rewrites(System);

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>optimization\<close>
    "define an optimization and open proof obligation"
    (Parse_Spec.thm_name ":" -- Parse.term
        >> DSL.rewrite_cmd);
\<close>

ML_file "~~/src/Doc/antiquote_setup.ML"


snipbegin \<open>PhaseRail\<close>
text \<open>
\<^rail>\<open>
@{syntax_def phase}: @'phase' @{syntax name} \<newline>
@'terminating' @{syntax measure} \<newline>
@'begin' (body*)
@'end'
;

@{syntax_def optimization}: @'optimization' @{syntax name} options? ':' \<newline>
rule proof
;

options: '[' (intval | subgoals) ']'
;

rule: term '\<mapsto>' term \<newline>
('when' condition ((condition '&&')*))?
;

@{syntax_def print_phases}: @'print_phases' '!'?
;

@{syntax_def export_phases}: @'export_phases' filename
;

@{syntax_def gencode}: @'gencode' filename term
;
\<close>

\<^descr> @{command phase}~\<open>name\<close>~\<open>terminating\<close>~\<open>measure\<close>
opens a new optimization phase environment.
A termination measure is provided as the measure argument.
All optimizations within the phase must satisfy termination for the given measure.

\<^descr> @{command optimization}~\<open>name\<close>
defines a new optimization rule with a proof of correctness.
An obligation for semantic preservation and termination are opened.
An optimization can only be defined within a \<^emph>\<open>phase\<close>.
                                                 
\<close>
snipend -

print_syntax

end