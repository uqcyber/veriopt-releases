chapter "veriopt"

session Graph in Graph = "HOL-Library" +
  description
    "GraalVM IR structure"
  options [quick_and_dirty]
  theories
    Values
    IRNodes
    IRNodeHierarchy
    Stamp
    IRGraph
    Comparison
    (* CFG -- will add back once sorries are fixed *)

session Semantics in Semantics = Graph +
  description
    "Semantics of GraalVM graphs"
  options [quick_and_dirty, document = pdf,
           document_output = "output",
           show_question_marks = false]
  theories
    IREval
    IRStepObj
  document_files (in "../latex")
    "root.tex"
    "mathpartir.sty"

session Proofs in Proofs = Semantics +
  description
    "Supporting proof theories and definitions"
  theories
    Bisimulation
    Form
    IRGraphFrames
    Rewrites
    Stuttering

session Optimizations in Optimizations = Proofs +
  description
    "Graph transformation optimizations"
  options [quick_and_dirty]
  theories
    Canonicalization
    CanonicalizationTree
    CanonicalizationProofs
    (*ConditionalElimination
    Construction*)

(*
session Tests in Tests = Optimizations +
  description
    "Miscellaneous project testing"
  theories
    AssertTesting
    ExecExamples
    UnitTesting
    (*ConditionalEliminationTests*)
*)

\<comment>\<open>All documentation sessions\<close>

session Document in "Papers/Main" = Optimizations +
  description
    "Whole project document"
  options [document = pdf, document_output = "output",
           document_variants="document:outline=/proof"]
  sessions
    Graph
    Semantics
    Proofs
    Optimizations
  document_theories
    Graph.Values
    Graph.IRNodes
    Graph.IRNodeHierarchy
    Graph.Stamp
    Graph.IRGraph

    Semantics.IREval
    Semantics.IRStepObj

    Proofs.Bisimulation
    Proofs.Form
    Proofs.IRGraphFrames
    Proofs.Rewrites
    Proofs.Stuttering

    Optimizations.Canonicalization
    Optimizations.CanonicalizationProofs
(*    Optimizations.ConditionalElimination
    Optimizations.Construction*)

  document_files (in ".")
    "root.tex"
  document_files (in "../../latex")
    "mathpartir.sty"

\<comment>\<open>Snippets for papers\<close>

session SemanticsPaper in "Papers/Semantics" = Optimizations +
  description
    "Content for IR semantics description paper"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    SemanticsSnippets
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"

(*session ValidationPaper in "Papers/Validation" = Tests +
  description
    "Content for paper on validation efforts"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    ValidationSnippets
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"*)
