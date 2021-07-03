chapter "veriopt"

session Graph in Graph = "HOL-Library" +
  description
    "GraalVM IR structure"
  theories
    Values2
    IRNodes2
    IRNodeHierarchy
    Stamp2
    IRGraph
    (*Comparison*)
    (* CFG -- will add back once sorries are fixed *)

session Semantics in Semantics = Graph +
  description
    "Semantics of GraalVM graphs"
  options [quick_and_dirty, document = pdf,
           document_output = "output",
           show_question_marks = false]
  theories
    IRTreeEval
    IRTreeEvalThms
    IRStepObj
    (*IRStepThms*)
  document_files (in "../latex")
    "root.tex"
    "mathpartir.sty"

(*session Proofs in Proofs = Semantics +
  description
    "Supporting proof theories and definitions"
  theories
    Bisimulation
    Form
    IRGraphFrames
    Rewrites
    Stuttering*)

session Optimizations in Optimizations = Semantics +
  description
    "Graph transformation optimizations"
  options [quick_and_dirty]
  theories
    (*Canonicalization*)
    CanonicalizationTree
    CanonicalizationTreeProofs
    (*ConditionalElimination
    Construction*)

session Tests in Tests = Semantics +
  description
    "Miscellaneous project testing"
  theories
    AssertTesting
    ExecExamples
    UnitTesting
    (*ConditionalEliminationTests*)

\<comment>\<open>All documentation sessions\<close>

session Document in "Papers/Main" = Optimizations +
  description
    "Whole project document"
  options [document = pdf, document_output = "output",
           document_variants="document:outline=/proof"]
  sessions
    Graph
    Semantics
    (*Proofs*)
    Optimizations
  document_theories
    Graph.Values2
    Graph.IRNodes2
    Graph.IRNodeHierarchy
    Graph.Stamp2
    Graph.IRGraph

    Semantics.IRTreeEval
    Semantics.IRTreeEvalThms
    Semantics.IRStepObj
    (*Semantics.IRStepThms*)

    (*Proofs.Bisimulation
    Proofs.Form
    Proofs.IRGraphFrames
    Proofs.Rewrites
    Proofs.Stuttering
    Graph.Traversal*)

    Optimizations.CanonicalizationTree
    Optimizations.CanonicalizationTreeProofs
  document_files (in ".")
    "root.tex"
  document_files (in "../../latex")
    "mathpartir.sty"

\<comment>\<open>Snippets for papers\<close>

(* Currently preserved in atva branch 
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
*)

session ValidationPaper in "Papers/Validation" = Tests +
  description
    "Content for paper on validation efforts"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    ValidationSnippets
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"
