chapter "veriopt"

session Veriopt = "HOL-Library" +
  description
    "Veriopt ROOT session containing shared libraries"
  options [document = pdf, document_output = "output"]
  theories
    Snipping
  document_files (in "./latex")
    "root.tex"
    "mathpartir.sty"

session Graph in Graph = Veriopt +
  description
    "GraalVM IR structure"
  options [quick_and_dirty]
  theories
    Values
    IRNodes
    IRNodeHierarchy
    Stamp
    StampLattice
    IRGraph
    Traversal
    (*Comparison*)
    (* CFG -- will add back once sorries are fixed *)

session Semantics in Semantics = Graph +
  description
    "Semantics of GraalVM graphs"
  options [quick_and_dirty, document = pdf,
           document_output = "output",
           show_question_marks = false]
  sessions
    "HOL-Eisbach"
  theories
    IRTreeEval
    IRTreeEvalThms
    TreeToGraph
    TreeToGraphThms
    IRStepObj
    IRStepThms
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

session Optimizations in Optimizations = Semantics +
  description
    "Graph transformation optimizations"
  options [quick_and_dirty]
  theories
    (*Canonicalization*)
    CanonicalizationTree
    CanonicalizationTreeProofs
    CanonicalizationSyntax
    (*ConditionalElimination
    Construction*)

session Tests in Tests = Semantics +
  description
    "Miscellaneous project testing"
  theories
    AssertTesting
    ExecExamples
    (*Test: UnitTesting*)
    (*Test: ArithmeticTesting*)
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
    Proofs
    Optimizations
  document_theories
    Graph.Values
    Graph.IRNodes
    Graph.IRNodeHierarchy
    Graph.Stamp
    Graph.IRGraph

    Semantics.IRTreeEval
    Semantics.IRTreeEvalThms
    Semantics.TreeToGraph
    Semantics.TreeToGraphThms
    Semantics.IRStepObj
    Semantics.IRStepThms

    Proofs.Bisimulation
    Proofs.Form
    Proofs.IRGraphFrames
    Proofs.Rewrites
    Proofs.Stuttering
    Graph.Traversal

    Optimizations.CanonicalizationTree
    Optimizations.CanonicalizationTreeProofs
  document_files (in ".")
    "root.tex"
  document_files (in "../Stamps")
    "lattice.tex"
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
  sessions
    Optimizations
  theories
    ValidationSnippets
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"

session Stamps in "Papers/Stamps" = Graph +
  description
    "GraalVM Stamp Theory"
  options [document = pdf,
           document_output = "document",
           document_variants="document:outline=/proof"]
  sessions
    Graph
  document_theories
    Graph.StampLattice
  document_files (in ".")
    "root.tex"
    "lattice.tex"
  document_files (in "../../latex")
    "mathpartir.sty"

session TreePaper in "Papers/Tree" = Optimizations +
  description
    "Content for paper on validation efforts"
  options [quick_and_dirty, document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    TreeSnippets
    SlideSnippets
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"


session Canonicalization in "Papers/Canonicalization" = Optimizations +
  description
    "Canonicalization optimizations"
  options [quick_and_dirty, document = pdf, document_output = "output",
           show_question_marks = false]
  document_theories
    Optimizations.CanonicalizationSyntax
  document_files (in ".")
    "root.tex"
  document_files (in "../../latex")
    "mathpartir.sty"
