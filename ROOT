chapter "veriopt"

session Graph in Graph = "HOL-Library" +
  description
    "GraalVM IR structure"
  options [quick_and_dirty, document = pdf,
           document_output = "document",
           document_variants="document:outline=/proof"]
  theories
    Values
    IRNodes
    IRNodeHierarchy
    Stamp
    Stamp4
    IRGraph
    Comparison
  document_files (in "../latex")
    "root.tex"
    "mathpartir.sty"
  document_files (in "../Stamps")
    "lattice.tex"

session Stamps in Stamps = Graph +
  description
    "GraalVM Stamp Theory"
  options [quick_and_dirty, document = pdf,
           document_output = "document",
           document_variants="document:outline=/proof"]
  sessions
    Graph
  document_theories
    Graph.Stamp4
  document_files (in ".")
    "root.tex"
    "lattice.tex"
  document_files (in "../latex")
    "mathpartir.sty"

session Semantics in Semantics = Graph +
  description
    "Semantics of GraalVM graphs"
  options [document = pdf,
           document_output = "document"]
  theories
    IREval
    IRStepObj

session Proofs in Proofs = Semantics +
  description
    "Supporting proof theories and definitions"
  options [quick_and_dirty, document = pdf,
           document_output = "document",
           show_question_marks = false]
  theories
    Bisimulation
    Form
    IRGraphFrames
    Rewrites
    Stuttering
  document_files (in "../latex")
    "root.tex"
    "mathpartir.sty"
  document_files (in "../Stamps")
    "lattice.tex"

session Optimizations in Optimizations = Proofs +
  description
    "Graph transformation optimizations"
  options [quick_and_dirty, document = pdf,
           document_output = "document",
           show_question_marks = false]
  theories
    Canonicalization
    CanonicalizationProofs
    ConditionalElimination
    Construction
  document_files (in "../latex")
    "root.tex"
    "mathpartir.sty"
  document_files (in "../Stamps")
    "lattice.tex"

session Tests in Tests = Optimizations +
  description
    "Miscellaneous project testing"
  theories
    AssertTesting
    ExecExamples
    UnitTesting
    (*ConditionalEliminationTests*)

session ATVA2021 in ATVA2021 = Optimizations +
  description
    "Content for ATVA2021 paper"
  options [document = pdf, document_output = "output",
           show_question_marks = false, quick_and_dirty]
  theories
    ATVA2021
  document_files (in "../latex")
    "root.tex"
    "mathpartir.sty"
  document_files (in "../Stamps")
    "lattice.tex"

session ASE2021 in ASE2021 = Tests +
  description
    "Content for ASE2021 paper"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    ASE2021
  document_files (in "../latex")
    "root.tex"
    "mathpartir.sty"
  document_files (in "../Stamps")
    "lattice.tex"

session Document in Document = Optimizations +
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
    Optimizations.ConditionalElimination
    Optimizations.Construction
  document_files (in ".")
    "root.tex"
  document_files (in "../Stamps")
    "lattice.tex"

(*
session semantics = "HOL-Library" +
  description
    "GraalIR Semantics"
  options [document = pdf, document_output = "output", quick_and_dirty, show_question_marks = false]
  theories
    IRNodes
    IRNodeHierarchy
    IRGraph
    IREval
    IRStepObj
    IRGraphFrames
    Canonicalization
    (* ConditionalElimination *)
    ATVA2021
  document_files
    "root.tex"
    "mathpartir.sty"
*)
