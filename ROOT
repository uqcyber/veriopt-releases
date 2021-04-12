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

session Semantics in Semantics = Graph +
  description
    "Semantics of GraalVM graphs"
  theories
    IREval
    IRStepObj

session Proofs in Proofs = Semantics +
  description
    "Supporting proof theories and definitions"
  options [quick_and_dirty]
  theories
    IRGraphFrames
    Stuttering

session Optimizations in Optimizations = Proofs +
  description
    "Graph transformation optimizations"
  options [quick_and_dirty]
  theories
    Canonicalization
    ConditionalElimination

session Tests in Tests = Optimizations +
  description
    "Miscellaneous project testing"
  theories
    AssertTesting
    ExecExamples
    UnitTesting
    ConditionalEliminationTests

session ATVA2021 in ATVA2021 = Optimizations +
  description
    "Content for ATVA2021 paper"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    ATVA2021
  document_files (in "../document")
    "root.tex"
    "mathpartir.sty"

session ASE2021 in ASE2021 = Optimizations +
  description
    "Content for ASE2021 paper"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    ASE2021
  document_files (in "../document")
    "root.tex"
    "mathpartir.sty"

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
