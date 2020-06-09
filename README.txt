This directory contains several alternative Isabelle models of the GraalVM IR Graph
(Intermediate Representation Graph).

Including:
  * GraalIR1.thy - explicit graph with int IDs inside the nodes.
  * GraalIT1_fromID.thy - same explicit graph but using functions from IDs to Nodes.
  * GraalIR2.thy - unsuccessful attempt at using Isabelle classes to model the Java subtype hierarchy.
  * GraalIR3_exprs.thy - explicit graph for control flow, but expressions (FloatingNode) as trees.
  * GraalRecords.thy - unsuccessful attempt at using Isabelle extensible records for Java subtype hierarchy.

  * exprs/Base.thy etc. - statements and expressions all modelled as trees (from Brae's thesis).

