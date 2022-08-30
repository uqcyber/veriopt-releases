theory ProofStatus
  imports
    AbsPhase
    AddPhase
    (*AndPhase
    ConditionalPhase
    MulPhase
    (*NarrowPhase*)
    NegatePhase
    NewAnd
    NotPhase
    OrPhase
    ShiftPhase
    SignedDivPhase
    SignedRemPhase
    SubPhase
    TacticSolving
    XorPhase*)
begin

declare [[show_types=false]]
print_phases

thm_oracles abs_negate


end