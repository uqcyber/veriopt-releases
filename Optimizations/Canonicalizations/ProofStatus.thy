theory ProofStatus
  imports
    AbsPhase
    AddPhase
    AndPhase
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
    XorPhase
begin

declare [[show_types=false]]
print_phases
print_phases!

print_methods

print_theorems

thm opt_add_left_negate_to_sub
thm_oracles AbsNegate

export_phases \<open>Full\<close>


end