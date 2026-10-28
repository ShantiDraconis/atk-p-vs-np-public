import MCore.K9

namespace MCore.BackwardAudit

def InterfaceFinalStatement {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  ¬ ∀ L, C.inP L ↔ C.inNP L

structure SeparationWitness {Language : Type}
    (C : ClassicalComplexityInterface Language) where
  L : Language
  hNP : C.inNP L
  hNotP : ¬ C.inP L

theorem separation_witness_closes
    {Language : Type}
    {C : ClassicalComplexityInterface Language}
    (W : SeparationWitness C) :
    InterfaceFinalStatement C :=
  witness_separates_classes C W.L W.hNP W.hNotP

def pnpWitnessWithoutOracleClosed : Bool := false

theorem pnp_without_oracle_still_open :
    pnpWitnessWithoutOracleClosed = false := by rfl

#print axioms MCore.BackwardAudit.separation_witness_closes
#print axioms MCore.BackwardAudit.pnp_without_oracle_still_open

end MCore.BackwardAudit
