import MCore.K9

namespace MCore.BackwardAudit

def InterfaceFinalStatement {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  ¬ ∀ L, C.inP L ↔ C.inNP L

def HypotheticalClosure {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  InterfaceFinalStatement C

theorem hypothetical_final
    {Language : Type}
    {C : ClassicalComplexityInterface Language}
    (H : HypotheticalClosure C) :
    InterfaceFinalStatement C :=
  H

#print axioms MCore.BackwardAudit.hypothetical_final

end MCore.BackwardAudit
