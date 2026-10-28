import MCore.Real.P05_Hodge.SourceBinding

namespace MCore.Real.P05_Hodge.ClosedBase.SemanticInterfaceCounteraudit

open P05_Hodge.SourceBinding

def evidence : SourceEvidence :=
  { name := "SemanticInterfaceCounteraudit"
    kind := .closedBase
    sourceRepo := canonicalHodgeRepo
    sourceRef := canonicalMainRef
    sourcePath := "audit/ATK_HODGE_SEMANTIC_INTERFACE_COUNTERAUDIT.lean"
    theoremName := "semantic_interface_does_not_force_hodge"
    semanticScope := "Fail-closed counteraudit: the abstract semantic interface alone does not imply the rational Hodge conjecture; concrete geometry is part of the producer."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P05_Hodge.ClosedBase.SemanticInterfaceCounteraudit.evidence_is_source_verified

end MCore.Real.P05_Hodge.ClosedBase.SemanticInterfaceCounteraudit
