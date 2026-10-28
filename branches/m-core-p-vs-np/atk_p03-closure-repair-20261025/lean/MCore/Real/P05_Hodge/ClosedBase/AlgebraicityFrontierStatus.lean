import MCore.Real.P05_Hodge.SourceBinding

namespace MCore.Real.P05_Hodge.ClosedBase.AlgebraicityFrontierStatus

open P05_Hodge.SourceBinding

def evidence : SourceEvidence :=
  { name := "AlgebraicityFrontierStatus"
    kind := .closedBase
    sourceRepo := canonicalHodgeRepo
    sourceRef := canonicalFrozenRef
    sourcePath := "lean/MCore/HodgeReduction.lean"
    theoremName := "hodge_reduction_proved / pointwise_payload_open"
    semanticScope := "Structural min-cut certificate: the reduction is proved while the pointwise algebraicity payload remains the open bridge."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P05_Hodge.ClosedBase.AlgebraicityFrontierStatus.evidence_is_source_verified

end MCore.Real.P05_Hodge.ClosedBase.AlgebraicityFrontierStatus
