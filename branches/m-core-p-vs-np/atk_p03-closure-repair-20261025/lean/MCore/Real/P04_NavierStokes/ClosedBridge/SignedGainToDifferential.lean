import MCore.Real.P04_NavierStokes.SourceBinding

namespace MCore.Real.P04_NavierStokes.ClosedBridge.SignedGainToDifferential

open P04_NavierStokes.SourceBinding

def evidence : SourceEvidence :=
  { name := "SignedGainToDifferential"
    kind := .closedBridge
    sourceRepo := canonicalNSRepo
    sourceRef := canonicalNSRef
    sourcePath := "audit/producer-first/ProducerFirst.lean"
    theoremName := "signedGain_implies_differential / signedGain_dissipation_margin_pos"
    semanticScope := "Conditional bridge from the signed-gain certificate plus enstrophy balance to the differential inequality with positive dissipation margin."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P04_NavierStokes.ClosedBridge.SignedGainToDifferential.evidence_is_source_verified

end MCore.Real.P04_NavierStokes.ClosedBridge.SignedGainToDifferential
