import MCore.Real.P04_NavierStokes.SourceBinding

namespace MCore.Real.P04_NavierStokes.ClosedBridge.CoreToCertificate

open P04_NavierStokes.SourceBinding

def evidence : SourceEvidence :=
  { name := "CoreToCertificate"
    kind := .closedBridge
    sourceRepo := canonicalNSRepo
    sourceRef := canonicalNSRef
    sourcePath := "audit/producer-first/SignedGainCore.lean"
    theoremName := "actualNSToSignedGain_of_core"
    semanticScope := "Conditional bridge: an ActualNSToSignedGainCore producer reconstructs the previously certified ActualNSToSignedGain producer for nonnegative viscosity."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P04_NavierStokes.ClosedBridge.CoreToCertificate.evidence_is_source_verified

end MCore.Real.P04_NavierStokes.ClosedBridge.CoreToCertificate
