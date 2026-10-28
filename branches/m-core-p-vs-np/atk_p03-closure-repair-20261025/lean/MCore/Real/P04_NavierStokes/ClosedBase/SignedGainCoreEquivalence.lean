import MCore.Real.P04_NavierStokes.SourceBinding

namespace MCore.Real.P04_NavierStokes.ClosedBase.SignedGainCoreEquivalence

open P04_NavierStokes.SourceBinding

def evidence : SourceEvidence :=
  { name := "SignedGainCoreEquivalence"
    kind := .closedBase
    sourceRepo := canonicalNSRepo
    sourceRef := canonicalNSRef
    sourcePath := "audit/producer-first/SignedGainCore.lean"
    theoremName := "nonempty_signedGainCertificate_iff_core"
    semanticScope := "For nonnegative viscosity, the full certificate is inhabited iff the smaller SignedGainCore is inhabited."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P04_NavierStokes.ClosedBase.SignedGainCoreEquivalence.evidence_is_source_verified

end MCore.Real.P04_NavierStokes.ClosedBase.SignedGainCoreEquivalence
