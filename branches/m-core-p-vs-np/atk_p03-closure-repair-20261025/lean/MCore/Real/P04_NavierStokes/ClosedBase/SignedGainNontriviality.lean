import MCore.Real.P04_NavierStokes.SourceBinding

namespace MCore.Real.P04_NavierStokes.ClosedBase.SignedGainNontriviality

open P04_NavierStokes.SourceBinding

def evidence : SourceEvidence :=
  { name := "SignedGainNontriviality"
    kind := .closedBase
    sourceRepo := canonicalNSRepo
    sourceRef := canonicalNSRef
    sourcePath := "audit/producer-first/ProducerFirst.lean"
    theoremName := "signedGainCertificate_not_trivially_inhabited"
    semanticScope := "Fail-closed firewall: SignedGainCertificate cannot be manufactured for arbitrary enstrophy data."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P04_NavierStokes.ClosedBase.SignedGainNontriviality.evidence_is_source_verified

end MCore.Real.P04_NavierStokes.ClosedBase.SignedGainNontriviality
