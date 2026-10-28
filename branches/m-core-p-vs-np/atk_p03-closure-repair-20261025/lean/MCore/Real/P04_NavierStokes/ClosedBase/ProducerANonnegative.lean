import MCore.Real.P04_NavierStokes.SourceBinding

namespace MCore.Real.P04_NavierStokes.ClosedBase.ProducerANonnegative

open P04_NavierStokes.SourceBinding

def evidence : SourceEvidence :=
  { name := "ProducerANonnegative"
    kind := .closedBase
    sourceRepo := canonicalNSRepo
    sourceRef := canonicalNSRef
    sourcePath := "audit/producer-first/ProducerFirst.lean"
    theoremName := "producerA_nonnegative"
    semanticScope := "Closed scalar lower-order coefficient nonnegativity inside the producer-first reduction."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P04_NavierStokes.ClosedBase.ProducerANonnegative.evidence_is_source_verified

end MCore.Real.P04_NavierStokes.ClosedBase.ProducerANonnegative
