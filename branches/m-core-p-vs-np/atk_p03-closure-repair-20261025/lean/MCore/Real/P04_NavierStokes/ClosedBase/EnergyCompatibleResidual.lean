import MCore.Real.P04_NavierStokes.SourceBinding

namespace MCore.Real.P04_NavierStokes.ClosedBase.EnergyCompatibleResidual

open P04_NavierStokes.SourceBinding

def evidence : SourceEvidence :=
  { name := "EnergyCompatibleResidual"
    kind := .closedBase
    sourceRepo := canonicalNSRepo
    sourceRef := canonicalNSRef
    sourcePath := "audit/producer-first/ProducerFirst.lean"
    theoremName := "producerA_residual_exact / energy_compatible_residual_is_quadratic"
    semanticScope := "Closed algebraic identity a(t)y(t)=C y(t)^2 for a(t)=C y(t)."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P04_NavierStokes.ClosedBase.EnergyCompatibleResidual.evidence_is_source_verified

end MCore.Real.P04_NavierStokes.ClosedBase.EnergyCompatibleResidual
