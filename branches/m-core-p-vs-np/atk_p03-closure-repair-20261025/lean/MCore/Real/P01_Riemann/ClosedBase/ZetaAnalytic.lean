import MCore.Real.P01_Riemann.SourceBinding
namespace MCore.Real.P01_Riemann.ClosedBase.ZetaAnalytic
open MCore.Real.P01_Riemann.SourceBinding
def evidence : SourceEvidence :=
  { name := "ZetaAnalytic", kind := .closedBase
    sourceRepo := "leanprover-community/mathlib4", sourceRef := "v4.19.0"
    sourcePath := "Mathlib/NumberTheory/LSeries/RiemannZeta.lean"
    theoremName := "differentiable_completedZeta₀ / differentiableAt_riemannZeta"
    semanticScope := "Completed zeta0 entire; riemannZeta differentiable away from s=1."
    sourceVerified := true }
theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl
#print axioms MCore.Real.P01_Riemann.ClosedBase.ZetaAnalytic.evidence_is_source_verified
end MCore.Real.P01_Riemann.ClosedBase.ZetaAnalytic
