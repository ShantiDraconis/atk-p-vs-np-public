import MCore.Real.P01_Riemann.SourceBinding
namespace MCore.Real.P01_Riemann.ClosedBase.ZetaFunctionalEquation
open MCore.Real.P01_Riemann.SourceBinding
def evidence : SourceEvidence :=
  { name := "ZetaFunctionalEquation", kind := .closedBase
    sourceRepo := "leanprover-community/mathlib4", sourceRef := "v4.19.0"
    sourcePath := "Mathlib/NumberTheory/LSeries/RiemannZeta.lean"
    theoremName := "completedRiemannZeta_one_sub / completedRiemannZeta₀_one_sub"
    semanticScope := "Completed-zeta reflection functional equation."
    sourceVerified := true }
theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl
#print axioms MCore.Real.P01_Riemann.ClosedBase.ZetaFunctionalEquation.evidence_is_source_verified
end MCore.Real.P01_Riemann.ClosedBase.ZetaFunctionalEquation
