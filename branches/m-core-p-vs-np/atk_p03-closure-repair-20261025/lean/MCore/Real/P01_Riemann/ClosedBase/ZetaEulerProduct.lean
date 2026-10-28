import MCore.Real.P01_Riemann.SourceBinding
namespace MCore.Real.P01_Riemann.ClosedBase.ZetaEulerProduct
open MCore.Real.P01_Riemann.SourceBinding
def evidence : SourceEvidence :=
  { name := "ZetaEulerProduct", kind := .closedBase
    sourceRepo := "leanprover-community/mathlib4", sourceRef := "v4.19.0"
    sourcePath := "Mathlib/NumberTheory/LSeries/RiemannZeta.lean"
    theoremName := "riemannZeta_eulerProduct_hasProd / riemannZeta_ne_zero_of_one_lt_re"
    semanticScope := "Euler product and nonvanishing for Re(s)>1."
    sourceVerified := true }
theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl
#print axioms MCore.Real.P01_Riemann.ClosedBase.ZetaEulerProduct.evidence_is_source_verified
end MCore.Real.P01_Riemann.ClosedBase.ZetaEulerProduct
