import MCore.Real.P02G21G22Attack
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace P02DirectExternalPromotion

open CanonicalSATBoundary
open CanonicalCircuitBits
open P02TerminalFrontier
open P02G21G22Attack
open FinalExternalCertificate
open FailProofAllGaps

/-- Direct external payload assembly from the minimal live G21 target.
No D3/DiagonalFamily hypothesis is required for this wiring step. -/
noncomputable def assembleFinalExternalFromG21
    (hP01 : SATInNPGap circuitBitEncoding)
    (hG21 : G21Pointwise)
    (hG3 : G3ModelMatch.G3ExternalContract) :
    FinalExternalInputs := by
  have hP02 : P02Target :=
    g21_pointwise_iff_p02_target.mp hG21
  exact
    { g1 := hP01
      g2 := Classical.choice hP02
      g3 := hG3 }

/-- Minimal direct final-external composition. -/
theorem P01_G21_G3_to_external_final
    (hP01 : SATInNPGap circuitBitEncoding)
    (hG21 : G21Pointwise)
    (hG3 : G3ModelMatch.G3ExternalContract) :
    OfficialPneqNP hG3.selection.model.P hG3.selection.model.NP := by
  exact final_external_certificate
    (assembleFinalExternalFromG21 hP01 hG21 hG3)

/-- The same three producers inhabit the repository's FinalExternalGap. -/
noncomputable theorem P01_G21_G3_to_FinalExternalGap
    (hP01 : SATInNPGap circuitBitEncoding)
    (hG21 : G21Pointwise)
    (hG3 : G3ModelMatch.G3ExternalContract) :
    FinalExternalGap :=
  ⟨assembleFinalExternalFromG21 hP01 hG21 hG3⟩

/-- Internal separation uses only P01 + G21; G3 is purely the external-model
promotion layer. -/
theorem P01_G21_to_internal_final
    (hP01 : SATInNPGap circuitBitEncoding)
    (hG21 : G21Pointwise) :
    PneqNP :=
  p01_g21_closes_internal hP01 hG21

#print axioms MCore.Real.P02DirectExternalPromotion.assembleFinalExternalFromG21
#print axioms MCore.Real.P02DirectExternalPromotion.P01_G21_G3_to_external_final
#print axioms MCore.Real.P02DirectExternalPromotion.P01_G21_G3_to_FinalExternalGap
#print axioms MCore.Real.P02DirectExternalPromotion.P01_G21_to_internal_final

end P02DirectExternalPromotion
end Real
end MCore
