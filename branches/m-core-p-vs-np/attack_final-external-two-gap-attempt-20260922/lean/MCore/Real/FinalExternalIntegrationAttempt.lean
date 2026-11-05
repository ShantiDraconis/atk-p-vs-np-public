import MCore.Real.FinalExternalTwoGap
import MCore.Real.P01MachineConstructionAttempt
import MCore.Real.G21PointwiseAttempt

namespace MCore
namespace Real
namespace FinalExternalIntegrationAttempt

open P01FinalCertificate
open P02G21G22Attack
open FinalExternalCertificate
open FinalExternalTwoGap

/-- Conditional integration only: it introduces no new mathematical producer. -/
def finalExternalGap
    (hP01 : P01ConstructionGap)
    (hG21 : G21Pointwise) :
    FinalExternalGap :=
  final_external_gap_of_two_gap ⟨hP01, hG21⟩

/--
Fail-closed issuance state. These values must remain unchanged while either
exploratory endpoint definition still contains sorry.
-/
def FINAL_ROOT : Option FinalExternalInputs := none
def FINAL_EXTERNAL_ISSUED : Bool := false
def FINAL_PROOF : Nat := 0

theorem finalExternalGap_closes_if_two_gaps_close
    (hP01 : P01ConstructionGap)
    (hG21 : G21Pointwise) :
    ∃ S : OfficialModel.OfficialModelSelection,
      FailProofAllGaps.OfficialPneqNP S.model.P S.model.NP := by
  exact final_external_two_gap_closes ⟨hP01, hG21⟩

#print axioms MCore.Real.FinalExternalIntegrationAttempt.finalExternalGap_closes_if_two_gaps_close

end FinalExternalIntegrationAttempt
end Real
end MCore
