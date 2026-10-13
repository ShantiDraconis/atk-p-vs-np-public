import MCore.Real.P01FinalCertificate
import MCore.Real.P02G21G22Attack
import MCore.Real.CookNormalizedG3Contract
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace FinalExternalTwoGap

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open CanonicalSATNTMAttack
open P01FinalCertificate
open P02TerminalFrontier
open P02G21G22Attack
open CookNormalizedG3Contract
open FinalExternalCertificate
open FailProofAllGaps
open OfficialModel

/-- The final external lane has exactly two remaining mathematical producers:
P01 HARD and the pointwise G2.1 lower-bound producer. G3 is supplied by the
already-certified normalized external contract. -/
def FinalExternalTwoGap : Prop :=
  P01ConstructionGap ∧ G21Pointwise

/-- The two terminal producers imply the repository's exact FinalExternalGap.
This theorem remains in Prop, so no computational witness is extracted from
Nonempty merely for packaging. -/
theorem final_external_gap_of_two_gap
    (h : FinalExternalTwoGap) :
    FinalExternalGap := by
  rcases h with ⟨hP01, hG21⟩
  have hG1 : SATInNPGap circuitBitEncoding := by
    exact construction_closes_p01 hP01
  have hP02 : P02Target :=
    g21_pointwise_iff_p02_target.mp hG21
  rcases hP02 with ⟨G⟩
  exact
    ⟨{ g1 := hG1
       g2 := G
       g3 := cookNormalizedExternalContract }⟩

/-- Once the two terminal producers are closed, the existing external
certificate pipeline closes with no additional mathematical producer. -/
theorem final_external_two_gap_closes
    (h : FinalExternalTwoGap) :
    ∃ S : OfficialModelSelection,
      OfficialPneqNP S.model.P S.model.NP := by
  exact final_external_gap_closes
    (final_external_gap_of_two_gap h)

#print axioms MCore.Real.FinalExternalTwoGap.final_external_gap_of_two_gap
#print axioms MCore.Real.FinalExternalTwoGap.final_external_two_gap_closes

end FinalExternalTwoGap
end Real
end MCore
