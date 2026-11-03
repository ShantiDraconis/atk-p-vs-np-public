import MCore.Real.PNPPromotedByMaterial
import MCore.Real.P02UniversalFailureMinCut
import MCore.Real.P02CandidateCodeFixedPointCounterprobe

namespace MCore
namespace Real
namespace PNPMaterialLowerBoundFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPPromotedByMaterial
open P02UniversalFailureMinCut
open P02CandidateCodeFixedPointCounterprobe
open P02RejectionImageEscape

/-- The legacy candidate-code fixed-point route is refuted and is permanently
    excluded from the promoted-by-material producer path. -/
theorem legacy_candidate_fixed_point_route_refuted :
    ¬ P02DiagonalNoShortcut.CandidateCodeSemanticFixedPoint := by
  exact candidateCodeSemanticFixedPoint_refuted

/-- The existing universal-counterexample min-cut and the new material
    lower-bound producer carry the same candidate-indexed mathematical data. -/
def toUniversalCounterexampleProducer
    (P : CanonicalSATLowerBoundProducer) :
    UniversalCounterexampleProducer where
  counterexample := P.counterexample
  failure := by
    intro candidate
    exact
      (failureMode_iff_not_correctAt
        candidate (P.counterexample candidate)).mpr
        (P.fails candidate)

def fromUniversalCounterexampleProducer
    (P : UniversalCounterexampleProducer) :
    CanonicalSATLowerBoundProducer where
  counterexample := P.counterexample
  fails := by
    intro candidate
    exact
      (failureMode_iff_not_correctAt
        candidate (P.counterexample candidate)).mp
        (P.failure candidate)

theorem lowerBoundProducer_iff_universalCounterexampleProducer :
    Nonempty CanonicalSATLowerBoundProducer ↔
      Nonempty UniversalCounterexampleProducer := by
  constructor
  · rintro ⟨P⟩
    exact ⟨toUniversalCounterexampleProducer P⟩
  · rintro ⟨P⟩
    exact ⟨fromUniversalCounterexampleProducer P⟩

/-- Exact remaining mathematical frontier after the SAT-in-NP side is closed. -/
def ExactRemainingMaterialGap : Prop :=
  Nonempty CanonicalSATLowerBoundProducer

theorem exactRemainingGap_iff_universalFailure :
    ExactRemainingMaterialGap ↔
      UniversalFailure CanonicalSATBits := by
  calc
    ExactRemainingMaterialGap
        ↔ Nonempty UniversalCounterexampleProducer := by
            exact lowerBoundProducer_iff_universalCounterexampleProducer
    _ ↔ UniversalFailure P02UniversalFailureMinCut.CanonicalSAT := by
          exact producer_iff_universal_failure
    _ ↔ UniversalFailure CanonicalSATBits := by
          simpa [P02UniversalFailureMinCut.CanonicalSAT,
            PNPMaterialInhabitant.CanonicalSATBits]

theorem exactRemainingGap_closes_promoted_material
    (h : ExactRemainingMaterialGap) :
    MaterialPromotionTarget := by
  rcases h with ⟨P⟩
  exact ⟨{ lowerBound := P }⟩

theorem exactRemainingGap_closes_PneqNP
    (h : ExactRemainingMaterialGap) :
    PneqNP := by
  exact materialPromotionTarget_closes_PneqNP
    (exactRemainingGap_closes_promoted_material h)

#print axioms MCore.Real.PNPMaterialLowerBoundFrontier.legacy_candidate_fixed_point_route_refuted
#print axioms MCore.Real.PNPMaterialLowerBoundFrontier.toUniversalCounterexampleProducer
#print axioms MCore.Real.PNPMaterialLowerBoundFrontier.fromUniversalCounterexampleProducer
#print axioms MCore.Real.PNPMaterialLowerBoundFrontier.lowerBoundProducer_iff_universalCounterexampleProducer
#print axioms MCore.Real.PNPMaterialLowerBoundFrontier.exactRemainingGap_iff_universalFailure
#print axioms MCore.Real.PNPMaterialLowerBoundFrontier.exactRemainingGap_closes_PneqNP

end PNPMaterialLowerBoundFrontier
end Real
end MCore
