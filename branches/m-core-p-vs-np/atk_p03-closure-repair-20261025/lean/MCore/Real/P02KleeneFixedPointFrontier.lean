import MCore.Real.P02RejectionImageOrbit
import MCore.Real.P02ActiveBridgeClosure

namespace MCore
namespace Real
namespace P02KleeneFixedPointFrontier

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02SemanticSelfSubstitution
open P02RejectionImageEscape
open P02RejectionImageOrbit

/-- The exact semantic fixed-point statement suggested by the diagonal route. -/
def KleeneStyleSemanticFixedPoint : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ y : BitString, OwnClockHalts M y) →
      ∃ x : BitString,
        observedBit M (rejectCode M x) = observedBit M x

/-- This is definitionally the existing one-step semantic recurrence target. -/
theorem kleeneStyle_iff_oddSemanticRecurrence :
    KleeneStyleSemanticFixedPoint ↔ RejectImageOddSemanticRecurrence := by
  rfl

/-- Therefore the proposed Kleene-style fixed point is not a smaller bridge:
it is exactly equivalent to the current RejectImageEscape OPEN_MATH. -/
theorem kleeneStyle_iff_rejectImageEscape :
    KleeneStyleSemanticFixedPoint ↔ RejectImageEscape := by
  calc
    KleeneStyleSemanticFixedPoint
        ↔ RejectCodeRunCollapse := by
            exact (kleeneStyle_iff_oddSemanticRecurrence.trans
              oddSemanticRecurrence_iff_runCollapse)
    _ ↔ TotalClockSemanticCollision :=
          rejectCodeRunCollapse_iff_totalClockSemanticCollision
    _ ↔ TotalClockAntiAlternation :=
          totalClockCollision_iff_antiAlternation
    _ ↔ RejectImageEscape :=
          rejectImageEscape_iff_totalClockAntiAlternation.symm

/-- A witness-producing version for a fixed M is sufficient once it is uniform
over all total-clock candidates; no machine-code serializer is assumed here. -/
theorem kleeneStyle_closes_pneqnp
    (h : KleeneStyleSemanticFixedPoint) :
    PneqNP := by
  exact P02ActiveBridgeClosure.rejectImageEscape_closes_pneqnp
    (kleeneStyle_iff_rejectImageEscape.mp h)

#print axioms MCore.Real.P02KleeneFixedPointFrontier.kleeneStyle_iff_rejectImageEscape
#print axioms MCore.Real.P02KleeneFixedPointFrontier.kleeneStyle_closes_pneqnp

end P02KleeneFixedPointFrontier
end Real
end MCore
