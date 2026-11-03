import MCore.Real.P02RejectionImageEscape

namespace MCore
namespace Real
namespace P02RejectionImageOrbit

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02SemanticSelfSubstitution
open P02RejectionImageEscape

def rejectIter
    (M : PolyDTMCandidate) :
    Nat → BitString → BitString
  | 0, x => x
  | n + 1, x => rejectCode M (rejectIter M n x)

@[simp] theorem rejectIter_zero
    (M : PolyDTMCandidate) (x : BitString) :
    rejectIter M 0 x = x := rfl

@[simp] theorem rejectIter_succ
    (M : PolyDTMCandidate) (n : Nat) (x : BitString) :
    rejectIter M (n + 1) x =
      rejectCode M (rejectIter M n x) := rfl

theorem globalFlip_twoStep_preserves
    (M : PolyDTMCandidate)
    (hFlip :
      ∀ x : BitString,
        observedBit M (rejectCode M x) = !(observedBit M x)) :
    ∀ x : BitString,
      observedBit M (rejectCode M (rejectCode M x)) =
        observedBit M x := by
  intro x
  have h1 := hFlip x
  have h2 := hFlip (rejectCode M x)
  cases hx : observedBit M x <;>
    cases hy : observedBit M (rejectCode M x) <;>
    cases hz : observedBit M (rejectCode M (rejectCode M x)) <;>
    simp_all

theorem correctOnRejectImage_twoStep_preserves
    (M : PolyDTMCandidate)
    (hTotal : ∀ y : BitString, OwnClockHalts M y)
    (hCorrect :
      ∀ x : BitString,
        M.CorrectAt
          (SATBits circuitBitEncoding)
          (rejectCode M x)) :
    ∀ x : BitString,
      observedBit M (rejectCode M (rejectCode M x)) =
        observedBit M x := by
  have hFlip :=
    (totalClock_globalFlip_iff_correctOnRejectImage M hTotal).mpr hCorrect
  exact globalFlip_twoStep_preserves M hFlip

theorem globalFlip_oddSemanticRecurrence_impossible
    (M : PolyDTMCandidate)
    (hFlip :
      ∀ x : BitString,
        observedBit M (rejectCode M x) = !(observedBit M x))
    (x : BitString)
    (hRec :
      observedBit M (rejectCode M x) = observedBit M x) :
    False := by
  have h := hFlip x
  cases hx : observedBit M x <;>
    cases hy : observedBit M (rejectCode M x) <;>
    simp_all

/-- Exact missing orbit obstruction: every total-clock machine has at least one
source whose observed bit recurs after one rejectCode step. -/
def RejectImageOddSemanticRecurrence : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ y : BitString, OwnClockHalts M y) →
      ∃ x : BitString,
        observedBit M (rejectCode M x) = observedBit M x

theorem oddSemanticRecurrence_iff_runCollapse :
    RejectImageOddSemanticRecurrence ↔ RejectCodeRunCollapse := by
  rfl

theorem oddSemanticRecurrence_implies_escape :
    RejectImageOddSemanticRecurrence →
      RejectImageEscape := by
  intro H
  exact rejectImageEscape_iff_totalClockAntiAlternation.mpr
    (rejectCodeRunCollapse_implies_antiAlternation
      (oddSemanticRecurrence_iff_runCollapse.mp H))


/--
Exact terminal reduction: the compressed terminal endpoint is inhabited
exactly when the one-step semantic recurrence exists. This introduces no new
parameter family; it identifies the material content of the endpoint.
-/
theorem terminalEndpoint_iff_oddSemanticRecurrence :
    P02RejectionImageEscape.Endpoint ↔ RejectImageOddSemanticRecurrence := by
  change RejectImageEscape ↔ RejectImageOddSemanticRecurrence
  constructor
  · intro hEscape
    have hAnti :
        TotalClockAntiAlternation :=
      (rejectImageEscape_iff_totalClockAntiAlternation.mp hEscape)
    have hCollision :
        TotalClockSemanticCollision :=
      (totalClockCollision_iff_antiAlternation.mpr hAnti)
    have hRun :
        RejectCodeRunCollapse :=
      (rejectCodeRunCollapse_iff_totalClockSemanticCollision.mpr hCollision)
    exact oddSemanticRecurrence_iff_runCollapse.mpr hRun
  · intro hRec
    exact oddSemanticRecurrence_implies_escape hRec

#print axioms MCore.Real.P02RejectionImageOrbit.terminalEndpoint_iff_oddSemanticRecurrence

#print axioms MCore.Real.P02RejectionImageOrbit.globalFlip_twoStep_preserves
#print axioms MCore.Real.P02RejectionImageOrbit.correctOnRejectImage_twoStep_preserves
#print axioms MCore.Real.P02RejectionImageOrbit.globalFlip_oddSemanticRecurrence_impossible
#print axioms MCore.Real.P02RejectionImageOrbit.oddSemanticRecurrence_implies_escape

end P02RejectionImageOrbit
end Real
end MCore
