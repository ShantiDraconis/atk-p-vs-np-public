import P02.LANE4.OPEN_MATH.BehavioralAlignment
import P02.LANE4.OPEN_MATH.FuelCounterexample
import MCore.Real.CanonicalFinalProof

namespace P02
namespace LANE4
namespace OPEN_MATH
namespace SameBehaviorFromPolyBound

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.P02TotalCandidateKleeneReduction
open BehavioralAlignment

/-- A tiny polynomially bounded clock that is not monotone.
This shows that PolynomialTimeBound is only an upper-bound property. -/
def descendingClock : TimeBound :=
  fun n => if n = 0 then 1 else 0

theorem descendingClock_poly :
    PolynomialTimeBound descendingClock := by
  refine ⟨1, 0, ?_⟩
  intro n
  by_cases h : n = 0
  · subst n
    simp [descendingClock]
  · simp [descendingClock, h]

theorem descendingClock_not_monotone :
    ¬ Monotone descendingClock := by
  intro hmono
  have h := hmono (show 0 ≤ 1 by omega)
  simp [descendingClock] at h

/-- Therefore polynomial boundedness alone cannot transport a size inequality
into a fuel inequality. -/
theorem polynomialTimeBound_does_not_imply_monotone :
    ¬ (∀ T : TimeBound,
        PolynomialTimeBound T → Monotone T) := by
  intro h
  exact descendingClock_not_monotone
    (h descendingClock descendingClock_poly)

/-- A concrete one-step size increase on which the descending clock loses fuel. -/
theorem size_growth_does_not_force_fuel_growth :
    0 ≤ 1 ∧ descendingClock 1 < descendingClock 0 := by
  simp [descendingClock]

/-- Exact resource statement that a reduction output is at least as long as
its source.  The current repository does not derive this merely from R5
injectivity; it is kept as an independent producer. -/
def ReductionSizeNondecreaseProducer : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString),
    x.length ≤ (reduceM M hTotal x).length

/-- Exact clock regularity needed to turn size nondecrease into fuel dominance. -/
def DeclaredClockMonotonicityProducer : Prop :=
  ∀ M : PolyDTMCandidate, Monotone M.timeBound

/-- Size growth plus a monotone declared clock yields the resource side of the
fuel route, but nothing semantic yet. -/
theorem size_and_clock_monotone_give_fuel
    (S : ReductionSizeNondecreaseProducer)
    (C : DeclaredClockMonotonicityProducer) :
    FuelWitnessProducer := by
  intro M hTotal
  refine ⟨[], ?_⟩
  unfold FuelDominatesSourceSimulation
  exact C M (S M hTotal [])

/-- Pointwise version, useful for alternative witness selectors. -/
theorem pointwise_size_and_clock_monotone_give_fuel
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (hSize : x.length ≤ (reduceM M hTotal x).length)
    (hMono : Monotone M.timeBound) :
    FuelDominatesSourceSimulation M hTotal x := by
  unfold FuelDominatesSourceSimulation
  exact hMono hSize

/-- Full proposed Poly+size route.  It still requires the genuine semantic
transport theorem; arithmetic growth does not manufacture SameBehaviorAt. -/
structure PolySizeBehaviorRouteProducer where
  size_nondecrease : ReductionSizeNondecreaseProducer
  clock_monotone : DeclaredClockMonotonicityProducer
  semantic_transport : FuelToBehaviorBridge

theorem poly_size_route_closes_T10
    (P : PolySizeBehaviorRouteProducer) :
    TotalBehavioralAlignmentProducer := by
  apply fuel_route_closes_behavioral_alignment
  · exact size_and_clock_monotone_give_fuel
      P.size_nondecrease P.clock_monotone
  · exact P.semantic_transport

/-- The actual PolyDTMCandidate field supplies only PolynomialTimeBound, not
DeclaredClockMonotonicityProducer.  This alias makes the type distinction
visible to audit tooling. -/
def CandidateProvidesPolynomialUpperBound : Prop :=
  ∀ M : PolyDTMCandidate,
    PolynomialTimeBound M.timeBound

theorem candidate_provides_polynomial_upper_bound :
    CandidateProvidesPolynomialUpperBound := by
  intro M
  exact M.time_poly

/-- The currently available candidate field cannot by pure logic be promoted
to the monotonicity producer used above. -/
def MissingClockRegularity : Prop :=
  DeclaredClockMonotonicityProducer

/-- Even after resource dominance is established, the exact semantic gap is
still FuelToBehaviorBridge. -/
def MissingSemanticTransport : Prop :=
  FuelToBehaviorBridge

#print axioms P02.LANE4.OPEN_MATH.SameBehaviorFromPolyBound.descendingClock_poly
#print axioms P02.LANE4.OPEN_MATH.SameBehaviorFromPolyBound.descendingClock_not_monotone
#print axioms P02.LANE4.OPEN_MATH.SameBehaviorFromPolyBound.polynomialTimeBound_does_not_imply_monotone
#print axioms P02.LANE4.OPEN_MATH.SameBehaviorFromPolyBound.size_growth_does_not_force_fuel_growth
#print axioms P02.LANE4.OPEN_MATH.SameBehaviorFromPolyBound.size_and_clock_monotone_give_fuel
#print axioms P02.LANE4.OPEN_MATH.SameBehaviorFromPolyBound.poly_size_route_closes_T10
#print axioms P02.LANE4.OPEN_MATH.SameBehaviorFromPolyBound.candidate_provides_polynomial_upper_bound

end SameBehaviorFromPolyBound
end OPEN_MATH
end LANE4
end P02
