import MCore.Real.P02ExplicitClockNormalForm

namespace MCore
namespace Real
namespace P02FiniteDescriptorReduction

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02ExplicitClockNormalForm

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

/-- Finite-description-shaped deterministic candidate.  The runtime bound is
stored by two natural numbers, not by an arbitrary function field. -/
structure FiniteDTMDescriptor where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  coefficient : Nat
  exponent : Nat

def monomialTimeBound
    (coefficient exponent : Nat) : TimeBound :=
  fun n => coefficient * (n + 1) ^ exponent

theorem monomialTimeBound_poly
    (coefficient exponent : Nat) :
    PolynomialTimeBound (monomialTimeBound coefficient exponent) := by
  refine ⟨coefficient, exponent, ?_⟩
  intro n
  exact Nat.le_refl _

def FiniteDTMDescriptor.toCandidate
    (D : FiniteDTMDescriptor) :
    PolyDTMCandidate :=
  { stateCount := D.stateCount
    machine := D.machine
    blank_none := D.blank_none
    accepting := D.accepting
    timeBound := monomialTimeBound D.coefficient D.exponent
    time_poly := monomialTimeBound_poly D.coefficient D.exponent }

noncomputable def descriptorOf
    (M : PolyDTMCandidate) :
    FiniteDTMDescriptor :=
  { stateCount := M.stateCount
    machine := M.machine
    blank_none := M.blank_none
    accepting := M.accepting
    coefficient := (clockWitness M).coefficient
    exponent := (clockWitness M).exponent }

theorem descriptorOf_toCandidate
    (M : PolyDTMCandidate) :
    (descriptorOf M).toCandidate =
      normalizedCandidate M := by
  rfl

/-- Exact lower-bound target restricted to finite descriptors. -/
def FiniteDescriptorFailure : Prop :=
  ∀ D : FiniteDTMDescriptor,
    ∃ x : BitString,
      ¬ D.toCandidate.CorrectAt SATTarget x

theorem finiteDescriptorFailure_implies_universalFailure
    (H : FiniteDescriptorFailure) :
    UniversalFailure SATTarget := by
  intro M
  rcases H (descriptorOf M) with ⟨x, hBad⟩
  refine ⟨x, ?_⟩
  apply original_failure_of_normalized_failure M SATTarget x
  simpa [descriptorOf_toCandidate] using hBad

theorem universalFailure_implies_finiteDescriptorFailure
    (H : UniversalFailure SATTarget) :
    FiniteDescriptorFailure := by
  intro D
  exact H D.toCandidate

theorem finiteDescriptorFailure_iff_universalFailure :
    FiniteDescriptorFailure ↔ UniversalFailure SATTarget := by
  constructor
  · exact finiteDescriptorFailure_implies_universalFailure
  · exact universalFailure_implies_finiteDescriptorFailure

/-- Pointwise failure on finite descriptors is already sufficient for the
internal endpoint, via the frozen P01 SAT-in-NP side. -/
theorem finiteDescriptorFailure_closes_internal_endpoint
    (H : FiniteDescriptorFailure) :
    PneqNP :=
  producer_closes_internal_endpoint
    (producerOfUniversalFailure
      (finiteDescriptorFailure_implies_universalFailure H))

#print axioms MCore.Real.P02FiniteDescriptorReduction.monomialTimeBound_poly
#print axioms MCore.Real.P02FiniteDescriptorReduction.descriptorOf_toCandidate
#print axioms MCore.Real.P02FiniteDescriptorReduction.finiteDescriptorFailure_iff_universalFailure
#print axioms MCore.Real.P02FiniteDescriptorReduction.finiteDescriptorFailure_closes_internal_endpoint

end P02FiniteDescriptorReduction
end Real
end MCore
