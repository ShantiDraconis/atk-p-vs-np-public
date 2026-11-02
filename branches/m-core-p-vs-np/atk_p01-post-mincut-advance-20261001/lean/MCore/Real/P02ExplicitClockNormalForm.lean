import MCore.Real.P02UniversalFailureMinCut
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02ExplicitClockNormalForm

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02UniversalFailureMinCut
open MachineRunLemmas

/-- One explicit polynomial clock witness for a hardened deterministic candidate. -/
structure PolynomialClockWitness (candidate : PolyDTMCandidate) where
  coefficient : Nat
  exponent : Nat
  dominates :
    ∀ n : Nat,
      candidate.timeBound n ≤ coefficient * (n + 1) ^ exponent

noncomputable def clockCoefficient
    (candidate : PolyDTMCandidate) : Nat :=
  Classical.choose candidate.time_poly

noncomputable def clockExponent
    (candidate : PolyDTMCandidate) : Nat :=
  Classical.choose (Classical.choose_spec candidate.time_poly)

theorem clockDominates
    (candidate : PolyDTMCandidate) :
    ∀ n : Nat,
      candidate.timeBound n ≤
        clockCoefficient candidate * (n + 1) ^ clockExponent candidate := by
  exact Classical.choose_spec (Classical.choose_spec candidate.time_poly)

noncomputable def clockWitness
    (candidate : PolyDTMCandidate) :
    PolynomialClockWitness candidate :=
  { coefficient := clockCoefficient candidate
    exponent := clockExponent candidate
    dominates := clockDominates candidate }

noncomputable def polynomialEnvelope
    (candidate : PolyDTMCandidate) : TimeBound :=
  let W := clockWitness candidate
  fun n => W.coefficient * (n + 1) ^ W.exponent

theorem timeBound_le_polynomialEnvelope
    (candidate : PolyDTMCandidate)
    (n : Nat) :
    candidate.timeBound n ≤ polynomialEnvelope candidate n := by
  classical
  exact (clockWitness candidate).dominates n

theorem polynomialEnvelope_poly
    (candidate : PolyDTMCandidate) :
    PolynomialTimeBound (polynomialEnvelope candidate) := by
  classical
  refine ⟨(clockWitness candidate).coefficient,
    (clockWitness candidate).exponent, ?_⟩
  intro n
  exact Nat.le_refl _

/-- Same physical machine and accepting map, but run at an explicit monomial
envelope extracted from the candidate's polynomial-time certificate. -/
noncomputable def normalizedCandidate
    (candidate : PolyDTMCandidate) :
    PolyDTMCandidate :=
  { stateCount := candidate.stateCount
    machine := candidate.machine
    blank_none := candidate.blank_none
    accepting := candidate.accepting
    timeBound := polynomialEnvelope candidate
    time_poly := polynomialEnvelope_poly candidate }

/-- Once the original run has halted, increasing fuel to the explicit
polynomial envelope leaves the final configuration unchanged. -/
theorem run_at_envelope_eq_of_halts
    (candidate : PolyDTMCandidate)
    (x : BitString)
    (hHalt :
      candidate.machine.HaltsWithin
        (candidate.timeBound x.length)
        (initialTMConfig candidate.machine x)) :
    candidate.machine.run
        (polynomialEnvelope candidate x.length)
        (initialTMConfig candidate.machine x) =
      candidate.machine.run
        (candidate.timeBound x.length)
        (initialTMConfig candidate.machine x) := by
  apply run_to_larger_fuel_of_halt candidate.machine
    (initialTMConfig candidate.machine x)
    (candidate.machine.run
      (candidate.timeBound x.length)
      (initialTMConfig candidate.machine x))
    (timeBound_le_polynomialEnvelope candidate x.length)
  · rfl
  · exact hHalt

theorem normalized_correctAt_of_correctAt
    (candidate : PolyDTMCandidate)
    (language : BitLanguage)
    (x : BitString)
    (h : candidate.CorrectAt language x) :
    (normalizedCandidate candidate).CorrectAt language x := by
  classical
  rcases h with ⟨hHalt, hSem⟩
  constructor
  · exact haltsWithin_mono candidate.machine
      (initialTMConfig candidate.machine x)
      (timeBound_le_polynomialEnvelope candidate x.length)
      hHalt
  · change
      candidate.accepting
          (candidate.machine.run
            (polynomialEnvelope candidate x.length)
            (initialTMConfig candidate.machine x)).state = true ↔
        language x
    rw [run_at_envelope_eq_of_halts candidate x hHalt]
    exact hSem

/-- Therefore a concrete failure of the normalized explicit-clock candidate is
already a concrete failure of the original candidate. -/
theorem original_failure_of_normalized_failure
    (candidate : PolyDTMCandidate)
    (language : BitLanguage)
    (x : BitString)
    (hFail :
      ¬ (normalizedCandidate candidate).CorrectAt language x) :
    ¬ candidate.CorrectAt language x := by
  intro hCorrect
  exact hFail (normalized_correctAt_of_correctAt
    candidate language x hCorrect)

/-- Stronger, clock-explicit attack interface.  It is sufficient for the exact
P02 universal failure min-cut, without changing the target SAT language. -/
structure ExplicitClockCounterexampleProducer where
  counterexample : PolyDTMCandidate → BitString
  normalized_failure :
    ∀ candidate : PolyDTMCandidate,
      ¬ (normalizedCandidate candidate).CorrectAt
        CanonicalSAT (counterexample candidate)

def ExplicitClockCounterexampleProducer.toUniversal
    (P : ExplicitClockCounterexampleProducer) :
    UniversalCounterexampleProducer where
  counterexample := P.counterexample
  failure := by
    intro candidate
    apply (failureMode_iff_not_correctAt
      candidate (P.counterexample candidate)).mpr
    exact original_failure_of_normalized_failure
      candidate CanonicalSAT (P.counterexample candidate)
      (P.normalized_failure candidate)

theorem explicit_clock_producer_implies_universal_failure
    (P : ExplicitClockCounterexampleProducer) :
    UniversalFailure CanonicalSAT :=
  producer_implies_universal_failure P.toUniversal

theorem explicit_clock_producer_closes_internal_endpoint
    (P : ExplicitClockCounterexampleProducer) :
    PneqNP :=
  producer_closes_internal_endpoint P.toUniversal

#print axioms MCore.Real.P02ExplicitClockNormalForm.timeBound_le_polynomialEnvelope
#print axioms MCore.Real.P02ExplicitClockNormalForm.run_at_envelope_eq_of_halts
#print axioms MCore.Real.P02ExplicitClockNormalForm.normalized_correctAt_of_correctAt
#print axioms MCore.Real.P02ExplicitClockNormalForm.original_failure_of_normalized_failure
#print axioms MCore.Real.P02ExplicitClockNormalForm.explicit_clock_producer_implies_universal_failure

end P02ExplicitClockNormalForm
end Real
end MCore
