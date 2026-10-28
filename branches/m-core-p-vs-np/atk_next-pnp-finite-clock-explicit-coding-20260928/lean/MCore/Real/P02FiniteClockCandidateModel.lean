import MCore.Real.P02CanonicalNormalization

namespace MCore
namespace Real
namespace P02FiniteClockCandidateModel

open CanonicalFinalProof
open P02CanonicalNormalization

structure FiniteClockDTMCandidate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  coefficient : Nat
  exponent : Nat

def FiniteClockDTMCandidate.toPoly
    (C : FiniteClockDTMCandidate) : PolyDTMCandidate :=
  { stateCount := C.stateCount
    machine := C.machine
    blank_none := C.blank_none
    accepting := C.accepting
    timeBound := canonicalTimeBound C.coefficient C.exponent
    time_poly := canonicalTimeBound_poly C.coefficient C.exponent }

def ofCandidateClock
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat) :
    FiniteClockDTMCandidate :=
  { stateCount := M.stateCount
    machine := M.machine
    blank_none := M.blank_none
    accepting := M.accepting
    coefficient := coefficient
    exponent := exponent }

@[simp] theorem ofCandidateClock_toPoly
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat) :
    (ofCandidateClock M coefficient exponent).toPoly =
      normalizedCandidate M coefficient exponent := rfl

def FiniteClockUniversalFailure (L : BitLanguage) : Prop :=
  ∀ C : FiniteClockDTMCandidate,
    ∃ x : BitString, ¬ C.toPoly.CorrectAt L x

theorem finiteClockUniversalFailure_implies_UniversalFailure
    {L : BitLanguage}
    (h : FiniteClockUniversalFailure L) :
    UniversalFailure L := by
  intro M
  rcases M.time_poly with ⟨coefficient, exponent, hbound⟩
  let C := ofCandidateClock M coefficient exponent
  rcases h C with ⟨x, hbad⟩
  refine ⟨x, ?_⟩
  intro hcorrect
  apply hbad
  simpa [C] using
    (normalizedCandidate_correctAt
      M coefficient exponent hbound L x hcorrect)

theorem finiteClockUniversalFailure_implies_not_in_p
    {L : BitLanguage}
    (h : FiniteClockUniversalFailure L) :
    ¬ InP L :=
  universal_failure_implies_not_in_p
    (finiteClockUniversalFailure_implies_UniversalFailure h)

#print axioms MCore.Real.P02FiniteClockCandidateModel.finiteClockUniversalFailure_implies_UniversalFailure
#print axioms MCore.Real.P02FiniteClockCandidateModel.finiteClockUniversalFailure_implies_not_in_p

end P02FiniteClockCandidateModel
end Real
end MCore
