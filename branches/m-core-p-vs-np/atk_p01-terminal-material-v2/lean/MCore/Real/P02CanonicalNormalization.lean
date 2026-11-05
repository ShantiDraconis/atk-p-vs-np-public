import MCore.Real.CanonicalFinalProof
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02CanonicalNormalization

open CanonicalFinalProof

def canonicalTimeBound (coefficient exponent : Nat) : TimeBound :=
  fun n => coefficient * (n + 1) ^ exponent

theorem canonicalTimeBound_poly
    (coefficient exponent : Nat) :
    PolynomialTimeBound (canonicalTimeBound coefficient exponent) := by
  refine ⟨coefficient, exponent, ?_⟩
  intro n
  exact Nat.le_refl _

def normalizedCandidate
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat) :
    PolyDTMCandidate :=
  { stateCount := M.stateCount
    machine := M.machine
    blank_none := M.blank_none
    accepting := M.accepting
    timeBound := canonicalTimeBound coefficient exponent
    time_poly := canonicalTimeBound_poly coefficient exponent }

@[simp] theorem normalizedCandidate_machine
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat) :
    (normalizedCandidate M coefficient exponent).machine = M.machine := rfl

@[simp] theorem normalizedCandidate_accepting
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat) :
    (normalizedCandidate M coefficient exponent).accepting = M.accepting := rfl

@[simp] theorem normalizedCandidate_timeBound
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat) :
    (normalizedCandidate M coefficient exponent).timeBound =
      canonicalTimeBound coefficient exponent := rfl

/-- Increasing a deterministic candidate's clock after it has halted preserves
its final configuration and therefore preserves CorrectAt. -/
theorem normalizedCandidate_correctAt
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat)
    (hbound :
      ∀ n : Nat,
        M.timeBound n ≤ canonicalTimeBound coefficient exponent n)
    (L : BitLanguage)
    (x : BitString)
    (hcorrect : M.CorrectAt L x) :
    (normalizedCandidate M coefficient exponent).CorrectAt L x := by
  unfold PolyDTMCandidate.CorrectAt at hcorrect ⊢
  dsimp [normalizedCandidate]
  rcases hcorrect with ⟨hhalts, hsemantic⟩
  let config := initialTMConfig M.machine x
  let oldFuel := M.timeBound x.length
  let newFuel := canonicalTimeBound coefficient exponent x.length
  have hle : oldFuel ≤ newFuel := hbound x.length
  have hhaltsNew :
      M.machine.HaltsWithin newFuel config :=
    MachineRunLemmas.haltsWithin_mono
      M.machine config hle hhalts
  have hrun :
      M.machine.run newFuel config =
        M.machine.run oldFuel config := by
    exact
      MachineRunLemmas.run_to_larger_fuel_of_halt
        M.machine
        config
        (M.machine.run oldFuel config)
        hle
        rfl
        hhalts
  constructor
  · exact hhaltsNew
  · rw [hrun]
    exact hsemantic

/-- G2.0: every hardened polynomial-time DTM candidate has a representative
with an explicit monomial clock c*(n+1)^k, the same finite machine and accepting
predicate, and no loss of already-correct inputs.

This normalizes the arbitrary TimeBound field.  It does NOT by itself prove an
enumeration theorem for finite machine descriptions; that is a separate coding
step required only by enumeration-based attacks. -/
theorem canonical_normalization
    (M : PolyDTMCandidate) :
    ∃ coefficient exponent : Nat,
      (normalizedCandidate M coefficient exponent).machine = M.machine ∧
      (normalizedCandidate M coefficient exponent).accepting = M.accepting ∧
      (∀ L : BitLanguage,
        ∀ x : BitString,
          M.CorrectAt L x →
            (normalizedCandidate M coefficient exponent).CorrectAt L x) := by
  rcases M.time_poly with ⟨coefficient, exponent, hbound⟩
  refine ⟨coefficient, exponent, rfl, rfl, ?_⟩
  intro L x hcorrect
  exact normalizedCandidate_correctAt
    M coefficient exponent hbound L x hcorrect

#print axioms MCore.Real.P02CanonicalNormalization.canonicalTimeBound_poly
#print axioms MCore.Real.P02CanonicalNormalization.normalizedCandidate_correctAt
#print axioms MCore.Real.P02CanonicalNormalization.canonical_normalization

end P02CanonicalNormalization
end Real
end MCore
