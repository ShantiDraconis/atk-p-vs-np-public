import MCore.Real.CanonicalFinalProof
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02CandidateNormalization

open CanonicalFinalProof
open MachineRunLemmas

/--
Replace the time bound of a deterministic polynomial-time candidate by one
explicit monomial bound extracted from its existing PolynomialTimeBound proof.

The finite machine, blank proof, and accepting predicate are unchanged.
This is a bound normalization theorem only; it does not by itself construct
an effective enumeration of PolyDTMCandidate.
-/
def normalizedCandidate
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat) :
    PolyDTMCandidate where
  stateCount := M.stateCount
  machine := M.machine
  blank_none := M.blank_none
  accepting := M.accepting
  timeBound := fun n => coefficient * (n + 1) ^ exponent
  time_poly := by
    refine ⟨coefficient, exponent, ?_⟩
    intro n
    exact Nat.le_refl _

@[simp] theorem normalizedCandidate_stateCount
    (M : PolyDTMCandidate)
    (c k : Nat) :
    (normalizedCandidate M c k).stateCount = M.stateCount := rfl

@[simp] theorem normalizedCandidate_machine
    (M : PolyDTMCandidate)
    (c k : Nat) :
    (normalizedCandidate M c k).machine = M.machine := rfl

@[simp] theorem normalizedCandidate_accepting
    (M : PolyDTMCandidate)
    (c k : Nat) :
    (normalizedCandidate M c k).accepting = M.accepting := rfl

@[simp] theorem normalizedCandidate_timeBound
    (M : PolyDTMCandidate)
    (c k n : Nat) :
    (normalizedCandidate M c k).timeBound n =
      c * (n + 1) ^ k := rfl

/--
Correctness at one input is preserved when the normalized explicit bound
dominates the original time bound.

The proof uses only deterministic run stability after a halting state:
once M has halted by its original fuel, extra fuel leaves the final
configuration unchanged.
-/
theorem correctAt_preserved_by_dominating_bound
    (M : PolyDTMCandidate)
    (c k : Nat)
    (hbound : ∀ n : Nat,
      M.timeBound n ≤ c * (n + 1) ^ k)
    (language : BitLanguage)
    (x : BitString)
    (hCorrect : M.CorrectAt language x) :
    (normalizedCandidate M c k).CorrectAt language x := by
  unfold PolyDTMCandidate.CorrectAt at hCorrect ⊢
  dsimp [normalizedCandidate] at *
  let config := initialTMConfig M.machine x
  change
    M.machine.HaltsWithin (M.timeBound x.length) config ∧
      (M.accepting
          (M.machine.run (M.timeBound x.length) config).state = true
        ↔ language x) at hCorrect
  change
    M.machine.HaltsWithin (c * (x.length + 1) ^ k) config ∧
      (M.accepting
          (M.machine.run (c * (x.length + 1) ^ k) config).state = true
        ↔ language x)
  rcases hCorrect with ⟨hhalt, hsem⟩
  have hle :
      M.timeBound x.length ≤ c * (x.length + 1) ^ k :=
    hbound x.length
  have hhalt' :
      M.machine.HaltsWithin (c * (x.length + 1) ^ k) config :=
    haltsWithin_mono M.machine config hle hhalt
  have hrun :
      M.machine.run (c * (x.length + 1) ^ k) config =
        M.machine.run (M.timeBound x.length) config := by
    exact run_to_larger_fuel_of_halt
      M.machine
      config
      (M.machine.run (M.timeBound x.length) config)
      hle
      rfl
      hhalt
  refine ⟨hhalt', ?_⟩
  rw [hrun]
  exact hsem

/--
G2.0 canonical normalization.

Every PolyDTMCandidate admits explicit polynomial constants whose canonical
normalized candidate uses exactly the same underlying machine data by
construction and preserves every pointwise CorrectAt fact.

No claim of effective enumerability is made here.  No diagonal witness,
SAT lower bound, FailureGenerator, or P != NP conclusion is produced here.
-/
theorem canonical_normalization :
    ∀ M : PolyDTMCandidate,
      ∃ coefficient exponent : Nat,
        (∀ n : Nat,
          M.timeBound n ≤ coefficient * (n + 1) ^ exponent) ∧
        (∀ language : BitLanguage,
          ∀ x : BitString,
            M.CorrectAt language x →
              (normalizedCandidate M coefficient exponent).CorrectAt
                language x) := by
  intro M
  rcases M.time_poly with ⟨coefficient, exponent, hbound⟩
  refine ⟨coefficient, exponent, hbound, ?_⟩
  intro language x hCorrect
  exact correctAt_preserved_by_dominating_bound
    M coefficient exponent hbound language x hCorrect

/--
A compact G2.0 certificate object.  Its candidate is definitionally the
canonical normalization of M at the stored polynomial constants.
-/
structure NormalizedCandidateWitness
    (M : PolyDTMCandidate) where
  coefficient : Nat
  exponent : Nat
  dominates :
    ∀ n : Nat,
      M.timeBound n ≤ coefficient * (n + 1) ^ exponent
  preserves_correctAt :
    ∀ language : BitLanguage,
      ∀ x : BitString,
        M.CorrectAt language x →
          (normalizedCandidate M coefficient exponent).CorrectAt language x

noncomputable def normalizationCoefficient
    (M : PolyDTMCandidate) : Nat :=
  Classical.choose M.time_poly

noncomputable def normalizationExponent
    (M : PolyDTMCandidate) : Nat :=
  Classical.choose (Classical.choose_spec M.time_poly)

theorem normalizationBound
    (M : PolyDTMCandidate) :
    ∀ n : Nat,
      M.timeBound n ≤
        normalizationCoefficient M *
          (n + 1) ^ normalizationExponent M := by
  exact Classical.choose_spec (Classical.choose_spec M.time_poly)

noncomputable def normalizationWitness
    (M : PolyDTMCandidate) :
    NormalizedCandidateWitness M := by
  let coefficient := normalizationCoefficient M
  let exponent := normalizationExponent M
  have hbound :
      ∀ n : Nat,
        M.timeBound n ≤ coefficient * (n + 1) ^ exponent := by
    exact normalizationBound M
  exact
    { coefficient := coefficient
      exponent := exponent
      dominates := hbound
      preserves_correctAt := by
        intro language x hCorrect
        exact correctAt_preserved_by_dominating_bound
          M coefficient exponent hbound language x hCorrect }

#print axioms MCore.Real.P02CandidateNormalization.correctAt_preserved_by_dominating_bound
#print axioms MCore.Real.P02CandidateNormalization.canonical_normalization
#print axioms MCore.Real.P02CandidateNormalization.normalizationWitness

end P02CandidateNormalization
end Real
end MCore
