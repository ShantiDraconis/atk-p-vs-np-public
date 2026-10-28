import MCore.Real.P02UniversalLowerBound
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02CanonicalClockReduction

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02UniversalLowerBound

def canonicalTimeBound (coefficient exponent : Nat) : TimeBound :=
  fun n => coefficient * (n + 1) ^ exponent

theorem canonicalTimeBound_poly
    (coefficient exponent : Nat) :
    PolynomialTimeBound (canonicalTimeBound coefficient exponent) := by
  exact ⟨coefficient, exponent, fun n => Nat.le_refl _⟩

def normalize
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat) :
    PolyDTMCandidate :=
  { stateCount := M.stateCount
    machine := M.machine
    blank_none := M.blank_none
    accepting := M.accepting
    timeBound := canonicalTimeBound coefficient exponent
    time_poly := canonicalTimeBound_poly coefficient exponent }

theorem normalize_correctAt
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat)
    (hbound :
      ∀ n, M.timeBound n ≤ canonicalTimeBound coefficient exponent n)
    (L : BitLanguage)
    (x : BitString)
    (h : M.CorrectAt L x) :
    (normalize M coefficient exponent).CorrectAt L x := by
  unfold PolyDTMCandidate.CorrectAt at h ⊢
  dsimp [normalize]
  rcases h with ⟨hhalt, hsem⟩
  let cfg := initialTMConfig M.machine x
  let oldFuel := M.timeBound x.length
  let newFuel := canonicalTimeBound coefficient exponent x.length
  have hle : oldFuel ≤ newFuel := hbound x.length
  have hhalt' :
      M.machine.HaltsWithin newFuel cfg :=
    MachineRunLemmas.haltsWithin_mono M.machine cfg hle hhalt
  have hrun :
      M.machine.run newFuel cfg = M.machine.run oldFuel cfg :=
    MachineRunLemmas.run_to_larger_fuel_of_halt
      M.machine cfg (M.machine.run oldFuel cfg) hle rfl hhalt
  constructor
  · exact hhalt'
  · rw [hrun]
    exact hsem

theorem normalization_exists
    (M : PolyDTMCandidate) :
    ∃ coefficient exponent,
      ∀ L x,
        M.CorrectAt L x →
          (normalize M coefficient exponent).CorrectAt L x := by
  rcases M.time_poly with ⟨c, k, hbound⟩
  exact ⟨c, k, fun L x h => normalize_correctAt M c k hbound L x h⟩

/-- A universal adversary only for explicit monomial-clock normal forms. -/
structure NormalizedAdversary where
  counterexample :
    (M : PolyDTMCandidate) →
    (coefficient exponent : Nat) →
    BitString
  fails :
    ∀ (M : PolyDTMCandidate) (coefficient exponent : Nat),
      FailureAt
        (normalize M coefficient exponent)
        (counterexample M coefficient exponent)

/-- Failure of the normalized extension transfers back to the original
candidate because correctness of the original would have survived clock
extension. -/
theorem normalized_failure_transfers_back
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat)
    (hbound :
      ∀ n, M.timeBound n ≤ canonicalTimeBound coefficient exponent n)
    (x : BitString)
    (hfail :
      FailureAt (normalize M coefficient exponent) x) :
    FailureAt M x := by
  intro hM
  exact hfail (normalize_correctAt M coefficient exponent hbound SATTarget x hM)

/-- Therefore it is sufficient to prove the universal lower bound only on
explicit monomial-clock representatives. -/
theorem normalizedAdversary_closes
    (A : NormalizedAdversary) :
    UniversalSATLowerBound := by
  intro M
  rcases M.time_poly with ⟨c, k, hbound⟩
  let x := A.counterexample M c k
  refine ⟨x, ?_⟩
  exact normalized_failure_transfers_back
    M c k hbound x (A.fails M c k)


/-- Conversely, the universal lower bound chooses a failing input for every
normalized representative. Hence the monomial-clock adversary is not a
stronger assumption: it is an exact normal form. -/
noncomputable def normalizedAdversaryOfUniversal
    (h : UniversalSATLowerBound) :
    NormalizedAdversary := by
  classical
  refine
    { counterexample := fun M c k =>
        Classical.choose (h (normalize M c k))
      fails := ?_ }
  intro M c k
  exact Classical.choose_spec (h (normalize M c k))

theorem normalizedAdversary_iff_universalSATLowerBound :
    Nonempty NormalizedAdversary ↔ UniversalSATLowerBound := by
  constructor
  · rintro ⟨A⟩
    exact normalizedAdversary_closes A
  · intro h
    exact ⟨normalizedAdversaryOfUniversal h⟩

theorem normalizedAdversary_iff_notInP :
    Nonempty NormalizedAdversary ↔ ¬ InP SATTarget := by
  rw [normalizedAdversary_iff_universalSATLowerBound]
  exact universalSATLowerBound_iff_notInP

end P02CanonicalClockReduction
end Real
end MCore
