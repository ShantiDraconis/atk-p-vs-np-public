import MCore.Real.P02OddSemanticRecurrence

namespace MCore
namespace Real
namespace P02OddParityMixingFrontier

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P02InvariantCore
open P02OddSemanticRecurrence

/--
A concrete odd-parity mixing witness for one total deterministic candidate.

The witness does not postulate a fixed point and does not mention P, NP,
UniversalFailure, or the final separation endpoint.  It records only an orbit
point, an odd orbital distance, and observational equality at the two endpoints.
-/
structure OddParityMixingWitness
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  seed : BitString
  start : Nat
  halfGap : Nat
  mixes :
    ObsEquiv M
      (Orbit (complementSemanticReduction M hTotal).reduce seed start)
      (Orbit (complementSemanticReduction M hTotal).reduce seed
        (start + (2 * halfGap + 1)))

/-- The exact universal existence claim proposed at the P02 frontier. -/
def OddParityMixingConjecture : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    Nonempty (OddParityMixingWitness M hTotal)

/--
One odd-parity mixing witness is exactly enough to produce odd semantic
recurrence for that candidate.
-/
theorem witness_implies_oddSemanticRecurrence
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (W : OddParityMixingWitness M hTotal) :
    OddSemanticRecurrence M
      (complementSemanticReduction M hTotal).reduce := by
  refine ⟨W.seed, W.start, W.start + (2 * W.halfGap + 1), ?_, W.mixes⟩
  exact ⟨W.halfGap, rfl⟩

/--
Conversely, every odd semantic recurrence contains such a witness.  This makes
the proposed object an exact data-level presentation of the current open
frontier rather than a hidden stronger assumption.
-/
noncomputable def witness_of_oddSemanticRecurrence
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (hOdd :
      OddSemanticRecurrence M
        (complementSemanticReduction M hTotal).reduce) :
    OddParityMixingWitness M hTotal := by
  classical
  rcases hOdd with ⟨seed, i, j, ⟨d, hj⟩, hObs⟩
  refine
    { seed := seed
      start := i
      halfGap := d
      mixes := ?_ }
  simpa [hj] using hObs

theorem oddParityMixing_iff_totalOddSemanticRecurrence :
    OddParityMixingConjecture ↔ TotalOddSemanticRecurrence := by
  constructor
  · intro H M hTotal
    exact witness_implies_oddSemanticRecurrence
      (Classical.choice (H M hTotal))
  · intro H M hTotal
    exact ⟨witness_of_oddSemanticRecurrence (H M hTotal)⟩

/--
If the proposed odd-parity mixing conjecture is eventually proved materially,
the existing certified reduction chain closes the repository's internal P≠NP
endpoint.
-/
theorem oddParityMixing_closes_internal_endpoint
    (H : OddParityMixingConjecture) :
    PneqNP := by
  exact totalOddRecurrence_closes_internal_endpoint
    ((oddParityMixing_iff_totalOddSemanticRecurrence).mp H)

/--
Research-facing name for the sole remaining material producer.
This is intentionally a proposition, not an axiom and not a theorem claiming
that the witness already exists.
-/
def ODD_PARITY_MIXING_OPEN_MATH : Prop :=
  OddParityMixingConjecture

#print axioms MCore.Real.P02OddParityMixingFrontier.witness_implies_oddSemanticRecurrence
#print axioms MCore.Real.P02OddParityMixingFrontier.witness_of_oddSemanticRecurrence
#print axioms MCore.Real.P02OddParityMixingFrontier.oddParityMixing_iff_totalOddSemanticRecurrence
#print axioms MCore.Real.P02OddParityMixingFrontier.oddParityMixing_closes_internal_endpoint

end P02OddParityMixingFrontier
end Real
end MCore
