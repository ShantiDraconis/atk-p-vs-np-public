import MCore.Real.P03TerminalSemanticBridge
import MCore.Real.P02InvariantCore

namespace MCore
namespace Real
namespace P03RangeFailureFrontier

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P02TableauDynamics
open P02OddSemanticRecurrence
open P02InvariantCore
open P03OpenMathFrontier
open P03TerminalSemanticBridge

/--
A semantic failure occurring on the concrete image of the complemented
Cook--Levin reduction.
-/
def RangeFailure
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∃ x : BitString,
    SemanticFailureAt M (R_M M hTotal x)

/--
An adjacent full-run equality is exactly a d=0 terminal witness.
-/
def adjacentWitness
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (x : BitString)
    (hInv :
      FullRunAcceptEquivalent M x (R_M M hTotal x)) :
    FullRunAcceptanceWitness M hTotal := by
  refine
    { pair :=
        { seed := x
          i := 0
          j := 1
          odd := ?_ }
      acceptance := ?_ }
  · exact ⟨0, by omega⟩
  · simpa [FullInputOrbitPair.left, FullInputOrbitPair.right,
      Orbit] using hInv

/--
A range semantic failure yields an adjacent terminal witness.
No polynomial interpolation and no nonzero odd gap are needed.
-/
def rangeFailure_to_witness
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (H : RangeFailure M hTotal) :
    FullRunAcceptanceWitness M hTotal := by
  rcases H with ⟨x, hFail⟩
  have hInvProp :
      DeclaredAccepts M (R_M M hTotal x) ↔ DeclaredAccepts M x := by
    simpa [R_M] using
      (semanticFailure_reduce_iff_invariant M hTotal x).mp hFail
  have hInv :
      FullRunAcceptEquivalent M x (R_M M hTotal x) := by
    apply (full_run_accept_equiv_iff_obs).2
    exact hInvProp.symm
  exact adjacentWitness x hInv

/--
Conversely, every odd-separated terminal witness collapses to an adjacent
invariant edge, hence to a semantic failure on the reduction range.
-/
theorem witness_implies_rangeFailure
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (W : FullRunAcceptanceWitness M hTotal) :
    RangeFailure M hTotal := by
  have hOdd :
      OddSemanticRecurrence M (R_M M hTotal) :=
    full_run_witness_implies_odd_semantic_recurrence W
  rcases oddRecurrence_implies_adjacent hOdd with ⟨x, hInv⟩
  refine ⟨x, ?_⟩
  apply (semanticFailure_reduce_iff_invariant M hTotal x).2
  simpa [R_M, ObsEquiv] using hInv

theorem rangeFailure_iff_fullRunWitness
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    RangeFailure M hTotal ↔
      Nonempty (FullRunAcceptanceWitness M hTotal) := by
  constructor
  · intro H
    exact ⟨rangeFailure_to_witness H⟩
  · rintro ⟨W⟩
    exact witness_implies_rangeFailure W

/--
Exact terminal law with all orbit-index scaffolding eliminated.
-/
def RangeFailureLaw : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    RangeFailure M hTotal

theorem rangeFailureLaw_iff_fullRunAcceptanceLaw :
    RangeFailureLaw ↔ FullRunAcceptanceLaw := by
  constructor
  · intro H M hTotal
    exact (rangeFailure_iff_fullRunWitness M hTotal).1 (H M hTotal)
  · intro H M hTotal
    exact (rangeFailure_iff_fullRunWitness M hTotal).2 (H M hTotal)

/--
Perfect semantic flip on the concrete complemented Cook--Levin image.
This is the exact constructive content needed to falsify RangeFailureLaw for
one total candidate.
-/
def PerfectFlip
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∀ x : BitString,
    DeclaredAccepts M (R_M M hTotal x) ↔
      ¬ DeclaredAccepts M x

/--
The exact alternative to a range failure: M agrees with CanonicalSAT on
every point in the concrete reduction range.
-/
def RangeCorrect
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∀ x : BitString,
    DeclaredAccepts M (R_M M hTotal x) ↔
      PNPCookLevinMaterialMinCut.CanonicalSAT (R_M M hTotal x)

theorem rangeCorrect_iff_perfectFlip
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    RangeCorrect M hTotal ↔ PerfectFlip M hTotal := by
  constructor
  · intro hCorrect x
    have hSat :
        PNPCookLevinMaterialMinCut.CanonicalSAT (R_M M hTotal x) ↔
          ¬ DeclaredAccepts M x := by
      simpa [R_M] using complement_reduce_correct M hTotal x
    exact (hCorrect x).trans hSat
  · intro hFlip x
    have hSat :
        PNPCookLevinMaterialMinCut.CanonicalSAT (R_M M hTotal x) ↔
          ¬ DeclaredAccepts M x := by
      simpa [R_M] using complement_reduce_correct M hTotal x
    exact (hFlip x).trans hSat.symm

theorem no_rangeFailure_iff_rangeCorrect
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    ¬ RangeFailure M hTotal ↔ RangeCorrect M hTotal := by
  classical
  unfold RangeFailure RangeCorrect SemanticFailureAt
  constructor
  · intro hNo x
    by_contra hBad
    apply hNo
    exact ⟨x, hBad⟩
  · intro hCorrect
    rintro ⟨x, hBad⟩
    exact hBad (hCorrect x)

/--
For each total candidate there is an exact fail-closed dichotomy:
either the desired material range failure already exists, or the candidate is
correct on the entire concrete Cook--Levin reduction range.
-/
theorem range_failure_or_range_correct
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    RangeFailure M hTotal ∨ RangeCorrect M hTotal := by
  classical
  by_cases h : RangeFailure M hTotal
  · exact Or.inl h
  · exact Or.inr ((no_rangeFailure_iff_rangeCorrect M hTotal).mp h)

#print axioms MCore.Real.P03RangeFailureFrontier.rangeFailure_to_witness
#print axioms MCore.Real.P03RangeFailureFrontier.witness_implies_rangeFailure
#print axioms MCore.Real.P03RangeFailureFrontier.rangeFailure_iff_fullRunWitness
#print axioms MCore.Real.P03RangeFailureFrontier.rangeFailureLaw_iff_fullRunAcceptanceLaw
#print axioms MCore.Real.P03RangeFailureFrontier.rangeCorrect_iff_perfectFlip
#print axioms MCore.Real.P03RangeFailureFrontier.no_rangeFailure_iff_rangeCorrect
#print axioms MCore.Real.P03RangeFailureFrontier.range_failure_or_range_correct

end P03RangeFailureFrontier
end Real
end MCore
