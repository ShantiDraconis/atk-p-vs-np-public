import MCore.Real.P02ExactDiagonalFrontier

namespace MCore
namespace Real
namespace P02BehavioralAlignment

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P02ExactDiagonalFrontier

/-- The Cook--Levin output does not need to be literally equal to its source
input.  It is enough that the deterministic candidate gives both bitstrings
the same declared acceptance value. -/
def BehavioralSelfAlignment
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∃ x : BitString,
    DeclaredAccepts M
        ((complementSemanticReduction M hTotal).reduce x) ↔
      DeclaredAccepts M x

/-- Literal self-input equality is sufficient for behavioral alignment, but is
not required by the downstream contradiction. -/
theorem literal_alignment_implies_behavioral
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (hLiteral : SelfInputAlignment M hTotal) :
    BehavioralSelfAlignment M hTotal := by
  rcases hLiteral with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [hx]

/-- The concrete complement Cook--Levin correctness theorem plus behavioral
alignment produces exactly the semantic diagonal witness required by the
minimal P02 frontier. -/
theorem behavioral_alignment_gives_exact_witness
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (hAlign : BehavioralSelfAlignment M hTotal) :
    ExactDiagonalWitness M := by
  rcases hAlign with ⟨x, hBehavior⟩
  let y : BitString :=
    (complementSemanticReduction M hTotal).reduce x
  refine ⟨y, ?_⟩
  have hReduce :
      CanonicalSAT y ↔ ¬ DeclaredAccepts M x := by
    simpa [y] using complement_reduce_correct M hTotal x
  constructor
  · intro hSat hAy
    have hNotAx : ¬ DeclaredAccepts M x := hReduce.mp hSat
    apply hNotAx
    exact hBehavior.mp hAy
  · intro hNotAy
    apply hReduce.mpr
    intro hAx
    apply hNotAy
    exact hBehavior.mpr hAx

/-- Uniform behavioral alignment is a sufficient concrete producer for the
exact diagonal frontier. -/
def TotalBehavioralAlignmentProducer : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
      BehavioralSelfAlignment M

theorem total_behavioral_alignment_to_exact
    (B : TotalBehavioralAlignmentProducer) :
    TotalExactDiagonalProducer := by
  intro M hTotal
  exact behavioral_alignment_gives_exact_witness
    M hTotal (B M hTotal)

theorem total_behavioral_alignment_implies_universal_failure
    (B : TotalBehavioralAlignmentProducer) :
    UniversalFailure CanonicalSAT :=
  total_exact_diagonal_implies_universal_failure
    (total_behavioral_alignment_to_exact B)

theorem total_behavioral_alignment_closes_internal_endpoint
    (B : TotalBehavioralAlignmentProducer) :
    PneqNP :=
  total_exact_diagonal_closes_internal_endpoint
    (total_behavioral_alignment_to_exact B)

#print axioms MCore.Real.P02BehavioralAlignment.literal_alignment_implies_behavioral
#print axioms MCore.Real.P02BehavioralAlignment.behavioral_alignment_gives_exact_witness
#print axioms MCore.Real.P02BehavioralAlignment.total_behavioral_alignment_to_exact
#print axioms MCore.Real.P02BehavioralAlignment.total_behavioral_alignment_implies_universal_failure
#print axioms MCore.Real.P02BehavioralAlignment.total_behavioral_alignment_closes_internal_endpoint

end P02BehavioralAlignment
end Real
end MCore
