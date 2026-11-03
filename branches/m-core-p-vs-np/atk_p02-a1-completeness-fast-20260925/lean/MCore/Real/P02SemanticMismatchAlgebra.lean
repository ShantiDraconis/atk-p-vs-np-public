import MCore.Real.P02UniversalFailureAlgebra

namespace MCore
namespace Real
namespace P02SemanticMismatchAlgebra

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02UniversalFailureAlgebra

theorem semanticMismatch_iff_not_match
    (M : PolyDTMCandidate) (x : BitString) :
    SemanticMismatch M x ↔ ¬ DeclaredSATMatch M x := by
  exact (not_declaredSATMatch_iff_semanticMismatch M x).symm

theorem semanticMismatch_iff_xor
    (M : PolyDTMCandidate) (x : BitString) :
    SemanticMismatch M x ↔
      (AcceptsAtDeclaredBound M x ∧ ¬ SATBits circuitBitEncoding x) ∨
      (¬ AcceptsAtDeclaredBound M x ∧ SATBits circuitBitEncoding x) := by
  rfl

theorem no_semanticMismatch_iff_match
    (M : PolyDTMCandidate) (x : BitString) :
    ¬ SemanticMismatch M x ↔ DeclaredSATMatch M x := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hnm
    exact h ((semanticMismatch_iff_not_match M x).mpr hnm)
  · intro hm hmis
    exact (semanticMismatch_iff_not_match M x).mp hmis hm

theorem declaredSATCorrect_iff_no_semanticMismatch
    (M : PolyDTMCandidate) :
    DeclaredSATCorrect M ↔
      ∀ x : BitString, ¬ SemanticMismatch M x := by
  unfold DeclaredSATCorrect
  constructor
  · intro h x
    exact (no_semanticMismatch_iff_match M x).mpr (h x)
  · intro h x
    exact (no_semanticMismatch_iff_match M x).mp (h x)

theorem total_and_semantically_correct_iff_correct_everywhere
    (M : PolyDTMCandidate) :
    (DeclaredClockTotal M ∧ DeclaredSATCorrect M) ↔
      ∀ x : BitString,
        M.CorrectAt (SATBits circuitBitEncoding) x := by
  constructor
  · rintro ⟨hT, hS⟩ x
    exact (correctAt_iff_declared_halts_and_match M x).mpr ⟨hT x, hS x⟩
  · intro h
    constructor
    · intro x
      exact ((correctAt_iff_declared_halts_and_match M x).mp (h x)).1
    · intro x
      exact ((correctAt_iff_declared_halts_and_match M x).mp (h x)).2

#print axioms MCore.Real.P02SemanticMismatchAlgebra.declaredSATCorrect_iff_no_semanticMismatch
#print axioms MCore.Real.P02SemanticMismatchAlgebra.total_and_semantically_correct_iff_correct_everywhere

end P02SemanticMismatchAlgebra
end Real
end MCore
