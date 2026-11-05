import Mathlib
import MCore.Real.P02UniversalFailureAlgebra
import MCore.Real.P01FullVerifierEvalLocal

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02UniversalFailureAlgebra
open P01FullVerifierEvalLocal

abbrev CandidateAccepts := P02DiagonalFrontier.AcceptsAtDeclaredBound
abbrev CandidateHalts := DeclaredHalts
abbrev CandidateClockTotal := DeclaredClockTotal
abbrev CandidateMismatch := SemanticMismatch

theorem mismatch_exact
    (M : PolyDTMCandidate) (x : BitString) :
    CandidateMismatch M x ↔
      (CandidateAccepts M x ∧ ¬ SATBits circuitBitEncoding x) ∨
      (¬ CandidateAccepts M x ∧ SATBits circuitBitEncoding x) := by
  rfl

theorem mismatch_iff_not_declared_match
    (M : PolyDTMCandidate) (x : BitString) :
    CandidateMismatch M x ↔ ¬ DeclaredSATMatch M x := by
  exact (not_declaredSATMatch_iff_semanticMismatch M x).symm

structure SemanticSeparationWitness (M : PolyDTMCandidate) where
  bits : BitString
  mismatch : CandidateMismatch M bits

def TotalSemanticSeparation : Prop :=
  ∀ M : PolyDTMCandidate, DeclaredClockTotal M → Nonempty (SemanticSeparationWitness M)

theorem totalSemanticSeparation_iff_core :
    TotalSemanticSeparation ↔
      ∀ M : PolyDTMCandidate,
        DeclaredClockTotal M → ∃ x : BitString, SemanticMismatch M x := by
  constructor
  · intro h M hT
    rcases h M hT with ⟨w⟩
    exact ⟨w.bits, w.mismatch⟩
  · intro h M hT
    rcases h M hT with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩

end MCore.Real.OpenMathCore
