import Mathlib
import MCore.Real.OpenMathCore.Calculus
import MCore.Real.P02UniversalFailureAlgebra

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open P02UniversalFailureAlgebra

structure CandidateBehavior where
  observable : PolyDTMCandidate → BitString → ℝ
  cost : PolyDTMCandidate → BitString → ℕ
  potential : PolyDTMCandidate → BitString → ℝ
  potential_nonneg : ∀ M x, 0 ≤ potential M x

structure BehavioralLaw (B : CandidateBehavior) where
  monotone_cost_under_extension :
    ∀ M x y, B.cost M x ≤ B.cost M (x ++ y)
  bounded_potential_by_cost :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ M x, B.potential M x ≤ c * (B.cost M x : ℝ)

structure MismatchDetector (B : CandidateBehavior) where
  score : PolyDTMCandidate → BitString → ℝ
  detects : ∀ M x, score M x ≠ 0 → SemanticMismatch M x

structure TotalCandidateSeparationLaw where
  witness : PolyDTMCandidate → BitString
  separates :
    ∀ M, DeclaredClockTotal M → SemanticMismatch M (witness M)

theorem totalCandidateSeparationLaw_closes_core
    (L : TotalCandidateSeparationLaw) :
    ∀ M : PolyDTMCandidate,
      DeclaredClockTotal M → ∃ x : BitString, SemanticMismatch M x := by
  intro M hTotal
  exact ⟨L.witness M, L.separates M hTotal⟩

end MCore.Real.OpenMathCore
