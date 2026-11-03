import MCore.Real.P02UniversalFailureAlgebra
import MCore.Real.P02SemanticStabilityLane

namespace MCore
namespace Real
namespace P02FastPathAttack

open CanonicalFinalProof
open CanonicalCircuitBits
open P02UniversalFailureAlgebra
open P02SemanticStabilityLane

/-- Minimal active P02 target on the current architecture:
only candidates that actually halt within their declared polynomial clock
still need a semantic SAT counterexample. Non-total candidates already fail
CorrectAt through the clock branch. -/
def TotalCandidateSemanticFailure : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
      ∃ x : BitString, SemanticMismatch M x

theorem totalCandidateSemanticFailure_to_normalized
    (h : TotalCandidateSemanticFailure) :
    TotalityOrSemanticCounterexample := by
  intro M
  by_cases hTotal : DeclaredClockTotal M
  · exact Or.inr (h M hTotal)
  · exact Or.inl hTotal

theorem totalCandidateSemanticFailure_closes_P02
    (h : TotalCandidateSemanticFailure) :
    P02TerminalFrontier.P02Target :=
  totality_or_semantic_closes_p02
    (totalCandidateSemanticFailure_to_normalized h)

theorem p02Target_to_totalCandidateSemanticFailure
    (h : P02TerminalFrontier.P02Target) :
    TotalCandidateSemanticFailure := by
  have hG21 : P02G21G22Attack.G21Pointwise :=
    P02G21G22Attack.g21_pointwise_iff_p02_target.mpr h
  intro M hTotal
  rcases hG21 M with ⟨x, hx⟩
  have hsplit :=
    (not_correctAt_iff_clock_or_semantic_mismatch M x).mp hx
  rcases hsplit with hclock | hmismatch
  · exact False.elim (hclock (hTotal x))
  · exact ⟨x, hmismatch⟩

theorem totalCandidateSemanticFailure_iff_P02Target :
    TotalCandidateSemanticFailure ↔
      P02TerminalFrontier.P02Target := by
  constructor
  · exact totalCandidateSemanticFailure_closes_P02
  · exact p02Target_to_totalCandidateSemanticFailure

/-- The semantic-stability lane is a sufficient but stronger producer for the
new minimal target. -/
theorem semanticStability_to_totalCandidateSemanticFailure
    (hStable : UniformSemanticStabilityProducer) :
    TotalCandidateSemanticFailure := by
  intro M _hTotal
  let hx := hStable M
  classical
  let x : BitString := Classical.choose hx
  have hs : SemanticStabilityAt M x := Classical.choose_spec hx
  refine ⟨semanticTransform M x, ?_⟩
  apply self_embed_witness_gives_semanticMismatch
  exact (witnessOfSemanticStability M x hs).flips

/-- Exact fast-path OPEN_MATH. This supersedes semantic stability as the
preferred target, while semantic stability remains a valid sufficient route. -/
def OPEN_MATH_P02_FAST : Prop :=
  TotalCandidateSemanticFailure

#print axioms MCore.Real.P02FastPathAttack.totalCandidateSemanticFailure_to_normalized
#print axioms MCore.Real.P02FastPathAttack.totalCandidateSemanticFailure_closes_P02
#print axioms MCore.Real.P02FastPathAttack.p02Target_to_totalCandidateSemanticFailure
#print axioms MCore.Real.P02FastPathAttack.totalCandidateSemanticFailure_iff_P02Target
#print axioms MCore.Real.P02FastPathAttack.semanticStability_to_totalCandidateSemanticFailure

end P02FastPathAttack
end Real
end MCore
