import MCore.Real.P02DiagonalNoShortcut
import MCore.Real.P02ActiveBridgeClosure

namespace MCore
namespace Real
namespace P02UserFinalClosureProbe

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02SemanticSelfSubstitution
open P02DiagonalNoShortcut
open P02FiniteCandidateDescription

/-- User-proposed endpoint, expressed with repository-native predicates. -/
def ProposedEndpoint : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ y : BitString, OwnClockHalts M y) →
      ∃ x : BitString,
        ¬ M.CorrectAt
          (CanonicalSATBoundary.SATBits CanonicalCircuitBits.circuitBitEncoding)
          (rejectCode M x)

abbrev Endpoint : Prop := ProposedEndpoint
abbrev Gap : Prop := Endpoint
abbrev Habitant : Prop := Gap
abbrev Inhabitant : Prop := Habitant

theorem endpoint_to_gap : Endpoint → Gap := id
theorem gap_to_habitant : Gap → Habitant := id
theorem habitant_to_inhabitant : Habitant → Inhabitant := id
theorem inhabitant_to_endpoint : Inhabitant → Endpoint := id

theorem endpoint_gap_same : Endpoint ↔ Gap := Iff.rfl
theorem gap_habitant_same : Gap ↔ Habitant := Iff.rfl
theorem habitant_inhabitant_same : Habitant ↔ Inhabitant := Iff.rfl
theorem inhabitant_endpoint_same : Inhabitant ↔ Endpoint := Iff.rfl

/-- The proposed diagonal witness can at least be represented by the finite
candidate code already present in the repository. -/
noncomputable def diagonalWitness (M : PolyDTMCandidate) : BitString :=
  candidateCode M

/-- Exact missing law required by the user's final step. -/
def DiagonalFixedPointLaw : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ y : BitString, OwnClockHalts M y) →
      observedBit M (rejectCode M (diagonalWitness M)) =
        observedBit M (diagonalWitness M)

/-- If the missing fixed-point law exists, the proposed endpoint closes. -/
theorem diagonal_fixedPoint_law_closes_endpoint
    (H : DiagonalFixedPointLaw) :
    Endpoint := by
  intro M hTotal
  refine ⟨diagonalWitness M, ?_⟩
  apply semantic_closure_forces_failure M (diagonalWitness M) (hTotal (diagonalWitness M))
  exact (semanticClosureAt_iff_observed_eq M (diagonalWitness M)).2 (H M hTotal)

/-- The proposed fixed-point law is exactly the already isolated
P02DiagonalNoShortcut.CandidateCodeSemanticFixedPoint after unfolding diagonalWitness. -/
theorem diagonal_fixedPoint_law_iff_existing_frontier :
    DiagonalFixedPointLaw ↔ P02DiagonalNoShortcut.CandidateCodeSemanticFixedPoint := by
  rfl

/-- Therefore the user-proposed closure does not remove the last theorem:
it renames exactly the same frontier. -/
theorem proposed_endpoint_from_existing_frontier
    (H : P02DiagonalNoShortcut.CandidateCodeSemanticFixedPoint) :
    Endpoint := by
  exact diagonal_fixedPoint_law_closes_endpoint H

#print axioms MCore.Real.P02UserFinalClosureProbe.diagonal_fixedPoint_law_closes_endpoint
#print axioms MCore.Real.P02UserFinalClosureProbe.diagonal_fixedPoint_law_iff_existing_frontier
#print axioms MCore.Real.P02UserFinalClosureProbe.proposed_endpoint_from_existing_frontier

end P02UserFinalClosureProbe
end Real
end MCore
