import MCore.Real.P02CandidateCodingBoundary
import MCore.Real.P02DiagonalCompilerFrontierV2
import MCore.Real.P02UniversalWitnessDetailed
import MCore.Real.P02UniversalFailureAlgebra
import MCore.Real.P02SameInputClosure

namespace MCore
namespace Real
namespace P02G21ExpandedTree

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02DiagonalFrontier
open P02DiagonalCompilerFrontierV2
open P02SemanticSelfEmbedding
open P02UniversalFailureAlgebra
open P02SameInputClosure
open P02UniversalWitnessDetailed
open P02G21G22Attack
open P02TerminalFrontier

/-- Root semantic obligation of the diagonal route. -/
abbrev G21SemanticRoot : Prop :=
  SameInputClosure

/-- Stronger effective infrastructure root. It does not imply the semantic
root without an additional self-reference theorem. -/
abbrev G21EffectiveInfrastructure : Prop :=
  P02CandidateCodingBoundary.EffectiveDiagonalInfrastructureGap

theorem semanticRoot_iff_selfCodeExistence :
    G21SemanticRoot ↔ P02SelfCodeExistence.SelfCodeExistence :=
  sameInputClosure_iff_selfCodeExistence

/-- Same-input semantic closure packages directly as a V2 diagonal compiler. -/
noncomputable def semanticRootToDiagonalCompilerV2
    (h : G21SemanticRoot) :
    DiagonalCompilerV2 where
  compile := fun M => Classical.choose (h M)
  valid := by
    intro M
    exact (Classical.choose_spec (h M)).1
  flip := by
    intro M
    exact (Classical.choose_spec (h M)).2

theorem semanticRoot_to_diagonalCompilerV2Gap
    (h : G21SemanticRoot) :
    DiagonalCompilerV2Gap :=
  ⟨semanticRootToDiagonalCompilerV2 h⟩

theorem semanticRoot_to_universalWitnessFamilyGap
    (h : G21SemanticRoot) :
    UniversalWitnessFamilyGap :=
  sameInputClosure_to_universalWitnessFamilyGap h

theorem semanticRoot_to_semanticSelfEmbeddingGap
    (h : G21SemanticRoot) :
    SemanticSelfEmbeddingGap :=
  sameInputClosure_to_semanticSelfEmbeddingGap h

theorem semanticRoot_to_totalityOrSemanticCounterexample
    (h : G21SemanticRoot) :
    TotalityOrSemanticCounterexample := by
  exact pointwise_self_embedding_implies_normalized_failure
    (fun M => by
      rcases h M with ⟨x, hv, hf⟩
      exact ⟨x, hv, hf⟩)

theorem semanticRoot_to_g21
    (h : G21SemanticRoot) :
    G21Pointwise :=
  sameInputClosure_to_g21Pointwise h

theorem semanticRoot_to_p02
    (h : G21SemanticRoot) :
    P02Target :=
  sameInputClosure_to_p02Target h

theorem semanticRoot_to_sat_not_in_p
    (h : G21SemanticRoot) :
    ¬ InP (SATBits circuitBitEncoding) :=
  p02_target_iff_sat_not_in_p.mp
    (semanticRoot_to_p02 h)

/-- Exact algebraic characterization already proved in the hardened model. -/
theorem g21_iff_totality_or_semantic :
    G21Pointwise ↔ TotalityOrSemanticCounterexample :=
  g21_iff_totality_or_semantic_counterexample

/-- G21 is definitionally the universal failure proposition for the canonical
SAT target. -/
theorem g21_iff_universalFailure :
    G21Pointwise ↔ UniversalFailure (SATBits circuitBitEncoding) := by
  rfl

/-- G21 is equivalent to the pinned P02 target. -/
theorem g21_iff_p02 :
    G21Pointwise ↔ P02Target :=
  g21_pointwise_iff_p02_target

/-- P02 is equivalent to SAT non-membership in the hardened deterministic
class. -/
theorem p02_iff_sat_not_in_p :
    P02Target ↔ ¬ InP (SATBits circuitBitEncoding) :=
  p02_target_iff_sat_not_in_p

/-- Complete downstream chain from the one genuine semantic root. -/
theorem semanticRoot_full_downstream
    (h : G21SemanticRoot) :
    G21Pointwise ∧
    P02Target ∧
    ¬ InP (SATBits circuitBitEncoding) := by
  have hg : G21Pointwise := semanticRoot_to_g21 h
  have hp : P02Target := g21_pointwise_iff_p02_target.mp hg
  have hn : ¬ InP (SATBits circuitBitEncoding) :=
    p02_target_iff_sat_not_in_p.mp hp
  exact ⟨hg, hp, hn⟩

/-
OPEN ROOT, intentionally uninhabited here:
  G21SemanticRoot =
    forall M, exists x,
      CanonicalSATValid x and
      (SATTarget x iff not AcceptsAtDeclaredBound M x)

There is deliberately no theorem
  G21EffectiveInfrastructure -> G21SemanticRoot.
That arrow is the remaining self-reference/same-input mathematics.
-/

#print axioms MCore.Real.P02G21ExpandedTree.semanticRootToDiagonalCompilerV2
#print axioms MCore.Real.P02G21ExpandedTree.semanticRoot_to_g21
#print axioms MCore.Real.P02G21ExpandedTree.semanticRoot_to_sat_not_in_p
#print axioms MCore.Real.P02G21ExpandedTree.semanticRoot_full_downstream

end P02G21ExpandedTree
end Real
end MCore
