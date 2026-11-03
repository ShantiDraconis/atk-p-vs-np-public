import MCore.Real.P02SelfCodeExistence
import MCore.Real.P02SemanticSelfEmbedding
import MCore.Real.P02G21G22Attack

namespace MCore
namespace Real
namespace P02SameInputClosure

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02DiagonalFrontier
open P02SelfCodeExistence
open P02SemanticSelfEmbedding
open P02G21G22Attack

/-- One same-input semantic counterexample against one deterministic
polynomial-time candidate. The same bitstring appears both as the SAT instance
and as the candidate input. -/
def SameInputWitness (M : PolyDTMCandidate) : Prop :=
  ∃ x : BitString,
    CanonicalSATValid x ∧
    (SATBits circuitBitEncoding x ↔
      ¬ AcceptsAtDeclaredBound M x)

/-- Universal same-input closure. This is intentionally the exact semantic
self-code obligation, stated with its same-input condition visible. -/
def SameInputClosure : Prop :=
  ∀ M : PolyDTMCandidate, SameInputWitness M

theorem sameInputWitness_iff_selfCode_at
    (M : PolyDTMCandidate) :
    SameInputWitness M ↔
      ∃ x : BitString,
        CanonicalSATValid x ∧
        (SATBits circuitBitEncoding x ↔
          ¬ AcceptsAtDeclaredBound M x) := Iff.rfl

theorem sameInputClosure_iff_selfCodeExistence :
    SameInputClosure ↔ SelfCodeExistence := Iff.rfl

/-- A same-input witness packages directly into the hardened diagonal witness. -/
noncomputable def sameInputWitnessToDiagonal
    (M : PolyDTMCandidate)
    (h : SameInputWitness M) :
    DiagonalCounterexampleWitness M :=
  let x : BitString := Classical.choose h
  let hs := Classical.choose_spec h
  { bits := x
    valid := hs.1
    flips := hs.2 }

/-- Same-input closure gives a full semantic self-embedder. -/
noncomputable def sameInputClosureToSemanticSelfEmbedder
    (h : SameInputClosure) :
    SemanticSelfEmbedder where
  bits := fun M => Classical.choose (h M)
  valid := by
    intro M
    exact (Classical.choose_spec (h M)).1
  flips := by
    intro M
    exact (Classical.choose_spec (h M)).2

theorem sameInputClosure_to_semanticSelfEmbeddingGap
    (h : SameInputClosure) :
    SemanticSelfEmbeddingGap :=
  ⟨sameInputClosureToSemanticSelfEmbedder h⟩

/-- Downstream promotion: once same-input closure is actually proved,
G21Pointwise follows without another mathematical assumption. -/
theorem sameInputClosure_to_g21Pointwise
    (h : SameInputClosure) :
    G21Pointwise := by
  intro M
  rcases h M with ⟨x, hvalid, hflip⟩
  refine ⟨x, ?_⟩
  exact diagonal_witness_fails M
    { bits := x
      valid := hvalid
      flips := hflip }

theorem sameInputClosure_to_p02Target
    (h : SameInputClosure) :
    P02TerminalFrontier.P02Target :=
  g21_pointwise_iff_p02_target.mp
    (sameInputClosure_to_g21Pointwise h)

#print axioms MCore.Real.P02SameInputClosure.sameInputWitnessToDiagonal
#print axioms MCore.Real.P02SameInputClosure.sameInputClosureToSemanticSelfEmbedder
#print axioms MCore.Real.P02SameInputClosure.sameInputClosure_to_g21Pointwise
#print axioms MCore.Real.P02SameInputClosure.sameInputClosure_to_p02Target

end P02SameInputClosure
end Real
end MCore
