import MCore.Real.P02SemanticTransformerCore

namespace MCore
namespace Real
namespace P02SemanticTransformerDichotomy

open CircuitK1
open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02UniversalFailureMinCut
open P02FailureNormalForms
open P02TotalCandidateSemanticCore
open P02SemanticTransformerCore

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

def falseBits : BitString :=
  encodeCircuit (.const false)

def trueBits : BitString :=
  encodeCircuit (.const true)

theorem falseBits_not_sat :
    ¬ SATTarget falseBits := by
  intro h
  have h' :
      SATLanguage (.const false) :=
    (encoded_sat_equivalence (.const false)).mp h
  simpa [SATLanguage, evalCircuit] using h'

theorem trueBits_sat :
    SATTarget trueBits := by
  apply (encoded_sat_equivalence (.const true)).mpr
  simp [SATLanguage, evalCircuit]

theorem semanticNegationBits_of_accept
    (M : PolyDTMCandidate)
    (x : BitString)
    (h : DeclaredAccept M x) :
    semanticNegationBits M x = falseBits := by
  unfold semanticNegationBits semanticNegationCircuit falseBits
  have hb : declaredAcceptBit M x = true := h
  rw [hb]
  rfl

theorem semanticNegationBits_of_reject
    (M : PolyDTMCandidate)
    (x : BitString)
    (h : ¬ DeclaredAccept M x) :
    semanticNegationBits M x = trueBits := by
  unfold semanticNegationBits semanticNegationCircuit trueBits
  have hb : declaredAcceptBit M x = false := by
    cases hv : declaredAcceptBit M x with
    | false => rfl
    | true =>
        exact False.elim (h hv)
  rw [hb]
  rfl

/-- The only Boolean pattern on the two constant canonical SAT instances that
blocks the one-step semantic-negation alignment route. -/
def ConstantCorrectPattern
    (M : PolyDTMCandidate) : Prop :=
  ¬ DeclaredAccept M falseBits ∧
    DeclaredAccept M trueBits

theorem alignment_or_constantCorrectPattern
    (M : PolyDTMCandidate) :
    (∃ x : BitString, OutputAcceptanceAligned M x) ∨
      ConstantCorrectPattern M := by
  classical
  by_cases hf : DeclaredAccept M falseBits
  · left
    refine ⟨falseBits, ?_⟩
    unfold OutputAcceptanceAligned
    rw [semanticNegationBits_of_accept M falseBits hf]
  · by_cases ht : DeclaredAccept M trueBits
    · exact Or.inr ⟨hf, ht⟩
    · left
      refine ⟨falseBits, ?_⟩
      unfold OutputAcceptanceAligned
      rw [semanticNegationBits_of_reject M falseBits hf]
      constructor
      · intro h
        exact False.elim (ht h)
      · intro h
        exact False.elim (hf h)

theorem alignment_of_not_constantCorrectPattern
    (M : PolyDTMCandidate)
    (hnot : ¬ ConstantCorrectPattern M) :
    ∃ x : BitString, OutputAcceptanceAligned M x := by
  rcases alignment_or_constantCorrectPattern M with h | h
  · exact h
  · exact False.elim (hnot h)

/-- Exact reduced semantic core: after the safe constant transformer handles
all other candidates, only total-clocked candidates already correct on the two
fixed SAT encodings remain. -/
def ConstantPatternSemanticCore : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
    ConstantCorrectPattern M →
      ∃ x : BitString, SemanticDisagreement M x

theorem constant_pattern_core_implies_total_semantic_core
    (H : ConstantPatternSemanticCore) :
    TotalCandidateSemanticCore := by
  intro M hTotal
  by_cases hPattern : ConstantCorrectPattern M
  · exact H M hTotal hPattern
  · rcases alignment_of_not_constantCorrectPattern M hPattern with
      ⟨x, halign⟩
    refine ⟨semanticNegationBits M x, ?_⟩
    apply
      (semanticDisagreement_iff_not_semantic_correct
        M (semanticNegationBits M x)).mpr
    exact transformed_output_fails_semantically M x halign

theorem total_semantic_core_implies_constant_pattern_core
    (H : TotalCandidateSemanticCore) :
    ConstantPatternSemanticCore := by
  intro M hTotal _
  exact H M hTotal

theorem constant_pattern_core_iff_total_semantic_core :
    ConstantPatternSemanticCore ↔ TotalCandidateSemanticCore := by
  constructor
  · exact constant_pattern_core_implies_total_semantic_core
  · exact total_semantic_core_implies_constant_pattern_core

theorem constant_pattern_core_iff_universal_failure :
    ConstantPatternSemanticCore ↔ UniversalFailure SATTarget := by
  rw [constant_pattern_core_iff_total_semantic_core]
  exact total_semantic_core_iff_universal_failure

theorem constant_pattern_core_closes_internal_endpoint
    (H : ConstantPatternSemanticCore) :
    PneqNP :=
  total_semantic_core_closes_internal_endpoint
    (constant_pattern_core_implies_total_semantic_core H)

#print axioms MCore.Real.P02SemanticTransformerDichotomy.falseBits_not_sat
#print axioms MCore.Real.P02SemanticTransformerDichotomy.trueBits_sat
#print axioms MCore.Real.P02SemanticTransformerDichotomy.alignment_or_constantCorrectPattern
#print axioms MCore.Real.P02SemanticTransformerDichotomy.constant_pattern_core_iff_total_semantic_core
#print axioms MCore.Real.P02SemanticTransformerDichotomy.constant_pattern_core_iff_universal_failure

end P02SemanticTransformerDichotomy
end Real
end MCore
