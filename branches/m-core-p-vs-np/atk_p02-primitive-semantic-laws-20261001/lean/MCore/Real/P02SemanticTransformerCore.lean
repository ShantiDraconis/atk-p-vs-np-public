import MCore.Real.P02TotalCandidateSemanticCore
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02SemanticTransformerCore

open CircuitK1
open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02UniversalFailureMinCut
open P02TotalCandidateSemanticCore

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

def DeclaredAccept
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.accepting
    (M.machine.run
      (M.timeBound x.length)
      (initialTMConfig M.machine x)).state = true

def declaredAcceptBit
    (M : PolyDTMCandidate)
    (x : BitString) : Bool :=
  M.accepting
    (M.machine.run
      (M.timeBound x.length)
      (initialTMConfig M.machine x)).state

theorem declaredAcceptBit_true_iff
    (M : PolyDTMCandidate)
    (x : BitString) :
    declaredAcceptBit M x = true ↔ DeclaredAccept M x := Iff.rfl

/-- Safe semantic transformer: evaluate the candidate at the supplied input and
emit the canonical constant circuit with the opposite truth value.  This does
not assert self-reference or a universal fixed point. -/
def semanticNegationCircuit
    (M : PolyDTMCandidate)
    (x : BitString) : Circuit :=
  .const (!(declaredAcceptBit M x))

def semanticNegationBits
    (M : PolyDTMCandidate)
    (x : BitString) : BitString :=
  encodeCircuit (semanticNegationCircuit M x)

theorem semanticNegationBits_valid
    (M : PolyDTMCandidate)
    (x : BitString) :
    ∃ phi : Circuit, decodeCircuit (semanticNegationBits M x) = some phi := by
  refine ⟨semanticNegationCircuit M x, ?_⟩
  exact decodeCircuit_encode _

theorem semanticNegationBits_length
    (M : PolyDTMCandidate)
    (x : BitString) :
    (semanticNegationBits M x).length = 3 := by
  unfold semanticNegationBits semanticNegationCircuit
  cases h : declaredAcceptBit M x <;>
    simp [encodeCircuit]

theorem semanticNegationBits_flip
    (M : PolyDTMCandidate)
    (x : BitString) :
    SATTarget (semanticNegationBits M x) ↔
      ¬ DeclaredAccept M x := by
  change
    SATBits circuitBitEncoding
      (encodeCircuit (semanticNegationCircuit M x)) ↔
      ¬ DeclaredAccept M x
  rw [encoded_sat_equivalence]
  unfold semanticNegationCircuit DeclaredAccept declaredAcceptBit
  cases hacc :
      M.accepting
        (M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x)).state <;>
    simp [SATLanguage, evalCircuit, hacc]

/-- Weaker replacement for a literal string fixed point: the candidate only has
to give the same declared answer on x and on the transformed canonical SAT
instance. -/
def OutputAcceptanceAligned
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  DeclaredAccept M (semanticNegationBits M x) ↔
    DeclaredAccept M x

/-- Acceptance alignment is sufficient for semantic disagreement on the
transformer's output. -/
theorem transformed_output_fails_semantically
    (M : PolyDTMCandidate)
    (x : BitString)
    (halign : OutputAcceptanceAligned M x) :
    ¬ (M.accepting
          (M.machine.run
            (M.timeBound (semanticNegationBits M x).length)
            (initialTMConfig M.machine (semanticNegationBits M x))).state = true ↔
        SATTarget (semanticNegationBits M x)) := by
  intro hcorrect
  have hflip := semanticNegationBits_flip M x
  by_cases hx : DeclaredAccept M x
  · have hy : DeclaredAccept M (semanticNegationBits M x) :=
      halign.mpr hx
    have hsat : SATTarget (semanticNegationBits M x) :=
      hcorrect.mp hy
    exact (hflip.mp hsat) hx
  · have hsat : SATTarget (semanticNegationBits M x) :=
      hflip.mpr hx
    have hy : DeclaredAccept M (semanticNegationBits M x) :=
      hcorrect.mpr hsat
    exact hx (halign.mp hy)

/-- Exact weakened alignment core.  Unlike the falsified literal fixed-point
route, this asks only for equality of the candidate's declared Boolean answer
between a seed and its transformed output. -/
def SemanticAlignmentCore : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
      ∃ x : BitString, OutputAcceptanceAligned M x

theorem semantic_alignment_core_implies_total_semantic_core
    (H : SemanticAlignmentCore) :
    TotalCandidateSemanticCore := by
  intro M hTotal
  rcases H M hTotal with ⟨x, halign⟩
  refine ⟨semanticNegationBits M x, ?_⟩
  apply
    (P02FailureNormalForms.semanticDisagreement_iff_not_semantic_correct
      M (semanticNegationBits M x)).mpr
  exact transformed_output_fails_semantically M x halign

theorem semantic_alignment_core_implies_universal_failure
    (H : SemanticAlignmentCore) :
    UniversalFailure SATTarget :=
  total_semantic_core_implies_universal_failure
    (semantic_alignment_core_implies_total_semantic_core H)

#print axioms MCore.Real.P02SemanticTransformerCore.semanticNegationBits_valid
#print axioms MCore.Real.P02SemanticTransformerCore.semanticNegationBits_flip
#print axioms MCore.Real.P02SemanticTransformerCore.transformed_output_fails_semantically
#print axioms MCore.Real.P02SemanticTransformerCore.semantic_alignment_core_implies_universal_failure

end P02SemanticTransformerCore
end Real
end MCore
