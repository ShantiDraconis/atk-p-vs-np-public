import MCore.Real.P02SemanticInvariantCore
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02SemanticNegationReduction

open CircuitK1
open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02TotalCandidateFailureMinCut
open P02SemanticInvariantCore

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

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
    declaredAcceptBit M x = true ↔
      DeclaredAccepts M x := Iff.rfl

/-- Canonical constant circuit with the opposite truth value of M's declared
answer on x. -/
def semanticNegationCircuit
    (M : PolyDTMCandidate)
    (x : BitString) : Circuit :=
  .const (!(declaredAcceptBit M x))

def semanticNegationBits
    (M : PolyDTMCandidate)
    (x : BitString) : BitString :=
  encodeCircuit (semanticNegationCircuit M x)

theorem semanticNegationBits_flip
    (M : PolyDTMCandidate)
    (x : BitString) :
    CanonicalSAT (semanticNegationBits M x) ↔
      ¬ DeclaredAccepts M x := by
  change
    SATBits circuitBitEncoding
      (encodeCircuit (semanticNegationCircuit M x)) ↔
      ¬ DeclaredAccepts M x
  rw [encoded_sat_equivalence]
  unfold semanticNegationCircuit DeclaredAccepts declaredAcceptBit
  cases hacc :
      M.accepting
        (M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x)).state <;>
    simp [SATLanguage, evalCircuit, hacc]

/-- The complement reduction required by the invariant core is explicit and
requires no Cook--Levin hypothesis. -/
def semanticNegationReduction
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    ComplementSemanticReduction M hTotal where
  reduce := semanticNegationBits M
  correct := semanticNegationBits_flip M

/-- The sole remaining data-level obligation after the complement reduction is
materialized: one seed whose declared answer is preserved by semantic negation. -/
def SemanticNegationInvariantPoint
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  Nonempty (InvariantPoint (semanticNegationReduction M hTotal))

def SEMANTIC_NEGATION_INVARIANT_OPEN_MATH : Prop :=
  ∀ (M : PolyDTMCandidate) (hTotal : DeclaredClockTotal M),
    SemanticNegationInvariantPoint M hTotal

theorem semanticNegationInvariant_closes_G2
    (H : SEMANTIC_NEGATION_INVARIANT_OPEN_MATH) :
    UniversalFailure CanonicalSAT := by
  apply totalInvariantPoint_closes_G2
  refine ⟨semanticNegationReduction, ?_⟩
  intro M hTotal
  exact H M hTotal

#print axioms MCore.Real.P02SemanticNegationReduction.semanticNegationBits_flip
#print axioms MCore.Real.P02SemanticNegationReduction.semanticNegationReduction
#print axioms MCore.Real.P02SemanticNegationReduction.semanticNegationInvariant_closes_G2

end P02SemanticNegationReduction
end Real
end MCore
