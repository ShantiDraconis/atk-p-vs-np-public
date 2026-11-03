import MCore.Real.P02ClockedDiagonalCompiler
import MCore.Real.P02UniversalFailureAlgebra

namespace MCore
namespace Real
namespace P02ConstantOrbitAudit

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02ClockedDiagonalCompiler
open P02UniversalFailureAlgebra

def falseBits : BitString := encodeCircuit (.const false)
def trueBits : BitString := encodeCircuit (.const true)

theorem falseBits_not_sat :
    ¬ SATBits circuitBitEncoding falseBits := by
  intro h
  have hs : SATLanguage (.const false) := by
    exact (encoded_sat_equivalence (.const false)).mp h
  simpa [SATLanguage, CircuitK1.evalCircuit] using hs

theorem trueBits_sat :
    SATBits circuitBitEncoding trueBits := by
  apply (encoded_sat_equivalence (.const true)).mpr
  simp [SATLanguage, CircuitK1.evalCircuit]

theorem no_mismatch_on_falseBits
    (M : PolyDTMCandidate)
    (h : ¬ AcceptsAtDeclaredBound M falseBits) :
    ¬ SemanticMismatch M falseBits := by
  intro hm
  rcases hm with ⟨ha, _⟩ | ⟨_, hs⟩
  · exact h ha
  · exact falseBits_not_sat hs

theorem no_mismatch_on_trueBits
    (M : PolyDTMCandidate)
    (h : AcceptsAtDeclaredBound M trueBits) :
    ¬ SemanticMismatch M trueBits := by
  intro hm
  rcases hm with ⟨_, hns⟩ | ⟨hna, _⟩
  · exact hns trueBits_sat
  · exact hna h

theorem semanticDiagonal_false_to_true
    (M : PolyDTMCandidate)
    (h : ¬ AcceptsAtDeclaredBound M falseBits) :
    semanticDiagonalBits M falseBits = trueBits := by
  unfold semanticDiagonalBits semanticDiagonalCircuit falseBits trueBits
  rw [← declaredAcceptBit_true_iff] at h
  cases hd : declaredAcceptBit M (encodeCircuit (.const false))
  · rfl
  · exact False.elim (h hd)

theorem semanticDiagonal_true_to_false
    (M : PolyDTMCandidate)
    (h : AcceptsAtDeclaredBound M trueBits) :
    semanticDiagonalBits M trueBits = falseBits := by
  unfold semanticDiagonalBits semanticDiagonalCircuit falseBits trueBits
  have hd : declaredAcceptBit M (encodeCircuit (.const true)) = true :=
    (declaredAcceptBit_true_iff M (encodeCircuit (.const true))).mpr h
  rw [hd]
  rfl

/-- If M correctly classifies the two constant circuits, the constant-output
semantic transformer forms a 2-cycle and yields no mismatch on either node.
Thus this local two-point orbit cannot by itself prove the active P02 target. -/
theorem constant_orbit_no_forced_mismatch
    (M : PolyDTMCandidate)
    (hFalse : ¬ AcceptsAtDeclaredBound M falseBits)
    (hTrue : AcceptsAtDeclaredBound M trueBits) :
    (semanticDiagonalBits M falseBits = trueBits) ∧
    (semanticDiagonalBits M trueBits = falseBits) ∧
    (¬ SemanticMismatch M falseBits) ∧
    (¬ SemanticMismatch M trueBits) := by
  exact ⟨semanticDiagonal_false_to_true M hFalse,
    semanticDiagonal_true_to_false M hTrue,
    no_mismatch_on_falseBits M hFalse,
    no_mismatch_on_trueBits M hTrue⟩

#print axioms MCore.Real.P02ConstantOrbitAudit.constant_orbit_no_forced_mismatch

end P02ConstantOrbitAudit
end Real
end MCore
