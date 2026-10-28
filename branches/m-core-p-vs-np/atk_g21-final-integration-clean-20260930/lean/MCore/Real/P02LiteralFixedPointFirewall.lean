import MCore.Real.P02ClockedDiagonalCompiler

namespace MCore
namespace Real
namespace P02LiteralFixedPointFirewall

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02ClockedDiagonalCompiler

def falseBits : BitString := encodeCircuit (.const false)
def trueBits : BitString := encodeCircuit (.const true)

/-- The current semantic diagonal transformer can emit only the two constant
circuit encodings. -/
theorem semanticDiagonalBits_cases
    (M : PolyDTMCandidate)
    (x : BitString) :
    semanticDiagonalBits M x = falseBits ∨
      semanticDiagonalBits M x = trueBits := by
  unfold semanticDiagonalBits semanticDiagonalCircuit falseBits trueBits
  cases h : declaredAcceptBit M x <;>
    simp [h, encodeCircuit]

/-- Both constant encodings are canonical SAT inputs with the expected truth
values. -/
theorem falseBits_not_sat :
    ¬ SATBits circuitBitEncoding falseBits := by
  rw [show falseBits = encodeCircuit (.const false) by rfl]
  rw [encoded_sat_equivalence]
  simp [SATLanguage, evalCircuit]

theorem trueBits_sat :
    SATBits circuitBitEncoding trueBits := by
  rw [show trueBits = encodeCircuit (.const true) by rfl]
  rw [encoded_sat_equivalence]
  simp [SATLanguage, evalCircuit]

/-- Fail-proof for the naive literal fixed-point route.

A deterministic candidate that is CorrectAt on just the two constant
encodings cannot have a literal fixed point x = semanticDiagonalBits M x.
Thus the constant-output semantic transformer cannot be the universal G2.1
producer; a genuine self-reference/compiler construction must contain more
structure than this two-point map. -/
theorem no_literal_fixed_point_if_constants_correct
    (M : PolyDTMCandidate)
    (hFalse :
      M.CorrectAt (SATBits circuitBitEncoding) falseBits)
    (hTrue :
      M.CorrectAt (SATBits circuitBitEncoding) trueBits) :
    ¬ ∃ x : BitString, semanticDiagonalBits M x = x := by
  rintro ⟨x, hfix⟩
  have hfail :
      ¬ M.CorrectAt (SATBits circuitBitEncoding) x :=
    semantic_fixed_point_fails M x hfix
  rcases semanticDiagonalBits_cases M x with hF | hT
  · have hx : x = falseBits := by
      calc
        x = semanticDiagonalBits M x := hfix.symm
        _ = falseBits := hF
    exact hfail (by simpa [hx] using hFalse)
  · have hx : x = trueBits := by
      calc
        x = semanticDiagonalBits M x := hfix.symm
        _ = trueBits := hT
    exact hfail (by simpa [hx] using hTrue)

#print axioms MCore.Real.P02LiteralFixedPointFirewall.semanticDiagonalBits_cases
#print axioms MCore.Real.P02LiteralFixedPointFirewall.falseBits_not_sat
#print axioms MCore.Real.P02LiteralFixedPointFirewall.trueBits_sat
#print axioms MCore.Real.P02LiteralFixedPointFirewall.no_literal_fixed_point_if_constants_correct

end P02LiteralFixedPointFirewall
end Real
end MCore
