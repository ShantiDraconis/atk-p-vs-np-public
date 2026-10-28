import MCore.Real.P02DiagonalFrontier

namespace MCore
namespace Real
namespace P02ClockedDiagonalCompiler

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier

/-- The deterministic candidate's declared acceptance bit on one concrete
canonical input. -/
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
      AcceptsAtDeclaredBound M x := by
  rfl

/-- A semantic clocked rejection circuit.  This is deliberately only a
meta-level transformer: it executes the already-total fuel evaluator and emits
a constant circuit with the opposite truth value.  It is not claimed to be a
uniform polynomial-time Cook-Levin compiler. -/
def semanticDiagonalCircuit
    (M : PolyDTMCandidate)
    (x : BitString) : Circuit :=
  .const (!(declaredAcceptBit M x))

def semanticDiagonalBits
    (M : PolyDTMCandidate)
    (x : BitString) : BitString :=
  encodeCircuit (semanticDiagonalCircuit M x)

/-- Every output is a syntactically valid canonical circuit encoding. -/
theorem semanticDiagonalBits_valid
    (M : PolyDTMCandidate)
    (x : BitString) :
    CanonicalSATValid (semanticDiagonalBits M x) := by
  refine ⟨semanticDiagonalCircuit M x, ?_⟩
  exact decodeCircuit_encode _

/-- The semantic transformer has constant encoded output length. -/
theorem semanticDiagonalBits_length
    (M : PolyDTMCandidate)
    (x : BitString) :
    (semanticDiagonalBits M x).length = 3 := by
  unfold semanticDiagonalBits semanticDiagonalCircuit
  cases h : declaredAcceptBit M x <;>
    simp [encodeCircuit]

/-- Exact semantic flip for a fixed supplied input.  This closes the
validity/constant-size/fidelity part of the proposed D(M,d) transformer, but
NOT the self-reference requirement x = D(M,x). -/
theorem semanticDiagonalBits_flip
    (M : PolyDTMCandidate)
    (x : BitString) :
    SATBits circuitBitEncoding (semanticDiagonalBits M x) ↔
      ¬ AcceptsAtDeclaredBound M x := by
  change
    SATBits circuitBitEncoding
        (encodeCircuit (semanticDiagonalCircuit M x)) ↔
      ¬ AcceptsAtDeclaredBound M x
  rw [encoded_sat_equivalence]
  unfold semanticDiagonalCircuit AcceptsAtDeclaredBound declaredAcceptBit
  cases hacc :
      M.accepting
        (M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x)).state <;>
    simp [SATLanguage, evalCircuit, hacc]

/-- If the transformer has a literal fixed point, that fixed point is a genuine
G2.1 diagonal witness.  Existence of such a fixed point remains OPEN_MATH. -/
def witnessOfSemanticFixedPoint
    (M : PolyDTMCandidate)
    (x : BitString)
    (hfix : semanticDiagonalBits M x = x) :
    DiagonalCounterexampleWitness M := by
  refine
    { bits := x
      valid := ?_
      flips := ?_ }
  · simpa [hfix] using semanticDiagonalBits_valid M x
  · simpa [hfix] using semanticDiagonalBits_flip M x

theorem semantic_fixed_point_fails
    (M : PolyDTMCandidate)
    (x : BitString)
    (hfix : semanticDiagonalBits M x = x) :
    ¬ M.CorrectAt (SATBits circuitBitEncoding) x := by
  exact diagonal_witness_fails M (witnessOfSemanticFixedPoint M x hfix)

#print axioms MCore.Real.P02ClockedDiagonalCompiler.semanticDiagonalBits_valid
#print axioms MCore.Real.P02ClockedDiagonalCompiler.semanticDiagonalBits_length
#print axioms MCore.Real.P02ClockedDiagonalCompiler.semanticDiagonalBits_flip
#print axioms MCore.Real.P02ClockedDiagonalCompiler.semantic_fixed_point_fails

end P02ClockedDiagonalCompiler
end Real
end MCore
