import MCore.Real.P02UniversalLowerBound
import MCore.Real.P02FinalCompression

namespace MCore
namespace Real
namespace P02UniversalKernel

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02OperatorKernel
open P02UniversalLowerBound

abbrev SATTarget : BitLanguage :=
  SATBits circuitBitEncoding

/-- Canonical syntactic validity for the fixed SAT encoding. -/
def CanonicalSATValid (x : BitString) : Prop :=
  ∃ phi : CircuitK1.Circuit, decodeCircuit x = some phi

/-- One semantic lower-bound witness against one deterministic candidate. -/
structure SemanticDiagonalWitness (M : PolyDTMCandidate) where
  bits : BitString
  valid : CanonicalSATValid bits
  flip :
    SATTarget bits ↔
      ¬ AcceptsAtDeclaredBound M bits

/-- The semantic flip alone forces a mismatch. -/
theorem SemanticDiagonalWitness.mismatch
    (M : PolyDTMCandidate)
    (W : SemanticDiagonalWitness M) :
    SemanticMismatch M W.bits := by
  apply (semanticMismatch_iff_wrong_yes_or_wrong_no M W.bits).mpr
  by_cases hA : AcceptsAtDeclaredBound M W.bits
  · left
    refine ⟨hA, ?_⟩
    intro hSAT
    exact (W.flip.mp hSAT) hA
  · right
    exact ⟨hA, W.flip.mpr hA⟩

/-- Hence every semantic diagonal witness is a genuine CorrectAt failure. -/
theorem SemanticDiagonalWitness.fails
    (M : PolyDTMCandidate)
    (W : SemanticDiagonalWitness M) :
    FailureAt M W.bits := by
  exact (failureAt_iff_nonhalting_or_mismatch M W.bits).mpr
    (Or.inr (SemanticDiagonalWitness.mismatch M W))

/-- Uniform semantic diagonalization family. This is the exact D3-style
mathematical producer; no endpoint theorem is stored as a field. -/
structure SemanticDiagonalFamily where
  witness : ∀ M : PolyDTMCandidate, SemanticDiagonalWitness M

def SemanticDiagonalFamily.toP02Producer
    (D : SemanticDiagonalFamily) :
    CanonicalSATP02Producer :=
  { counterexample := fun M => (D.witness M).bits
    sound := fun M => SemanticDiagonalWitness.fails M (D.witness M) }

/-- A semantic family closes the universal lower bound. -/
theorem semanticDiagonalFamily_closes_lowerBound
    (D : SemanticDiagonalFamily) :
    UniversalSATLowerBound := by
  intro M
  exact ⟨(D.witness M).bits, SemanticDiagonalWitness.fails M (D.witness M)⟩

theorem semanticDiagonalFamily_closes_notInP
    (D : SemanticDiagonalFamily) :
    ¬ InP SATTarget := by
  exact universalSATLowerBound_iff_notInP.mp
    (semanticDiagonalFamily_closes_lowerBound D)

/-- Pointwise formulation of the exact same semantic producer. -/
def PointwiseSemanticDiagonal : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      CanonicalSATValid x ∧
      (SATTarget x ↔ ¬ AcceptsAtDeclaredBound M x)

theorem semanticFamily_iff_pointwise :
    Nonempty SemanticDiagonalFamily ↔ PointwiseSemanticDiagonal := by
  constructor
  · rintro ⟨D⟩ M
    exact ⟨(D.witness M).bits, (D.witness M).valid, (D.witness M).flip⟩
  · intro h
    classical
    refine ⟨{ witness := fun M => ?_ }⟩
    let x : BitString := Classical.choose (h M)
    have hx :
        CanonicalSATValid x ∧
          (SATTarget x ↔ ¬ AcceptsAtDeclaredBound M x) :=
      Classical.choose_spec (h M)
    exact { bits := x, valid := hx.1, flip := hx.2 }

/-- Pointwise semantic diagonalization is sufficient for the exact P02
operator, with no additional endpoint hypothesis. -/
theorem pointwiseSemanticDiagonal_closes_p02
    (h : PointwiseSemanticDiagonal) :
    Nonempty CanonicalSATP02Producer := by
  rcases semanticFamily_iff_pointwise.mpr h with ⟨D⟩
  exact ⟨D.toP02Producer⟩

/-- Terminal equivalence: the semantic diagonal family is a sufficient
constructive presentation of the universal lower bound. -/
theorem semanticDiagonalFamily_to_final_open_math
    (h : Nonempty SemanticDiagonalFamily) :
    P02FinalCompression.FINAL_OPEN_MATH := by
  rcases h with ⟨D⟩
  exact ⟨D.toP02Producer⟩

/-- Once D3 is supplied, the already-recovered P01 composition closes the
internal endpoint. -/
theorem semanticDiagonalFamily_closes_final
    (hP01 : P02FinalCompression.P01Side)
    (D : SemanticDiagonalFamily) :
    PneqNP := by
  exact P02FinalCompression.final_open_math_closes
    hP01
    ⟨D.toP02Producer⟩

end P02UniversalKernel
end Real
end MCore
