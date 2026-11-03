import Mathlib
import MCore.Real.OpenMathUniversalSeparationLaw
import MCore.Real.OpenMathCore.SelfQuotation
import MCore.Real.OpenMathCore.BoundedUniversalSimulation
import MCore.Real.OpenMathCore.SATCircuitCompiler
import MCore.Real.OpenMathCore.SameInputClosure
import MCore.Real.OpenMathCore.TerminalArchitecture
import MCore.Real.P02CandidateCodingFrontier
import MCore.Real.P02DiagonalCompilerFrontierV2
import MCore.Real.P02ClockedDiagonalCompiler

namespace MCore
namespace Real
namespace SemanticSelfQuotation

open Set Filter
open scoped Topology
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02UniversalFailureAlgebra
open P02CandidateCodingFrontier
open P02DiagonalCompilerFrontierV2
open P02ClockedDiagonalCompiler
open OpenMathCore
open OpenMathUniversalSeparationLaw

/-- Concrete auxiliary geometry: closed interval [0,1], midpoint 1/2,
contraction factor 1/2. -/
def geometricContraction :
    Contraction midpointMap midpoint (1 / 2) :=
  midpointMap_contraction

def geometricRepelPull :
    RepelAndPull midpointMap midpoint :=
  midpointMap_repelPull

def geometricRatioLaw :
    RatioTendsToOne ratioX ratioY :=
  ratioLaw

/-- The candidate-code layer. This remains parametric until an actual coding
interface is inhabited. -/
structure CandidateCodeLayer where
  coding : CandidateCodingInterface

def CandidateCodeLayer.code
    (C : CandidateCodeLayer) :
    PolyDTMCandidate → BitString :=
  C.coding.encode

theorem CandidateCodeLayer.code_injective
    (C : CandidateCodeLayer) :
    Function.Injective C.code :=
  P02CandidateCodingFrontier.encode_injective C.coding

/-- Semantic self-quotation does not require literal bitwise fixed points.
It asks directly for a canonical SAT instance whose semantics negate the
candidate on that very same bitstring. -/
structure SemanticSelfQuotation where
  codeLayer : CandidateCodeLayer
  quoteCircuit : PolyDTMCandidate → CircuitK1.Circuit
  quoteBits : PolyDTMCandidate → BitString
  quoteBits_eq :
    ∀ M, quoteBits M = encodeCircuit (quoteCircuit M)
  valid :
    ∀ M, CanonicalSATValid (quoteBits M)
  same_input_exact :
    ∀ M,
      SATBits circuitBitEncoding (quoteBits M) ↔
        ¬ AcceptsAtDeclaredBound M (quoteBits M)

def SemanticSelfQuotation.toSameInputClosure
    (Q : SemanticSelfQuotation) :
    SameInputClosure where
  witness := Q.quoteBits
  valid := Q.valid
  simulation_exact := Q.same_input_exact

def SemanticSelfQuotation.toDiagonalCompilerV2
    (Q : SemanticSelfQuotation) :
    DiagonalCompilerV2 :=
  Q.toSameInputClosure.toDiagonalCompilerV2

theorem SemanticSelfQuotation.givesMismatch
    (Q : SemanticSelfQuotation)
    (M : PolyDTMCandidate) :
    SemanticMismatch M (Q.quoteBits M) := by
  exact sameInputClosure_gives_mismatch Q.toSameInputClosure M

theorem SemanticSelfQuotation.closesT5F
    (Q : SemanticSelfQuotation) :
    T5FCore := by
  intro M _
  exact ⟨Q.quoteBits M, Q.givesMismatch M⟩

theorem SemanticSelfQuotation.closesG21
    (Q : SemanticSelfQuotation) :
    P02G21G22Attack.G21Pointwise := by
  exact T5FCore_implies_G21 Q.closesT5F

theorem SemanticSelfQuotation.closesP02
    (Q : SemanticSelfQuotation) :
    P02TerminalFrontier.P02Target := by
  exact T5FCore_implies_P02 Q.closesT5F

/-- The currently available clocked diagonal transformer is pointwise:
for each supplied x it builds a valid constant-size circuit that flips M(x).
This is not yet self-quotation on the same input. -/
theorem clockedDiagonal_pointwise
    (M : PolyDTMCandidate)
    (x : BitString) :
    CanonicalSATValid (semanticDiagonalBits M x) ∧
    (semanticDiagonalBits M x).length = 3 ∧
    (SATBits circuitBitEncoding (semanticDiagonalBits M x) ↔
      ¬ AcceptsAtDeclaredBound M x) := by
  exact ⟨
    semanticDiagonalBits_valid M x,
    semanticDiagonalBits_length M x,
    semanticDiagonalBits_flip M x
  ⟩

/-- A literal fixed point remains only a sufficient special case and is not
used in SemanticSelfQuotation. -/
theorem literalFixedPoint_is_sufficient
    (M : PolyDTMCandidate)
    (x : BitString)
    (hfix : semanticDiagonalBits M x = x) :
    SemanticMismatch M x := by
  exact semanticDiagonal_fixedPoint_gives_mismatch M x hfix

/-- Exact terminal gap: existence of this object is equivalent in strength to
having a same-input diagonal witness producer. No inhabitant is asserted. -/
def SemanticSelfQuotationGap : Prop :=
  Nonempty SemanticSelfQuotation

theorem semanticSelfQuotationGap_implies_T5F
    (h : SemanticSelfQuotationGap) :
    T5FCore := by
  rcases h with ⟨Q⟩
  exact Q.closesT5F

#print axioms MCore.Real.SemanticSelfQuotation.geometricContraction
#print axioms MCore.Real.SemanticSelfQuotation.geometricRepelPull
#print axioms MCore.Real.SemanticSelfQuotation.geometricRatioLaw
#print axioms MCore.Real.SemanticSelfQuotation.SemanticSelfQuotation.closesT5F
#print axioms MCore.Real.SemanticSelfQuotation.SemanticSelfQuotation.closesG21
#print axioms MCore.Real.SemanticSelfQuotation.SemanticSelfQuotation.closesP02
#print axioms MCore.Real.SemanticSelfQuotation.semanticSelfQuotationGap_implies_T5F

end SemanticSelfQuotation
end Real
end MCore
