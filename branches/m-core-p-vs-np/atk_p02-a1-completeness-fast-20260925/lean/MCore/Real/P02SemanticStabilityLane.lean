import MCore.Real.P02CookLevinFromBoundedExec
import MCore.Real.P02TableauCompletenessClose
import MCore.Real.P02DiagonalFrontier
import MCore.Real.P02FinalAttack
import MCore.Real.P01FinalCertificate
import MCore.Real.CookNormalizedG3Contract
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace P02SemanticStabilityLane

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02DiagonalFrontier
open P02G21G22Attack
open P02CookLevinFromBoundedExec
open P02TableauCompletenessClose
open P02FinalAttack
open P01FinalCertificate
open CookNormalizedG3Contract
open FinalExternalCertificate

/-- The actual Cook-Levin diagonal transformer used by the third lane. -/
def semanticTransform
    (M : PolyDTMCandidate)
    (x : BitString) : BitString :=
  encodeCircuit (rejectCircuit M x)

/-- Minimal semantic condition needed to transport the Cook-Levin flip from
x to the transformed input T_M(x).  No syntactic fixed point is required. -/
def SemanticStabilityAt
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  AcceptsAtDeclaredBound M (semanticTransform M x) ↔
    AcceptsAtDeclaredBound M x

/-- Third-lane OPEN_MATH producer. -/
def UniformSemanticStabilityProducer : Prop :=
  ∀ M : PolyDTMCandidate, ∃ x : BitString, SemanticStabilityAt M x

/-- Cook-Levin already gives the semantic flip at T_M(x) against M(x). -/
theorem semanticTransform_flip
    (M : PolyDTMCandidate)
    (x : BitString) :
    SATBits circuitBitEncoding (semanticTransform M x) ↔
      ¬ AcceptsAtDeclaredBound M x := by
  simpa [semanticTransform, SATTarget] using
    (rejectCircuit_cook_levin_correct
      boundedExecCorrectness_closed M x)

/-- Semantic stability is exactly what is needed to turn T_M(x) into a genuine
diagonal witness. -/
def witnessOfSemanticStability
    (M : PolyDTMCandidate)
    (x : BitString)
    (hStable : SemanticStabilityAt M x) :
    DiagonalCounterexampleWitness M := by
  refine {
    bits := semanticTransform M x
    valid := ?_
    flips := ?_
  }
  · exact ⟨rejectCircuit M x, decodeCircuit_encode (rejectCircuit M x)⟩
  · have hFlip := semanticTransform_flip M x
    constructor
    · intro hSat
      have hNotX : ¬ AcceptsAtDeclaredBound M x := hFlip.mp hSat
      intro hTx
      exact hNotX (hStable.mp hTx)
    · intro hNotTx
      apply hFlip.mpr
      intro hX
      exact hNotTx (hStable.mpr hX)

/-- Uniform semantic stability produces the existing diagonal family directly. -/
theorem uniformSemanticStability_to_D3
    (h : UniformSemanticStabilityProducer) :
    D3SemanticSelfReference := by
  classical
  refine ⟨{
    witness := fun M =>
      let hx := h M
      let x : BitString := Classical.choose hx
      let hStable : SemanticStabilityAt M x := Classical.choose_spec hx
      witnessOfSemanticStability M x hStable
  }⟩

theorem uniformSemanticStability_closes_P02
    (h : UniformSemanticStabilityProducer) :
    P02TerminalFrontier.P02Target :=
  D3_to_P02Target (uniformSemanticStability_to_D3 h)

/-- Pointwise formulation useful for direct mathematical attack. -/
def SemanticStabilityPointwise (M : PolyDTMCandidate) : Prop :=
  ∃ x : BitString, SemanticStabilityAt M x

theorem producer_iff_pointwise :
    UniformSemanticStabilityProducer ↔
      ∀ M : PolyDTMCandidate, SemanticStabilityPointwise M :=
  Iff.rfl

/-- A one-step orbit collision is stronger than semantic stability. -/
def TransformFixedPointAt
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  semanticTransform M x = x

theorem transformFixedPoint_implies_semanticStability
    (M : PolyDTMCandidate)
    (x : BitString)
    (h : TransformFixedPointAt M x) :
    SemanticStabilityAt M x := by
  unfold TransformFixedPointAt at h
  unfold SemanticStabilityAt
  rw [h]

/-- A two-step orbit collision also yields semantic stability, using the two
Cook-Levin flip equations rather than syntactic equality with x. -/
def TwoStepOrbitCollisionAt
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  semanticTransform M (semanticTransform M x) =
    semanticTransform M x

theorem twoStepOrbitCollision_implies_semanticStability
    (M : PolyDTMCandidate)
    (x : BitString)
    (hCollision : TwoStepOrbitCollisionAt M x) :
    SemanticStabilityAt M x := by
  have h1 := semanticTransform_flip M x
  have h2 := semanticTransform_flip M (semanticTransform M x)
  have hsatEq :
      SATBits circuitBitEncoding
          (semanticTransform M (semanticTransform M x)) ↔
        SATBits circuitBitEncoding (semanticTransform M x) := by
    rw [hCollision]
  have hneg :
      (¬ AcceptsAtDeclaredBound M (semanticTransform M x)) ↔
        (¬ AcceptsAtDeclaredBound M x) := by
    constructor
    · intro hNotTx
      have hSatTT : SATBits circuitBitEncoding
          (semanticTransform M (semanticTransform M x)) :=
        h2.mpr hNotTx
      have hSatT : SATBits circuitBitEncoding (semanticTransform M x) :=
        hsatEq.mp hSatTT
      exact h1.mp hSatT
    · intro hNotX
      have hSatT : SATBits circuitBitEncoding (semanticTransform M x) :=
        h1.mpr hNotX
      have hSatTT : SATBits circuitBitEncoding
          (semanticTransform M (semanticTransform M x)) :=
        hsatEq.mpr hSatT
      exact h2.mp hSatTT
  constructor
  · intro hTx
    by_contra hX
    exact (hneg.mpr hX) hTx
  · intro hX
    by_contra hTx
    exact (hneg.mp hTx) hX

/-- A uniform two-step orbit collision is sufficient for P02. -/
def UniformTwoStepOrbitCollision : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString, TwoStepOrbitCollisionAt M x

theorem uniformTwoStepOrbitCollision_to_stability
    (h : UniformTwoStepOrbitCollision) :
    UniformSemanticStabilityProducer := by
  intro M
  rcases h M with ⟨x, hx⟩
  exact ⟨x, twoStepOrbitCollision_implies_semanticStability M x hx⟩

theorem uniformTwoStepOrbitCollision_closes_P02
    (h : UniformTwoStepOrbitCollision) :
    P02TerminalFrontier.P02Target :=
  uniformSemanticStability_closes_P02
    (uniformTwoStepOrbitCollision_to_stability h)

/-- Final external promotion for the third lane once P01 and semantic stability
are both genuinely inhabited. -/
noncomputable def semanticStability_to_FinalExternalInputs
    (hP01 : SATInNPGap circuitBitEncoding)
    (hStable : UniformSemanticStabilityProducer) :
    FinalExternalInputs :=
  assembleFinalExternal
    hP01
    (uniformSemanticStability_to_D3 hStable)
    cookNormalizedExternalContract

theorem semanticStability_closes_FinalExternal
    (hP01 : SATInNPGap circuitBitEncoding)
    (hStable : UniformSemanticStabilityProducer) :
    FailProofAllGaps.OfficialPneqNP
      cookNormalizedExternalContract.selection.model.P
      cookNormalizedExternalContract.selection.model.NP :=
  final_external_certificate
    (semanticStability_to_FinalExternalInputs hP01 hStable)

/-- Exact third-lane terminal OPEN_MATH. -/
def OPEN_MATH_SEMANTIC_STABILITY : Prop :=
  UniformSemanticStabilityProducer

#print axioms MCore.Real.P02SemanticStabilityLane.semanticTransform_flip
#print axioms MCore.Real.P02SemanticStabilityLane.witnessOfSemanticStability
#print axioms MCore.Real.P02SemanticStabilityLane.uniformSemanticStability_to_D3
#print axioms MCore.Real.P02SemanticStabilityLane.uniformSemanticStability_closes_P02
#print axioms MCore.Real.P02SemanticStabilityLane.transformFixedPoint_implies_semanticStability
#print axioms MCore.Real.P02SemanticStabilityLane.twoStepOrbitCollision_implies_semanticStability
#print axioms MCore.Real.P02SemanticStabilityLane.uniformTwoStepOrbitCollision_closes_P02
#print axioms MCore.Real.P02SemanticStabilityLane.semanticStability_closes_FinalExternal

end P02SemanticStabilityLane
end Real
end MCore
