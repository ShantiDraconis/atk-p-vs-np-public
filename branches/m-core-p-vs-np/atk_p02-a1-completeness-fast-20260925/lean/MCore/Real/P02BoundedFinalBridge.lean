import MCore.Real.P02BoundedSemanticInput
import MCore.Real.P02CookLevinFromBoundedExec
import MCore.Real.P02TableauCompletenessClose
import MCore.Real.P02FinalAttack
import MCore.Real.P01FinalCertificate
import MCore.Real.CookNormalizedG3Contract
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace P02BoundedFinalBridge

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02G21G22Attack
open P02BoundedSemanticInput
open P02CookLevinFromBoundedExec
open P02TableauCompletenessClose
open P02FinalAttack
open P01FinalCertificate
open CookNormalizedG3Contract
open FinalExternalCertificate

/-- One finite-fuel same-input witness for one polynomial DTM candidate.

This is the exact bounded object needed to turn the computable finite observation
`selfInputFuel` into a genuine semantic diagonal witness.  No claim that such
an object exists is built into the definition. -/
structure BoundedSameInputWitness (M : PolyDTMCandidate) where
  fuel : Nat
  code : Nat.Partrec.Code
  same_input :
    selfInputFuel fuel code =
      encodeCircuit (rejectCircuit M (selfInputFuel fuel code))

/-- Uniform bounded producer.  This is the only global lifting premise in this
lane.  It is intentionally explicit: finite-fuel decidability alone does not
inhabit this proposition. -/
def UniformBoundedSameInputProducer : Prop :=
  ∀ M : PolyDTMCandidate, Nonempty (BoundedSameInputWitness M)

/-- Every genuine bounded same-input witness yields a semantic diagonal
counterexample for the same candidate. -/
def BoundedSameInputWitness.toDiagonalWitness
    (M : PolyDTMCandidate)
    (W : BoundedSameInputWitness M) :
    DiagonalCounterexampleWitness M := by
  let y : BitString := selfInputFuel W.fuel W.code
  let x : BitString := encodeCircuit (rejectCircuit M y)
  have hxy : y = x := by
    simpa [x, y] using W.same_input
  refine {
    bits := x
    valid := ?_
    flips := ?_
  }
  · exact ⟨rejectCircuit M y,
      decodeCircuit_encode (rejectCircuit M y)⟩
  · have hCL :
        SATTarget x ↔ ¬ AcceptsAtDeclaredBound M y := by
      simpa only [x] using
        (rejectCircuit_cook_levin_correct
          boundedExecCorrectness_closed M y)
    rw [hxy] at hCL
    simpa [SATTarget] using hCL

/-- The uniform bounded same-input producer is sufficient for the exact D3
semantic self-reference object. -/
theorem uniformBoundedSameInput_to_D3
    (h : UniformBoundedSameInputProducer) :
    D3SemanticSelfReference := by
  classical
  refine ⟨{
    witness := fun M =>
      BoundedSameInputWitness.toDiagonalWitness M
        (Classical.choice (h M))
  }⟩

/-- Hence the bounded producer closes the exact P02 target, with no separate
literal fixed-point assumption. -/
theorem uniformBoundedSameInput_closes_P02
    (h : UniformBoundedSameInputProducer) :
    P02TerminalFrontier.P02Target :=
  D3_to_P02Target (uniformBoundedSameInput_to_D3 h)

/-- Internal P != NP endpoint once the existing P01 producer and the bounded
same-input producer are both supplied. -/
theorem boundedProducer_P01_closes_internal
    (hP01 : SATInNPGap circuitBitEncoding)
    (hBounded : UniformBoundedSameInputProducer) :
    PneqNP :=
  P01_D3_to_internal_final hP01
    (uniformBoundedSameInput_to_D3 hBounded)

/-- External three-producer payload assembled from P01, the bounded same-input
producer, and the already-existing normalized G3 contract. -/
noncomputable def boundedProducer_to_FinalExternalInputs
    (hP01 : SATInNPGap circuitBitEncoding)
    (hBounded : UniformBoundedSameInputProducer) :
    FinalExternalInputs :=
  assembleFinalExternal
    hP01
    (uniformBoundedSameInput_to_D3 hBounded)
    cookNormalizedExternalContract

/-- Final external certificate endpoint for the bounded lane. -/
theorem boundedProducer_closes_FinalExternal
    (hP01 : SATInNPGap circuitBitEncoding)
    (hBounded : UniformBoundedSameInputProducer) :
    FailProofAllGaps.OfficialPneqNP
      cookNormalizedExternalContract.selection.model.P
      cookNormalizedExternalContract.selection.model.NP :=
  final_external_certificate
    (boundedProducer_to_FinalExternalInputs hP01 hBounded)

/-- Exact final-proof frontier for this lane.  P01 is separated from the
bounded-to-global lifting object so CI can certify each independently. -/
def BoundedFinalProofInputs : Prop :=
  P01ConstructionGap ∧ UniformBoundedSameInputProducer

theorem boundedFinalProofInputs_closes_FinalExternalGap
    (h : BoundedFinalProofInputs) :
    FinalExternalGap := by
  rcases h with ⟨hP01, hBounded⟩
  have hG1 : SATInNPGap circuitBitEncoding :=
    construction_closes_p01 hP01
  exact ⟨boundedProducer_to_FinalExternalInputs hG1 hBounded⟩

#print axioms MCore.Real.P02BoundedFinalBridge.BoundedSameInputWitness.toDiagonalWitness
#print axioms MCore.Real.P02BoundedFinalBridge.uniformBoundedSameInput_to_D3
#print axioms MCore.Real.P02BoundedFinalBridge.uniformBoundedSameInput_closes_P02
#print axioms MCore.Real.P02BoundedFinalBridge.boundedProducer_P01_closes_internal
#print axioms MCore.Real.P02BoundedFinalBridge.boundedProducer_closes_FinalExternal
#print axioms MCore.Real.P02BoundedFinalBridge.boundedFinalProofInputs_closes_FinalExternalGap

end P02BoundedFinalBridge
end Real
end MCore
