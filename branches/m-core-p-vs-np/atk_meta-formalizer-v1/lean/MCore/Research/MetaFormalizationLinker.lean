import MCore.Real.P01FinalCertificate
import MCore.Real.P02G21G22Attack
import MCore.Real.FinalExternalCertificate
import MCore.Real.FinalProofEvidencePromotion

namespace MCore
namespace Research
namespace MetaFormalizationLinker

open Real

inductive Area where
  | p01
  | p02
  | g3
  | finalExternal
  | research
  deriving DecidableEq, Repr, BEq

inductive EvidenceClass where
  | source
  | pattern
  | kernelGreen
  | frozen
  | certified
  | falsified
  deriving DecidableEq, Repr, BEq

structure EvidenceNode where
  area : Area
  cls : EvidenceClass
  source : String
  note : String
  deriving Repr

/-- Metadata and repeated patterns carry no proof credit by themselves. -/
def EvidenceNode.proofCredit (e : EvidenceNode) : Nat :=
  match e.cls with
  | .kernelGreen | .frozen | .certified => 0
  | _ => 0

/-- Exact P01 promotion boundary. -/
structure P01Promotion where
  evidence : EvidenceNode
  exact : Real.P01FinalCertificate.P01MachineConstruction

/-- Exact P02 promotion boundary. -/
structure P02Promotion where
  evidence : EvidenceNode
  exact : Real.FailProofAllGaps.FailureGenerator
    (Real.CanonicalSATBoundary.SATBits
      Real.CanonicalCircuitBits.circuitBitEncoding)

/-- Exact external promotion boundary. -/
structure ExternalPromotion where
  p01 : P01Promotion
  p02 : P02Promotion
  g3 : Real.G3ModelMatch.G3ExternalContract

def ExternalPromotion.toInputs (E : ExternalPromotion) :
    Real.FinalExternalCertificate.FinalExternalInputs where
  g1 := Real.P01FinalCertificate.construction_closes_p01 ⟨E.p01.exact⟩
  g2 := E.p02.exact
  g3 := E.g3

theorem exact_external_promotion
    (E : ExternalPromotion) :
    Real.FailProofAllGaps.OfficialPneqNP
      E.g3.selection.model.P
      E.g3.selection.model.NP := by
  exact Real.FinalExternalCertificate.final_external_certificate E.toInputs

/-
There is intentionally no theorem:
  EvidenceNode -> P01MachineConstruction
  EvidenceNode -> FailureGenerator
  repeated pattern -> exact producer
Only exact kernel terms cross promotion boundaries.
-/

#print axioms MCore.Research.MetaFormalizationLinker.exact_external_promotion

end MetaFormalizationLinker
end Research
end MCore
