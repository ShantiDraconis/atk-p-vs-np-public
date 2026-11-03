import MCore.Real.P01FinalCertificate
import MCore.Real.P02G21G22Attack

namespace MCore
namespace Real
namespace FinalProofEvidencePromotion

open CanonicalFinalProof
open P01FinalCertificate
open P02G21G22Attack

/-- Research-evidence lanes accepted by the FINAL_PROOF audit layer.
These labels carry no proof content by themselves. -/
inductive EvidenceLane where
  | prime2
  | horizonPrime
  | g21Semantic
  | p01Physical
  | complexityBounds
  | encodingInvariants
  | negativeResults
  | geometricP012
  | certificateProvenance
  | externalSource
  deriving DecidableEq, Repr, BEq

/-- Status of a collected item before any mathematical promotion. -/
inductive EvidenceStatus where
  | observed
  | supported
  | falsified
  | inconclusive
  | greenSource
  | openMath
  deriving DecidableEq, Repr, BEq

/-- Typed metadata accepted from the research-evidence registry.
No Prop-valued mathematical claim is stored here: evidence cannot become a
proof merely by being registered. -/
structure EvidenceRecord where
  evidenceId : String
  lane : EvidenceLane
  status : EvidenceStatus
  claim : String
  exactScope : String
  sourceRepository : String
  sourceSha : String
  sourcePath : String
  workflowRun : Option Nat
  notes : String
  deriving Repr

/-- Promotion gate for G21.
An evidence item is relevant to the real pointwise frontier only when accompanied
by a kernel term of the exact existing G21Pointwise proposition. -/
structure G21EvidencePromotion where
  evidence : EvidenceRecord
  exactTarget : G21Pointwise

/-- Promotion gate for P01.
Evidence about parsers, physical machines, bounds, traces, or encodings receives
P01 proof credit only when it constructs the exact concrete machine payload. -/
structure P01EvidencePromotion where
  evidence : EvidenceRecord
  construction : P01MachineConstruction

/-- Accepted evidence can close G21 only through an exact proof term. -/
theorem evidence_to_g21
    (E : G21EvidencePromotion) :
    G21Pointwise :=
  E.exactTarget

/-- Accepted evidence can close the P01 implementation gap only through an
actual P01MachineConstruction. -/
theorem evidence_to_p01ConstructionGap
    (E : P01EvidencePromotion) :
    P01ConstructionGap :=
  ⟨E.construction⟩

/-- The P01 evidence path then uses the existing canonical promotion theorem. -/
theorem evidence_to_p01
    (E : P01EvidencePromotion) :
    CanonicalSATNTMAttack.CanonicalSATMachineClosure :=
  construction_closes_p01 (evidence_to_p01ConstructionGap E)

/-- Combined evidence closure contains both real producers, not proxy labels. -/
structure FinalProofEvidenceClosure where
  p01 : P01EvidencePromotion
  g21 : G21EvidencePromotion

theorem evidenceClosure_real_gaps
    (E : FinalProofEvidenceClosure) :
    P01ConstructionGap ∧ G21Pointwise :=
  ⟨evidence_to_p01ConstructionGap E.p01, evidence_to_g21 E.g21⟩

/-- Once both exact producers are present, reuse the existing internal endpoint
consumer.  Evidence metadata itself contributes no mathematical assumption. -/
theorem evidenceClosure_closes_internal
    (E : FinalProofEvidenceClosure) :
    PneqNP := by
  exact P02G21G22Attack.p01_g21_closes_internal
    (construction_closes_p01 (evidence_to_p01ConstructionGap E.p01))
    (evidence_to_g21 E.g21)

/-
FAIL-CLOSED:
There is intentionally no theorem EvidenceRecord -> G21Pointwise and no theorem
EvidenceRecord -> P01ConstructionGap.  The two promotion structures require the
exact missing kernel objects.
-/

#print axioms MCore.Real.FinalProofEvidencePromotion.evidence_to_g21
#print axioms MCore.Real.FinalProofEvidencePromotion.evidence_to_p01ConstructionGap
#print axioms MCore.Real.FinalProofEvidencePromotion.evidenceClosure_real_gaps
#print axioms MCore.Real.FinalProofEvidencePromotion.evidenceClosure_closes_internal

end FinalProofEvidencePromotion
end Real
end MCore
