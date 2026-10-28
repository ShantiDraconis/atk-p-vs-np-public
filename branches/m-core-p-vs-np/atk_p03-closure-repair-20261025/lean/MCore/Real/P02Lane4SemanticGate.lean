import MCore.Real.Claim1To7Only
import MCore.Real.P02UniversalLowerBoundMaster

namespace MCore
namespace Real
namespace P02Lane4SemanticGate

open Claim1To7Only
open P02UniversalLowerBoundMaster

/-- Reused seven-claim aggregate candidate. -/
abbrev CandidateRoot : Prop :=
  Claim1To7Evidence
    MCore.Real.SevenCertificateBridge.canonicalSevenEndpoint

/-- Official P02 lower-bound target in the current repository. -/
abbrev OfficialTarget : Prop :=
  UNIVERSAL_LOWER_BOUND

/-- Exact T10 obligation: the reused claim bundle must imply the official target. -/
abbrev T10SemanticBridge : Prop :=
  CandidateRoot → OfficialTarget

theorem candidateRoot_inhabited : CandidateRoot :=
  canonicalClaim1To7

/-- Because CandidateRoot is already inhabited, any semantic bridge out of it
is exactly as strong as the official lower-bound target. This prevents a
wrapper-only promotion from hiding the remaining mathematical obligation. -/
theorem t10SemanticBridge_iff_officialTarget :
    T10SemanticBridge ↔ OfficialTarget := by
  constructor
  · intro h
    exact h candidateRoot_inhabited
  · intro h _
    exact h

/-- If T10 is supplied, it closes the current exact P02 lower bound. -/
theorem t10_closes_official_target
    (h : T10SemanticBridge) :
    OfficialTarget :=
  (t10SemanticBridge_iff_officialTarget.mp h)

/-- The official target remains definitionally the repository's canonical
SAT-not-in-P statement through the already-certified master equivalence. -/
theorem officialTarget_iff_sat_not_in_p :
    OfficialTarget ↔
      ¬ MCore.Real.CanonicalFinalProof.InP
        (MCore.Real.CanonicalSATBoundary.SATBits
          MCore.Real.CanonicalCircuitBits.circuitBitEncoding) :=
  universal_lower_bound_iff_not_in_p

#print axioms MCore.Real.P02Lane4SemanticGate.candidateRoot_inhabited
#print axioms MCore.Real.P02Lane4SemanticGate.t10SemanticBridge_iff_officialTarget
#print axioms MCore.Real.P02Lane4SemanticGate.t10_closes_official_target
#print axioms MCore.Real.P02Lane4SemanticGate.officialTarget_iff_sat_not_in_p

end P02Lane4SemanticGate
end Real
end MCore
