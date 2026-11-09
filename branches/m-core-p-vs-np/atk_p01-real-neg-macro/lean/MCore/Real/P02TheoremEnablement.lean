import MCore.Real.P02SupportBundle

namespace MCore
namespace Real
namespace P02TheoremEnablement

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02SupportBundle
open P02KleeneBridgeFrontier

/-- Terminal activation certificate for the current internal theorem route.
It contains exactly the two positive payloads required by the already-proved
transport: canonical SAT in NP (P01) and the single remaining P02 bridge.
No external theorem is asserted by this structure alone. -/
structure TheoremEnablementCertificate where
  p01 : SATInNPGap circuitBitEncoding
  bridge : CandidateCodingBridge

def TheoremEnablementCertificate.toSupportBundle
    (C : TheoremEnablementCertificate) :
    SupportBundle :=
  { bridge := C.bridge }

def TheoremEnablementCertificate.toP02Target
    (C : TheoremEnablementCertificate) :
    P02TerminalFrontier.P02Target :=
  C.toSupportBundle.toP02Target

theorem theorem_enablement_closes_pneqnp
    (C : TheoremEnablementCertificate) :
    PneqNP := by
  exact support_bundle_closes_internal C.p01 C.toSupportBundle

/-- Exact final activation gap.  All wiring after these payloads is GREEN. -/
def TheoremEnablementGap : Prop :=
  Nonempty TheoremEnablementCertificate

theorem theorem_enablement_gap_closes
    (h : TheoremEnablementGap) :
    PneqNP := by
  rcases h with ⟨C⟩
  exact theorem_enablement_closes_pneqnp C

/-- P02-side activation remains exactly the candidate-coding bridge gap. -/
theorem p02_activation_iff_candidate_coding_bridge :
    SupportBundleGap ↔ CandidateCodingBridgeGap :=
  support_bundle_gap_iff_candidate_coding_bridge_gap

#print axioms MCore.Real.P02TheoremEnablement.theorem_enablement_closes_pneqnp
#print axioms MCore.Real.P02TheoremEnablement.theorem_enablement_gap_closes
#print axioms MCore.Real.P02TheoremEnablement.p02_activation_iff_candidate_coding_bridge

end P02TheoremEnablement
end Real
end MCore
