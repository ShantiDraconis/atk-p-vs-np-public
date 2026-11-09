import MCore.Real.P02KleeneBridgeFrontier
import MCore.Real.P02G21G22Attack
import MCore.Real.P02CanonicalNormalization
import MCore.Real.P02OpenMathClosure

namespace MCore
namespace Real
namespace P02SupportBundle

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02TerminalFrontier
open P02KleeneBridgeFrontier

/-- Canonical support bundle for the current P02 route.
All intermediate transport theorems already exist; the only mathematical
payload retained here is the candidate-coding/self-reference bridge. -/
structure SupportBundle where
  bridge : CandidateCodingBridge

def SupportBundle.toP02Target
    (S : SupportBundle) :
    P02Target :=
  candidate_coding_bridge_closes_p02 ⟨S.bridge⟩

theorem support_bundle_closes_internal
    (hP01 : SATInNPGap circuitBitEncoding)
    (S : SupportBundle) :
    PneqNP := by
  exact p01_p02_close_internal_separation hP01 S.toP02Target

/-- Exact compressed blocker: no duplicated lower-bound notion. -/
def SupportBundleGap : Prop :=
  Nonempty SupportBundle

theorem support_bundle_gap_iff_candidate_coding_bridge_gap :
    SupportBundleGap ↔ CandidateCodingBridgeGap := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.bridge⟩
  · rintro ⟨B⟩
    exact ⟨{ bridge := B }⟩

theorem support_bundle_gap_closes_p02
    (h : SupportBundleGap) :
    P02Target := by
  rcases h with ⟨S⟩
  exact S.toP02Target

theorem support_bundle_gap_enables_pneqnp
    (hP01 : SATInNPGap circuitBitEncoding)
    (h : SupportBundleGap) :
    PneqNP := by
  rcases h with ⟨S⟩
  exact support_bundle_closes_internal hP01 S

#print axioms MCore.Real.P02SupportBundle.support_bundle_gap_iff_candidate_coding_bridge_gap
#print axioms MCore.Real.P02SupportBundle.support_bundle_gap_closes_p02
#print axioms MCore.Real.P02SupportBundle.support_bundle_gap_enables_pneqnp

end P02SupportBundle
end Real
end MCore
