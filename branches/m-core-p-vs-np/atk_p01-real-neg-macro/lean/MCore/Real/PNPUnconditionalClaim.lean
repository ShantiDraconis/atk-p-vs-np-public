import MCore.Real.P01TerminalDelta
import MCore.Real.P02TheoremEnablement

namespace MCore
namespace Real
namespace PNPUnconditionalClaim

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P01TerminalDelta
open P02KleeneBridgeFrontier
open P02TheoremEnablement

/-- Exact no-hypothesis terminal payload for the internal P-versus-NP theorem.
There are no logical assumptions in this structure: both remaining machine
objects must be supplied as concrete data with their proofs. -/
structure UnconditionalClaimCertificate where
  p01_execution : IntegratedExecutionCertificate
  p02_bridge : CandidateCodingBridge

def UnconditionalClaimCertificate.toEnablement
    (C : UnconditionalClaimCertificate) :
    TheoremEnablementCertificate where
  p01 := p01_terminal_gap_closes ⟨C.p01_execution⟩
  bridge := C.p02_bridge

/-- A fully inhabited unconditional certificate closes the internal theorem
with no additional hypotheses. -/
theorem unconditional_certificate_closes_pneqnp
    (C : UnconditionalClaimCertificate) :
    PneqNP :=
  theorem_enablement_closes_pneqnp C.toEnablement

/-- Single normative OPEN_MATH root for an unconditional internal claim. -/
def UnconditionalClaimGap : Prop :=
  Nonempty UnconditionalClaimCertificate

theorem unconditional_claim_gap_closes
    (h : UnconditionalClaimGap) :
    PneqNP := by
  rcases h with ⟨C⟩
  exact unconditional_certificate_closes_pneqnp C

/-- The terminal gap is exactly the conjunction of the two concrete payloads. -/
theorem unconditional_claim_gap_iff :
    UnconditionalClaimGap ↔
      P01TerminalGap ∧ CandidateCodingBridgeGap := by
  constructor
  · rintro ⟨C⟩
    exact ⟨⟨C.p01_execution⟩, ⟨C.p02_bridge⟩⟩
  · rintro ⟨⟨P01⟩, ⟨P02⟩⟩
    exact ⟨{ p01_execution := P01, p02_bridge := P02 }⟩

/-- Minimal normative form: the coding wrapper contributes no extra mathematics.
The unconditional claim is exactly P01 terminal execution plus semantic
self-embedding on the P02 side. -/
theorem unconditional_claim_gap_iff_minimal :
    UnconditionalClaimGap ↔
      P01TerminalGap ∧ P02SemanticSelfEmbedding.SemanticSelfEmbeddingGap := by
  rw [unconditional_claim_gap_iff]
  constructor
  · rintro ⟨hP01, hBridge⟩
    exact ⟨hP01,
      (P02KleeneBridgeFrontier.candidate_coding_bridge_gap_iff_semantic_self_embedding_gap).mp hBridge⟩
  · rintro ⟨hP01, hSemantic⟩
    exact ⟨hP01,
      (P02KleeneBridgeFrontier.candidate_coding_bridge_gap_iff_semantic_self_embedding_gap).mpr hSemantic⟩

#print axioms MCore.Real.PNPUnconditionalClaim.unconditional_claim_gap_iff_minimal
#print axioms MCore.Real.PNPUnconditionalClaim.unconditional_certificate_closes_pneqnp
#print axioms MCore.Real.PNPUnconditionalClaim.unconditional_claim_gap_closes
#print axioms MCore.Real.PNPUnconditionalClaim.unconditional_claim_gap_iff

end PNPUnconditionalClaim
end Real
end MCore
