import MCore.Real.P02RejectionImageEscape
import MCore.Real.P02UserFinalClosureProbe
import MCore.Real.P02RPADualConfirmation
import MCore.Real.P02EndpointLattice
import MCore.Real.P02EndpointLatticeCube
import MCore.Real.P02CandidateCodeFixedPointCounterprobe

namespace MCore
namespace Real
namespace P02UnifiedTheory

open CanonicalFinalProof
open P02RejectionImageEscape
open P02UserFinalClosureProbe
open P02RPADualConfirmation
open P02EndpointLattice
open P02EndpointLatticeCube
open P02CandidateCodeFixedPointCounterprobe

/-- Dense structural certificate: the terminal aliases are one proposition. -/
theorem terminal_signature_unified :
    (P02RejectionImageEscape.Endpoint ↔ P02RejectionImageEscape.Gap) ∧
    (P02RejectionImageEscape.Gap ↔ P02RejectionImageEscape.Habitant) ∧
    (P02RejectionImageEscape.Habitant ↔ P02RejectionImageEscape.Inhabitant) ∧
    (P02RejectionImageEscape.Inhabitant ↔ P02RejectionImageEscape.Endpoint) :=
  P02RejectionImageEscape.terminal_cycle

/-- Dense RPA certificate: a complete dual endpoint transition is exactly
an inhabitant of the active endpoint. -/
theorem rpa_unified :
    P02RPADualConfirmation.ActiveRPA ↔
      P02RejectionImageEscape.Endpoint :=
  P02RPADualConfirmation.activeRPA_nonempty_iff_endpoint

/-- Dense lattice certificate: all 14 ordered states through length three
are present in one finite registry. -/
theorem lattice_cube_14 :
    cube14.length = 14 :=
  cube14_length

/-- FULL is the canonical image of OPEN+OPEN+CLOSED+CLOSED. -/
theorem full_word_closes_lattice :
    canonicalize (evalWord W_FULL4) = FULL :=
  full4_canonicalizes_full

/-- FULL carries exactly the external-certificate payload, without creating
that payload. -/
theorem full_certificate_exact :
    Nonempty P02EndpointLatticeCube.FullWordCertificate ↔
      P02RPADualConfirmation.GLOBAL_EXTERNAL_CERTIFICATE :=
  P02EndpointLatticeCube.fullWordCertificate_iff_globalExternal

/-- Publication root: an actual external certificate closes the canonical
P-vs-NP root. -/
theorem external_certificate_closes_pneqnp
    (h : P02RPADualConfirmation.GLOBAL_EXTERNAL_CERTIFICATE) :
    PneqNP :=
  P02RPADualConfirmation.global_external_closes_pneqnp h

/-- Counterprobe result: the special candidateCode fixed-point route is not
a valid universal producer. -/
theorem candidate_code_shortcut_blocked :
    ¬ P02DiagonalNoShortcut.CandidateCodeSemanticFixedPoint :=
  candidateCodeSemanticFixedPoint_refuted

/-- Exact material frontier retained after all structural compression. -/
abbrev MATERIAL_ENDPOINT : Prop := RejectImageEscape

theorem material_endpoint_iff_antiAlternation :
    MATERIAL_ENDPOINT ↔
      P02SemanticSelfSubstitution.TotalClockAntiAlternation :=
  rejectImageEscape_iff_totalClockAntiAlternation

#print axioms MCore.Real.P02UnifiedTheory.terminal_signature_unified
#print axioms MCore.Real.P02UnifiedTheory.rpa_unified
#print axioms MCore.Real.P02UnifiedTheory.lattice_cube_14
#print axioms MCore.Real.P02UnifiedTheory.full_word_closes_lattice
#print axioms MCore.Real.P02UnifiedTheory.full_certificate_exact
#print axioms MCore.Real.P02UnifiedTheory.external_certificate_closes_pneqnp
#print axioms MCore.Real.P02UnifiedTheory.candidate_code_shortcut_blocked
#print axioms MCore.Real.P02UnifiedTheory.material_endpoint_iff_antiAlternation

end P02UnifiedTheory
end Real
end MCore
