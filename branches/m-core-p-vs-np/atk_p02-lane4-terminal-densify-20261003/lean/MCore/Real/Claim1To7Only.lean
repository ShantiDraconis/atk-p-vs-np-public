import MCore.Real.BridgeSeven

namespace MCore.Real.Claim1To7Only

open MCore.Real.SevenCertificateBridge

abbrev Claim1 (ep : SevenEndpoint) : Prop := cert_1b7ce6f8 ep
abbrev Claim2 (ep : SevenEndpoint) : Prop := cert_24464291 ep
abbrev Claim3 (ep : SevenEndpoint) : Prop := cert_f0a9fcd1 ep
abbrev Claim4 (ep : SevenEndpoint) : Prop := cert_519e6868 ep
abbrev Claim5 (ep : SevenEndpoint) : Prop := cert_003dd377 ep
abbrev Claim6 (ep : SevenEndpoint) : Prop := cert_7732c120 ep
abbrev Claim7 (ep : SevenEndpoint) : Prop := cert_45bf2597 ep

structure Claim1To7Evidence (ep : SevenEndpoint) : Prop where
  claim1 : Claim1 ep
  claim2 : Claim2 ep
  claim3 : Claim3 ep
  claim4 : Claim4 ep
  claim5 : Claim5 ep
  claim6 : Claim6 ep
  claim7 : Claim7 ep

theorem canonicalClaim1To7 :
    Claim1To7Evidence canonicalSevenEndpoint := by
  exact ⟨
    canonicalSevenGreenEvidence.cert_1b7ce6f8,
    canonicalSevenGreenEvidence.cert_24464291,
    canonicalSevenGreenEvidence.cert_f0a9fcd1,
    canonicalSevenGreenEvidence.cert_519e6868,
    canonicalSevenGreenEvidence.cert_003dd377,
    canonicalSevenGreenEvidence.cert_7732c120,
    canonicalSevenGreenEvidence.cert_45bf2597
  ⟩

/-- Claim-only external certificate: exactly the seven kernel-checked claims. -/
abbrev EXTERNAL_CERTIFICATE : Prop :=
  Claim1To7Evidence canonicalSevenEndpoint

/-- Claim-only final root. No unrelated producer or lane is admitted. -/
abbrev FINAL_ROOT : Prop :=
  EXTERNAL_CERTIFICATE

/-- Claim-only final proof endpoint. It contains exactly Claim1 through Claim7. -/
abbrev FINAL_PROOF : Prop :=
  FINAL_ROOT

theorem canonicalExternalCertificate : EXTERNAL_CERTIFICATE :=
  canonicalClaim1To7

theorem canonicalFinalRoot : FINAL_ROOT :=
  canonicalExternalCertificate

theorem canonicalFinalProof : FINAL_PROOF :=
  canonicalFinalRoot

#print axioms MCore.Real.Claim1To7Only.canonicalClaim1To7
#print axioms MCore.Real.Claim1To7Only.canonicalExternalCertificate
#print axioms MCore.Real.Claim1To7Only.canonicalFinalRoot
#print axioms MCore.Real.Claim1To7Only.canonicalFinalProof

end MCore.Real.Claim1To7Only
