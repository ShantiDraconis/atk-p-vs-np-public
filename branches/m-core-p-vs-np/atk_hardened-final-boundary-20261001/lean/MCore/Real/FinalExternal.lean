import MCore.Real.FinalProof
import MCore.Real.P01FinalCertificate

namespace MCore.Real

/-- Final external producer for the concrete Circuit machine model.
    It contains exactly the two live theorem-producing inputs required by
    FinalProof.final_proof_from_residual. -/
structure FinalExternalLiveTwoProducer : Prop where
  satInNP : SATInNP
  satLowerBound : SATLowerBoundCertificate

/-- Kernel-checkable final external certificate. -/
abbrev FinalExternalCertificate : Prop :=
  Nonempty FinalExternalLiveTwoProducer

/-- Canonical final root for the concrete machine model. -/
def FINAL_ROOT : Prop :=
  MachinePneqNP

/-- Final external data creates the exact FINAL_PROOF residual. -/
theorem finalExternal_to_residual
    (E : FinalExternalLiveTwoProducer) :
    FINAL_PROOF_RESIDUAL :=
  ⟨E.satInNP, E.satLowerBound⟩

/-- FINAL_EXTERNAL -> FINAL_ROOT. -/
theorem finalExternal_to_FINAL_ROOT
    (E : FinalExternalLiveTwoProducer) :
    FINAL_ROOT :=
  final_proof_from_residual (finalExternal_to_residual E)

/-- Certificate-shaped entry point. -/
theorem finalExternalCertificate_to_FINAL_ROOT
    (C : FinalExternalCertificate) :
    FINAL_ROOT := by
  rcases C with ⟨E⟩
  exact finalExternal_to_FINAL_ROOT E

/-- The external object is exactly equivalent to the existing residual,
    so this file adds no mathematical assumption and no weaker shortcut. -/
theorem finalExternal_iff_residual :
    FinalExternalCertificate ↔ FINAL_PROOF_RESIDUAL := by
  constructor
  · rintro ⟨E⟩
    exact finalExternal_to_residual E
  · rintro ⟨hNP, hLB⟩
    exact ⟨⟨hNP, hLB⟩⟩

#print axioms MCore.Real.finalExternal_to_residual
#print axioms MCore.Real.finalExternal_to_FINAL_ROOT
#print axioms MCore.Real.finalExternalCertificate_to_FINAL_ROOT
#print axioms MCore.Real.finalExternal_iff_residual

end MCore.Real
