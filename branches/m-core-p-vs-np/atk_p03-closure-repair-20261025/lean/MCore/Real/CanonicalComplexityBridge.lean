import MCore.K9
import MCore.Real.CanonicalPSubsetNP
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace CanonicalComplexityBridge

open CanonicalFinalProof
open CanonicalPSubsetNP
open FailProofAllGaps

def canonicalInterface : ClassicalComplexityInterface BitLanguage :=
  { inP := InP
    inNP := InNP
    p_subset_np := inP_subset_inNP }

theorem canonical_interface_p_match
    (L : BitLanguage) :
    canonicalInterface.inP L ↔ InP L :=
  Iff.rfl

theorem canonical_interface_np_match
    (L : BitLanguage) :
    canonicalInterface.inNP L ↔ InNP L :=
  Iff.rfl

def canonicalExternalMatch :
    ExternalModelMatch canonicalInterface.inP canonicalInterface.inNP :=
  { p_match := fun _ => Iff.rfl
    np_match := fun _ => Iff.rfl }

theorem canonical_failure_witness_separates_legacy_interface
    {L : BitLanguage}
    (hNP : canonicalInterface.inNP L)
    (hFail : UniversalFailure L) :
    ¬ (∀ X : BitLanguage,
      canonicalInterface.inP X ↔ canonicalInterface.inNP X) := by
  intro hEq
  have hP : InP L := (hEq L).mpr hNP
  exact (universal_failure_implies_not_in_p hFail) hP

#print axioms MCore.Real.CanonicalComplexityBridge.canonical_interface_p_match
#print axioms MCore.Real.CanonicalComplexityBridge.canonical_interface_np_match
#print axioms MCore.Real.CanonicalComplexityBridge.canonical_failure_witness_separates_legacy_interface

end CanonicalComplexityBridge
end Real
end MCore
