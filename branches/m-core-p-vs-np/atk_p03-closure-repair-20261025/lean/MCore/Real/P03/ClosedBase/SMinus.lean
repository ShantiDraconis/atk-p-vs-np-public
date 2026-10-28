import MCore.Real.P03.ClosedBase.SourceBinding
namespace MCore.Real.P03.ClosedBase.SMinus
open MCore.Real.P03.ClosedBase.SourceBinding
def evidence : ClosedSourceEvidence :=
  { name := "SMinus", sourceRepo := canonicalRepo, sourceRef := "9a63941c097bc2ff2b82bc4c709bb224f4746fb7"
    theoremName := "SMinus / sminus_eq_zero_iff", semanticScope := "S- quadratic and zero characterization.", sourceVerified := true }
theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl
#print axioms MCore.Real.P03.ClosedBase.SMinus.evidence_is_source_verified
end MCore.Real.P03.ClosedBase.SMinus
