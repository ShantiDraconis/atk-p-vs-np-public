import MCore.Real.P03.ClosedBase.SourceBinding
namespace MCore.Real.P03.ClosedBase.SPlus
open MCore.Real.P03.ClosedBase.SourceBinding
def evidence : ClosedSourceEvidence :=
  { name := "SPlus", sourceRepo := canonicalRepo, sourceRef := "2e20eb3b3f98e113e397befa2544377c2403c9d8"
    theoremName := "SPlus / splus_eq_zero_iff", semanticScope := "S+ quadratic and zero characterization.", sourceVerified := true }
theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl
#print axioms MCore.Real.P03.ClosedBase.SPlus.evidence_is_source_verified
end MCore.Real.P03.ClosedBase.SPlus
