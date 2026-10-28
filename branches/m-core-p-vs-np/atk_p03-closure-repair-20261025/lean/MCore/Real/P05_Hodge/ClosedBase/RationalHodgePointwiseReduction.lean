import MCore.Real.P05_Hodge.SourceBinding

namespace MCore.Real.P05_Hodge.ClosedBase.RationalHodgePointwiseReduction

open P05_Hodge.SourceBinding

def evidence : SourceEvidence :=
  { name := "RationalHodgePointwiseReduction"
    kind := .closedBase
    sourceRepo := canonicalHodgeRepo
    sourceRef := canonicalFrozenRef
    sourcePath := "lean/MCore/HodgeReduction.lean"
    theoremName := "rationalHodge_iff_pointwise"
    semanticScope := "Closed definitional reduction of the semantic rational Hodge endpoint to pointwise algebraicity obligations."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P05_Hodge.ClosedBase.RationalHodgePointwiseReduction.evidence_is_source_verified

end MCore.Real.P05_Hodge.ClosedBase.RationalHodgePointwiseReduction
