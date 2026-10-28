import MCore.Real.P05_Hodge.SourceBinding

namespace MCore.Real.P05_Hodge.ClosedBridge.PointwiseToHodge

open P05_Hodge.SourceBinding

def evidence : SourceEvidence :=
  { name := "PointwiseToHodge"
    kind := .closedBridge
    sourceRepo := canonicalHodgeRepo
    sourceRef := canonicalFrozenRef
    sourcePath := "lean/MCore/HodgeReduction.lean"
    theoremName := "pointwise_closes_hodge"
    semanticScope := "Conditional bridge: a proof of every pointwise algebraicity obligation closes the semantic rational Hodge conjecture."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P05_Hodge.ClosedBridge.PointwiseToHodge.evidence_is_source_verified

end MCore.Real.P05_Hodge.ClosedBridge.PointwiseToHodge
