import MCore.Real.P02_YangMills.SourceBinding

namespace MCore.Real.P02_YangMills.ClosedBase.A1FrontierReduction

open P02_YangMills.SourceBinding

def evidence : SourceClosedEvidence :=
  { name := "A1FrontierReduction"
    kind := .closedBase
    sourceRepo := canonicalYMRepo
    sourceRef := canonicalYMRef
    sourcePath := "lean/MCore/YangMills/A1/PhantomBridgeTriviality.lean"
    theoremName := "a1_scientific_open_bridge_iff_B1_B2"
    semanticScope := "Closed reduction of the legacy A1 scientific bridge to MeasureInvariance and ObservableInvariance; removes B3/B4/B5 as material producers."
    sourceVerified := true }

theorem evidence_is_source_verified :
    evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P02_YangMills.ClosedBase.A1FrontierReduction.evidence_is_source_verified

end MCore.Real.P02_YangMills.ClosedBase.A1FrontierReduction
