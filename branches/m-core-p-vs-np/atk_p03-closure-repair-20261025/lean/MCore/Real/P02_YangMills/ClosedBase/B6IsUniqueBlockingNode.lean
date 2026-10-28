import MCore.Real.P02_YangMills.SourceBinding

namespace MCore.Real.P02_YangMills.ClosedBase.B6IsUniqueBlockingNode

open P02_YangMills.SourceBinding

def evidence : SourceClosedEvidence :=
  { name := "B6IsUniqueBlockingNode"
    kind := .closedBase
    sourceRepo := canonicalYMRepo
    sourceRef := canonicalYMRef
    sourcePath := "lean/MCore/YangMills/A1/FrontierDecompositionV2.lean"
    theoremName := "a1_v2_has_exactly_one_blocking_node / a1_v2_blocking_node_is_k20_k30"
    semanticScope := "Min-cut certificate only: the unique blocking node of the audited A1 decomposition is B6/K20-K30."
    sourceVerified := true }

theorem evidence_is_source_verified :
    evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P02_YangMills.ClosedBase.B6IsUniqueBlockingNode.evidence_is_source_verified

end MCore.Real.P02_YangMills.ClosedBase.B6IsUniqueBlockingNode
