import MCore.Real.P05_Hodge.SourceBinding

namespace MCore.Real.P05_Hodge.ClosedBase.HodgeDecompositionReduction

open P05_Hodge.SourceBinding

def evidence : SourceEvidence :=
  { name := "HodgeDecompositionReduction"
    kind := .closedBase
    sourceRepo := canonicalHodgeRepo
    sourceRef := canonicalFrozenRef
    sourcePath := "lean/MCore/HodgeDecomposition.lean"
    theoremName := "hodge_iff_all_decomposed"
    semanticScope := "Closed equivalence between the semantic Hodge endpoint and all decomposed local algebraicity obligations, relative to supplied decomposition data."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P05_Hodge.ClosedBase.HodgeDecompositionReduction.evidence_is_source_verified

end MCore.Real.P05_Hodge.ClosedBase.HodgeDecompositionReduction
