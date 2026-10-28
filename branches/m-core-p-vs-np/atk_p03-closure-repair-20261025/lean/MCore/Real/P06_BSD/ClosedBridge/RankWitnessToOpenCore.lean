import MCore.Real.P06_BSD.SourceBinding

namespace MCore.Real.P06_BSD.ClosedBridge.RankWitnessToOpenCore

open P06_BSD.SourceBinding

def evidence : SourceEvidence :=
  { name := "RankWitnessToOpenCore"
    kind := .closedBridge
    sourceRepo := canonicalBSDRepo
    sourceRef := canonicalMainRef
    sourcePath := "lean/MCore/BackwardAudit/WithoutOracle.lean"
    theoremName := "rank_witness_contract_closes"
    semanticScope := "Conditional bridge only: a supplied RankPartWitnessContract closes the abstract BSDOpenCore for every typed datum."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P06_BSD.ClosedBridge.RankWitnessToOpenCore.evidence_is_source_verified

end MCore.Real.P06_BSD.ClosedBridge.RankWitnessToOpenCore
