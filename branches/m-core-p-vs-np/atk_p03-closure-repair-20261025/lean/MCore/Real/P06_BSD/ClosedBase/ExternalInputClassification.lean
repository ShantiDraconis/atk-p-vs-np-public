import MCore.Real.P06_BSD.SourceBinding

namespace MCore.Real.P06_BSD.ClosedBase.ExternalInputClassification

open P06_BSD.SourceBinding

def evidence : SourceEvidence :=
  { name := "ExternalInputClassification"
    kind := .closedBase
    sourceRepo := canonicalBSDRepo
    sourceRef := canonicalMainRef
    sourcePath := "lean/MCore/K11.lean"
    theoremName := "k11_modularity_external / k11_analytic_continuation_external / k11_functional_equation_external / k11_rank_equality_open"
    semanticScope := "Closed provenance classification: modularity, analytic continuation and functional equation are external inputs; rank equality remains open."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P06_BSD.ClosedBase.ExternalInputClassification.evidence_is_source_verified

end MCore.Real.P06_BSD.ClosedBase.ExternalInputClassification
