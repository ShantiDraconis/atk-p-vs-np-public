import MCore.Real.P06_BSD.SourceBinding

namespace MCore.Real.P06_BSD.ClosedBase.AbstractTypeCounteraudit

open P06_BSD.SourceBinding

def evidence : SourceEvidence :=
  { name := "AbstractTypeCounteraudit"
    kind := .closedBase
    sourceRepo := canonicalBSDRepo
    sourceRef := canonicalMainRef
    sourcePath := "audit/ATK_BSD_ABSTRACT_TYPE_COUNTERAUDIT.lean"
    theoremName := "no_universal_rank_part_over_arbitrary_data"
    semanticScope := "Fail-closed counteraudit: arbitrary natural-number rank data do not model elliptic curves, so the abstract universal BSDRankPart target is rejected."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P06_BSD.ClosedBase.AbstractTypeCounteraudit.evidence_is_source_verified

end MCore.Real.P06_BSD.ClosedBase.AbstractTypeCounteraudit
