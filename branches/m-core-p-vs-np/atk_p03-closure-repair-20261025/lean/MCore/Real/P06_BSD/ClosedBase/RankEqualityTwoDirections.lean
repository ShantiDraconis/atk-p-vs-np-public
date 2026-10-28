import MCore.Real.P06_BSD.SourceBinding

namespace MCore.Real.P06_BSD.ClosedBase.RankEqualityTwoDirections

open P06_BSD.SourceBinding

def evidence : SourceEvidence :=
  { name := "RankEqualityTwoDirections"
    kind := .closedBase
    sourceRepo := canonicalBSDRepo
    sourceRef := canonicalMainRef
    sourcePath := "lean/MCore/K10.lean"
    theoremName := "k10_rank_equality_iff_two_directions"
    semanticScope := "Closed propositional decomposition of BSD rank equality into the two directional inequalities; neither direction is proved by this equivalence."
    sourceVerified := true }

theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl

#print axioms MCore.Real.P06_BSD.ClosedBase.RankEqualityTwoDirections.evidence_is_source_verified

end MCore.Real.P06_BSD.ClosedBase.RankEqualityTwoDirections
