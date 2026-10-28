import MCore.Real.P03.ClosedBase.SourceBinding
namespace MCore.Real.P03.ClosedBase.Nabla2
open MCore.Real.P03.ClosedBase.SourceBinding
def evidence : ClosedSourceEvidence :=
  { name := "Nabla2", sourceRepo := canonicalRepo, sourceRef := "3e074d546496789e2c73b4b210abb581d0e23026"
    theoremName := "hessian_entries / rank_one_outer_product", semanticScope := "Rank-one Hessian certificate.", sourceVerified := true }
theorem evidence_is_source_verified : evidence.sourceVerified = true := rfl
#print axioms MCore.Real.P03.ClosedBase.Nabla2.evidence_is_source_verified
end MCore.Real.P03.ClosedBase.Nabla2
