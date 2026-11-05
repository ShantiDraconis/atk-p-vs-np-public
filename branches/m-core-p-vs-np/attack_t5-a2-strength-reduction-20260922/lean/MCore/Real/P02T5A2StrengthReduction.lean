import MCore.Real.P02SemanticSelfEmbeddingClose
import MCore.Real.P02G21G22Attack

namespace MCore
namespace Real
namespace P02T5A2StrengthReduction

open P02SemanticSelfEmbeddingClose
open P02G21G22Attack
open P02TerminalFrontier

/-- The semantic diagonal producer used by T5-A2 is sufficient for the exact
minimal G2.1 pointwise lower-bound frontier. This is a one-way reduction only:
no converse is asserted. -/
theorem universal_witness_implies_g21_pointwise
    (h : UniversalWitnessExists) :
    G21Pointwise := by
  apply g21_pointwise_iff_p02_target.mpr
  exact universal_witness_closes_p02 h

/-- Consequently the current T5-A2 existence problem is a sufficient producer
for P02, while the minimal OPEN_MATH target remains G21Pointwise/P02Target. -/
theorem universal_witness_implies_p02_target
    (h : UniversalWitnessExists) :
    P02Target := by
  exact g21_pointwise_iff_p02_target.mp
    (universal_witness_implies_g21_pointwise h)

#print axioms MCore.Real.P02T5A2StrengthReduction.universal_witness_implies_g21_pointwise
#print axioms MCore.Real.P02T5A2StrengthReduction.universal_witness_implies_p02_target

end P02T5A2StrengthReduction
end Real
end MCore
