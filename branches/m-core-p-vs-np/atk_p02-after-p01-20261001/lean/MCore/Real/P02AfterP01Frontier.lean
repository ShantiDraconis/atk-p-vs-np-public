import MCore.Real.P01PostMinCutClosure
import MCore.Real.P02G21G22Attack

namespace MCore
namespace Real
namespace P02AfterP01Frontier

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P01PostMinCutClosure
open P02TerminalFrontier
open P02G21G22Attack

/-- After frozen P01 closure, the post-mincut residual is definitionally the
pointwise G2.1 lower-bound statement for the same canonical SAT language. -/
theorem remaining_material_gap_iff_g21 :
    RemainingMaterialGap ↔ G21Pointwise := by
  rfl

/-- The sole remaining material producer after P01 is exactly P02Target. -/
theorem remaining_material_gap_iff_p02 :
    RemainingMaterialGap ↔ P02Target := by
  rw [remaining_material_gap_iff_g21]
  exact g21_pointwise_iff_p02_target

/-- P02 alone is now the only missing internal producer: P01 is supplied by
the frozen kernel-checked construction on this branch ancestry. -/
theorem p02_closes_internal_after_frozen_p01
    (hP02 : P02Target) :
    PneqNP := by
  apply P01PostMinCutClosure.remaining_material_gap_implies_p_ne_np
  exact remaining_material_gap_iff_p02.mpr hP02

/-- Equivalent pointwise formulation of the remaining producer. -/
theorem g21_closes_internal_after_frozen_p01
    (hG21 : G21Pointwise) :
    PneqNP := by
  exact P02G21G22Attack.p01_g21_closes_internal
    P01PostMinCutClosure.canonical_sat_in_np_closed hG21

#print axioms MCore.Real.P02AfterP01Frontier.remaining_material_gap_iff_g21
#print axioms MCore.Real.P02AfterP01Frontier.remaining_material_gap_iff_p02
#print axioms MCore.Real.P02AfterP01Frontier.p02_closes_internal_after_frozen_p01
#print axioms MCore.Real.P02AfterP01Frontier.g21_closes_internal_after_frozen_p01

end P02AfterP01Frontier
end Real
end MCore
