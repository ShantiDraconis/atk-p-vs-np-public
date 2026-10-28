import MCore.Real.P01RawTotalizationProducer

namespace MCore
namespace Real
namespace P01PostMinCutClosure

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits

/-- The frozen P01 mechanical closure gives the canonical SAT-in-NP witness
for the exact bit-language used by the hardened endpoint. -/
theorem canonical_sat_in_np_closed :
    SATInNPGap circuitBitEncoding := by
  exact P01FinalCertificate.construction_closes_p01
    P01RawTotalizationProducer.p01ConstructionGap_closed

/-- After P01 is closed, the sole material internal separation obligation is
the universal deterministic fail proof for the same canonical SAT language. -/
abbrev RemainingMaterialGap : Prop :=
  UniversalFailure (SATBits circuitBitEncoding)

theorem remaining_material_gap_implies_p_ne_np
    (hFail : RemainingMaterialGap) :
    PneqNP :=
  target_failure_implies_p_ne_np
    canonical_sat_in_np_closed hFail

theorem final_residual_iff_remaining_material_gap :
    (SATInNPGap circuitBitEncoding ∧
      UniversalFailure (SATBits circuitBitEncoding)) ↔
      RemainingMaterialGap := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨canonical_sat_in_np_closed, h⟩

#print axioms MCore.Real.P01PostMinCutClosure.canonical_sat_in_np_closed
#print axioms MCore.Real.P01PostMinCutClosure.remaining_material_gap_implies_p_ne_np
#print axioms MCore.Real.P01PostMinCutClosure.final_residual_iff_remaining_material_gap

end P01PostMinCutClosure
end Real
end MCore
