import MCore.Real.P01FinalCertificate
import MCore.Real.P01WitnessIndexedReadGlobal
import MCore.Real.PNPMaterialInhabitant

namespace MCore
namespace Real
namespace PNPMaterialNPFrontier

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P01FinalCertificate
open P01WitnessIndexedReadGlobal
open PNPMaterialInhabitant

/-- The indexed witness-read subproblem is no longer part of the NP-side frontier. -/
theorem indexed_witness_read_is_closed :
    P01WitnessIndexedRead.WitnessIndexedReadGap := by
  exact witnessIndexedReadGap_closed

/-- The exact integrated P01 machine object is sufficient for the NP half of
    the canonical material inhabitant. -/
theorem p01_construction_closes_material_np
    (h : P01ConstructionGap) :
    InNP CanonicalSATBits := by
  exact construction_closes_p01 h

/-- Once the integrated NP construction exists, the only remaining field of
    the material inhabitant is the genuine deterministic lower bound. -/
theorem p01_plus_lower_bound_builds_material_inhabitant
    (hP01 : P01ConstructionGap)
    (hLower : ¬ InP CanonicalSATBits) :
    MaterialInhabitantPNP := by
  exact
    { in_np := p01_construction_closes_material_np hP01
      not_in_p := hLower }

/-- Proposition-level closure, exposing the exact two independent producers. -/
theorem p01_plus_lower_bound_closes_material_apriori
    (hP01 : P01ConstructionGap)
    (hLower : ¬ InP CanonicalSATBits) :
    MaterialAprioriBoundPNP := by
  exact ⟨p01_plus_lower_bound_builds_material_inhabitant hP01 hLower⟩

#print axioms MCore.Real.PNPMaterialNPFrontier.indexed_witness_read_is_closed
#print axioms MCore.Real.PNPMaterialNPFrontier.p01_construction_closes_material_np
#print axioms MCore.Real.PNPMaterialNPFrontier.p01_plus_lower_bound_builds_material_inhabitant
#print axioms MCore.Real.PNPMaterialNPFrontier.p01_plus_lower_bound_closes_material_apriori

end PNPMaterialNPFrontier
end Real
end MCore
