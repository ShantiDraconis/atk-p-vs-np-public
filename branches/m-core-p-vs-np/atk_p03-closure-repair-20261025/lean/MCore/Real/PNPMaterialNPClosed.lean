import MCore.Real.P01RawTotalizationProducer
import MCore.Real.PNPMaterialNPFrontier

namespace MCore
namespace Real
namespace PNPMaterialNPClosed

open CanonicalFinalProof
open CanonicalCircuitBits
open P01RawTotalizationProducer
open PNPMaterialInhabitant
open PNPMaterialNPFrontier

/-- The repository's concrete raw-totalization producer closes the integrated
    canonical SAT NTM construction with no endpoint hypothesis. -/
theorem p01_construction_material_closed :
    P01FinalCertificate.P01ConstructionGap := by
  exact p01ConstructionGap_closed

/-- Material NP half of the canonical P-vs-NP endpoint. -/
theorem canonical_sat_in_np_material :
    InNP CanonicalSATBits := by
  exact p01_construction_closes_material_np
    p01_construction_material_closed

/-- After the NP side is materially closed, the complete material endpoint is
    equivalent to supplying only the genuine deterministic lower bound. -/
theorem lower_bound_only_builds_material
    (hLower : ¬ InP CanonicalSATBits) :
    MaterialAprioriBoundPNP := by
  exact p01_plus_lower_bound_closes_material_apriori
    p01_construction_material_closed hLower

/-- Operational spelling of the same remaining lower-bound obligation. -/
theorem universal_failure_only_builds_material
    (hFail : UniversalFailure CanonicalSATBits) :
    MaterialAprioriBoundPNP := by
  exact lower_bound_only_builds_material
    (universal_failure_implies_not_in_p hFail)

#print axioms MCore.Real.PNPMaterialNPClosed.p01_construction_material_closed
#print axioms MCore.Real.PNPMaterialNPClosed.canonical_sat_in_np_material
#print axioms MCore.Real.PNPMaterialNPClosed.lower_bound_only_builds_material
#print axioms MCore.Real.PNPMaterialNPClosed.universal_failure_only_builds_material

end PNPMaterialNPClosed
end Real
end MCore
