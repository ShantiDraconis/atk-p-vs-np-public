import MCore.Real.P01VerifierPhaseMinCutStructural
import MCore.Real.PNPMaterialNPFrontier

namespace MCore
namespace Real
namespace PNPMaterialVerifierFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open P01IntegratedAssembly
open P01WitnessPrepGlobal
open P01VerifierPhaseMinCutStructural
open P01FinalCertificate
open PNPMaterialInhabitant
open PNPMaterialNPFrontier

/-- The witness-preparation phase is a concrete inhabitant, not an open hypothesis. -/
theorem prep_phase_is_material :
    Nonempty P01PrepPhase := by
  exact ⟨prepPhase⟩

/-- Exact remaining NP-side mechanical min-cut. -/
abbrev CanonicalVerifierMinCut : Prop :=
  Nonempty (P01VerifierPhase prepPhase.layout)

/-- A verifier-phase inhabitant closes the integrated P01 construction. -/
theorem verifier_min_cut_closes_p01
    (h : CanonicalVerifierMinCut) :
    P01ConstructionGap := by
  exact p01ConstructionGap_of_verifierPhase h

/-- Therefore the same verifier inhabitant closes the NP half of the canonical
    P-vs-NP material endpoint. -/
theorem verifier_min_cut_closes_material_np
    (h : CanonicalVerifierMinCut) :
    InNP CanonicalSATBits := by
  exact p01_construction_closes_material_np
    (verifier_min_cut_closes_p01 h)

/-- Once this verifier exists, the ONLY remaining field of the full material
    endpoint is the genuine deterministic lower bound. -/
theorem verifier_plus_lower_bound_builds_material
    (hVerifier : CanonicalVerifierMinCut)
    (hLower : ¬ InP CanonicalSATBits) :
    MaterialAprioriBoundPNP := by
  exact p01_plus_lower_bound_closes_material_apriori
    (verifier_min_cut_closes_p01 hVerifier) hLower

#print axioms MCore.Real.PNPMaterialVerifierFrontier.prep_phase_is_material
#print axioms MCore.Real.PNPMaterialVerifierFrontier.verifier_min_cut_closes_p01
#print axioms MCore.Real.PNPMaterialVerifierFrontier.verifier_min_cut_closes_material_np
#print axioms MCore.Real.PNPMaterialVerifierFrontier.verifier_plus_lower_bound_builds_material

end PNPMaterialVerifierFrontier
end Real
end MCore
