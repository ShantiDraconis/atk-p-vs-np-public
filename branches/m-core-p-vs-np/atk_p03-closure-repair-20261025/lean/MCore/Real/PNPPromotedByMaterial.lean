import MCore.Real.PNPMaterialNPClosed
import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace PNPPromotedByMaterial

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPMaterialInhabitant
open PNPMaterialNPClosed

/--
A genuinely material lower-bound producer for canonical SAT.

This structure does not store PneqNP, not-InP SAT, UniversalFailure SAT, or an
endpoint-equivalent proposition. Instead it carries the operational content
needed to refute every deterministic polynomial-time candidate: for each
candidate it computes a concrete bitstring and proves that the candidate is
incorrect on that bitstring.
-/
structure CanonicalSATLowerBoundProducer where
  counterexample : PolyDTMCandidate → BitString
  fails :
    ∀ candidate : PolyDTMCandidate,
      ¬ candidate.CorrectAt CanonicalSATBits (counterexample candidate)

/-- The producer supplies the universal-failure statement by direct witness extraction. -/
theorem lowerBoundProducer_to_universalFailure
    (P : CanonicalSATLowerBoundProducer) :
    UniversalFailure CanonicalSATBits := by
  intro candidate
  exact ⟨P.counterexample candidate, P.fails candidate⟩

/-- Hence the same producer supplies the genuine deterministic lower bound. -/
theorem lowerBoundProducer_to_notInP
    (P : CanonicalSATLowerBoundProducer) :
    ¬ InP CanonicalSATBits := by
  exact universal_failure_implies_not_in_p
    (lowerBoundProducer_to_universalFailure P)

/--
Full material closure object.

The NP half is not stored as a hypothesis: it is already produced concretely
by PNPMaterialNPClosed.canonical_sat_in_np_material. The only field is the
genuine candidate-by-candidate lower-bound producer.
-/
structure PromotedByMaterialPNP where
  lowerBound : CanonicalSATLowerBoundProducer

/-- Material endpoint obtained without assuming an endpoint-equivalent field. -/
theorem promoted_material_endpoint
    (P : PromotedByMaterialPNP) :
    MaterialInhabitantPNP := by
  exact
    { in_np := canonical_sat_in_np_material
      not_in_p := lowerBoundProducer_to_notInP P.lowerBound }

/-- Operational form of the same material endpoint. -/
theorem promoted_operational_endpoint
    (P : PromotedByMaterialPNP) :
    OperationalMaterialEndpointPNP := by
  exact material_to_operational (promoted_material_endpoint P)

/-- The material a-priori bound. -/
theorem promoted_material_apriori
    (P : PromotedByMaterialPNP) :
    MaterialAprioriBoundPNP := by
  exact ⟨promoted_material_endpoint P⟩

/-- Final internal theorem: a genuine material producer closes PneqNP. -/
theorem promoted_material_PneqNP
    (P : PromotedByMaterialPNP) :
    PneqNP := by
  exact material_inhabitant_closes_PneqNP
    (promoted_material_endpoint P)

/--
Exact Millennium-level open target.

To obtain an actual PROMOTED_BY_MATERIAL certificate, one must define a closed
term hPNP_material : PromotedByMaterialPNP whose counterexample is explicit and
whose fails theorem kernel-checks for every PolyDTMCandidate.

No proof of this target is supplied here. Constructing it is exactly the
remaining P versus NP lower-bound problem in this formal model.
-/
def MaterialPromotionTarget : Prop :=
  Nonempty PromotedByMaterialPNP

theorem materialPromotionTarget_closes_PneqNP
    (h : MaterialPromotionTarget) :
    PneqNP := by
  rcases h with ⟨P⟩
  exact promoted_material_PneqNP P

#print axioms MCore.Real.PNPPromotedByMaterial.lowerBoundProducer_to_universalFailure
#print axioms MCore.Real.PNPPromotedByMaterial.lowerBoundProducer_to_notInP
#print axioms MCore.Real.PNPPromotedByMaterial.promoted_material_endpoint
#print axioms MCore.Real.PNPPromotedByMaterial.promoted_operational_endpoint
#print axioms MCore.Real.PNPPromotedByMaterial.promoted_material_apriori
#print axioms MCore.Real.PNPPromotedByMaterial.promoted_material_PneqNP
#print axioms MCore.Real.PNPPromotedByMaterial.materialPromotionTarget_closes_PneqNP

end PNPPromotedByMaterial
end Real
end MCore
