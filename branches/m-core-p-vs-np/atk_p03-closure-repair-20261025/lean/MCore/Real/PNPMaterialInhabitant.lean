import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace PNPMaterialInhabitant

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits

/-- The fixed canonical language used by the material P-vs-NP lane. -/
abbrev CanonicalSATBits : BitLanguage :=
  SATBits circuitBitEncoding

/--
Material endpoint payload for the fixed canonical SAT language.

This deliberately stores only:
* the NP-side realization, and
* the genuine deterministic lower bound.

No separation theorem, P != NP hypothesis, endpoint equivalence, or
UniversalFailure field is stored.
-/
structure MaterialInhabitantPNP where
  in_np : InNP CanonicalSATBits
  not_in_p : ¬ InP CanonicalSATBits

/-- The proposition asserting that the material payload is actually inhabited. -/
def MaterialAprioriBoundPNP : Prop :=
  Nonempty MaterialInhabitantPNP

/--
Operational form of the same endpoint.  UniversalFailure is equivalent to
not-InP in the hardened canonical model.
-/
def OperationalMaterialEndpointPNP : Prop :=
  InNP CanonicalSATBits ∧ UniversalFailure CanonicalSATBits

theorem material_to_operational
    (h : MaterialInhabitantPNP) :
    OperationalMaterialEndpointPNP := by
  exact ⟨h.in_np, not_in_p_implies_universal_failure h.not_in_p⟩

theorem operational_to_material
    (h : OperationalMaterialEndpointPNP) :
    MaterialInhabitantPNP := by
  exact
    { in_np := h.1
      not_in_p := universal_failure_implies_not_in_p h.2 }

theorem material_iff_operational :
    MaterialAprioriBoundPNP ↔ OperationalMaterialEndpointPNP := by
  constructor
  · intro h
    rcases h with ⟨w⟩
    exact material_to_operational w
  · intro h
    exact ⟨operational_to_material h⟩

/-- A genuine material inhabitant closes the repository's canonical P != NP endpoint. -/
theorem material_inhabitant_closes_PneqNP
    (h : MaterialInhabitantPNP) :
    PneqNP := by
  exact target_failure_implies_p_ne_np
    h.in_np
    (not_in_p_implies_universal_failure h.not_in_p)

/-- Same closure phrased at the proposition/in-habited level. -/
theorem material_apriori_bound_closes_PneqNP
    (h : MaterialAprioriBoundPNP) :
    PneqNP := by
  rcases h with ⟨w⟩
  exact material_inhabitant_closes_PneqNP w

/--
Constructor only.  This theorem is intentionally not a producer of the lower
bound; it makes the remaining mathematical obligation syntactically explicit.
-/
theorem material_apriori_bound_PNP_of
    (hNP : InNP CanonicalSATBits)
    (hLowerBound : ¬ InP CanonicalSATBits) :
    MaterialAprioriBoundPNP := by
  exact ⟨{ in_np := hNP, not_in_p := hLowerBound }⟩

/-
OPEN_MATH / CLAY-LEVEL TARGET:

theorem material_apriori_bound_PNP :
    MaterialAprioriBoundPNP := by
  -- Must construct BOTH:
  --   1. InNP CanonicalSATBits
  --   2. ¬ InP CanonicalSATBits
  --
  -- The second field is the genuine super-polynomial lower bound.
  -- Filling it from PneqNP, UniversalFailure, LowerBoundWitness.not_in_p,
  -- or an endpoint-equivalent hypothesis would be circular and is forbidden.
-/

#print axioms MCore.Real.PNPMaterialInhabitant.material_to_operational
#print axioms MCore.Real.PNPMaterialInhabitant.operational_to_material
#print axioms MCore.Real.PNPMaterialInhabitant.material_iff_operational
#print axioms MCore.Real.PNPMaterialInhabitant.material_inhabitant_closes_PneqNP
#print axioms MCore.Real.PNPMaterialInhabitant.material_apriori_bound_closes_PneqNP
#print axioms MCore.Real.PNPMaterialInhabitant.material_apriori_bound_PNP_of

end PNPMaterialInhabitant
end Real
end MCore
