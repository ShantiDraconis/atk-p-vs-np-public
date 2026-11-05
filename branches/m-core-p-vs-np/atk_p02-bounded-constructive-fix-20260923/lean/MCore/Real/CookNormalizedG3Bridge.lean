import MCore.Real.CookNormalizedNTMBridge
import MCore.Real.G3ModelMatch

namespace MCore
namespace Real
namespace CookNormalizedG3Bridge

open CanonicalFinalProof
open EncodingNormalization
open G3ModelMatch
open CookNormalizedMachineModel
open CookNormalizedDTMBridge
open CookNormalizedNTMBridge

def identityCost : TimeBound :=
  fun n => n

theorem identityCost_poly :
    PolynomialTimeBound identityCost := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp [identityCost]

def identityNormalization : EncodingNormalization :=
  { canonicalToExternal := id
    externalToCanonical := id
    left_inverse := by intro bs; rfl
    right_inverse := by intro bs; rfl
    encodeCost := identityCost
    decodeCost := identityCost
    encodeCost_poly := identityCost_poly
    decodeCost_poly := identityCost_poly
    encode_length_le_cost := by
      intro bs
      simp [identityCost]
    decode_length_le_cost := by
      intro bs
      simp [identityCost] }

def identitySimulationOverhead : PolySimulationOverhead :=
  { cost := identityCost
    cost_poly := identityCost_poly }

/-- Complete two-way bridge between the hardened internal machine model and the
independent normalized Cook-style formal model.  Because the two formal models
use the same canonical bit-tape representation, normalization is identity and
all four translations preserve the declared polynomial clock exactly.

This is a normalized formal-model bridge.  It is not, by itself, a proof that
the normalized formal model is definitionally identical to every convention in
Cook/CMI's prose problem statement; that source-fidelity audit remains
separate. -/
def cookNormalizedBridge :
    G3ModelBridge cookNormalizedModel :=
  { normalization := identityNormalization
    internalDTM_to_external := internalDTM_to_cook
    internalDTM_to_external_overhead := identitySimulationOverhead
    externalDTM_to_internal := cookDTM_to_internal
    externalDTM_to_internal_overhead := identitySimulationOverhead
    internalNTM_to_external := internalNTM_to_cook
    internalNTM_to_external_overhead := identitySimulationOverhead
    externalNP_to_internal := cookNTM_to_internal
    externalNP_to_internal_overhead := identitySimulationOverhead }

theorem cookNormalized_p_match
    (L : BitLanguage) :
    InP L ↔ cookNormalizedModel.P L :=
  cookNormalizedBridge.p_match L

theorem cookNormalized_np_match
    (L : BitLanguage) :
    InNP L ↔ cookNormalizedModel.NP L :=
  cookNormalizedBridge.np_match L

def CookNormalizedBridgeClosed : Prop :=
  Nonempty (G3ModelBridge cookNormalizedModel)

theorem cookNormalizedBridge_closed :
    CookNormalizedBridgeClosed :=
  ⟨cookNormalizedBridge⟩

#print axioms MCore.Real.CookNormalizedG3Bridge.identityCost_poly
#print axioms MCore.Real.CookNormalizedG3Bridge.cookNormalized_p_match
#print axioms MCore.Real.CookNormalizedG3Bridge.cookNormalized_np_match
#print axioms MCore.Real.CookNormalizedG3Bridge.cookNormalizedBridge_closed

end CookNormalizedG3Bridge
end Real
end MCore
