import MCore.Real.OfficialCookSource
import MCore.Real.CookNormalizedG3Bridge
import MCore.Real.G3ModelMatch

namespace MCore
namespace Real
namespace CookNormalizedG3Contract

open OfficialModel
open OfficialCookSource
open CookNormalizedMachineModel
open CookNormalizedG3Bridge
open G3ModelMatch

/--
Concrete normalized G3 selection.

This closes the repository's typed G3ExternalContract for the normalized
Cook-style model using the populated Cook/CMI provenance record and the
already-proved two-way polynomial model bridge.

It deliberately does NOT assert that this normalized formal model is a complete
formalization of every convention in the Cook/CMI prose source. That separate
source-fidelity statement remains outside this theorem.
-/
def cookNormalizedSelection : OfficialModelSelection :=
  { model := cookNormalizedModel
    source := cookCMISource }

def cookNormalizedExternalContract : G3ExternalContract :=
  { selection := cookNormalizedSelection
    bridge := cookNormalizedBridge }

/-- The normalized typed G3 contract is inhabited. -/
theorem cook_normalized_g3_contract_closed :
    G3Gap := by
  exact ⟨cookNormalizedExternalContract⟩

/-- Exact P-model match carried by the normalized contract. -/
theorem cook_normalized_contract_p_match
    (L : CanonicalFinalProof.BitLanguage) :
    CanonicalFinalProof.InP L ↔
      cookNormalizedSelection.model.P L := by
  exact cookNormalizedExternalContract.bridge.p_match L

/-- Exact NP-model match carried by the normalized contract. -/
theorem cook_normalized_contract_np_match
    (L : CanonicalFinalProof.BitLanguage) :
    CanonicalFinalProof.InNP L ↔
      cookNormalizedSelection.model.NP L := by
  exact cookNormalizedExternalContract.bridge.np_match L

#print axioms MCore.Real.CookNormalizedG3Contract.cook_normalized_g3_contract_closed
#print axioms MCore.Real.CookNormalizedG3Contract.cook_normalized_contract_p_match
#print axioms MCore.Real.CookNormalizedG3Contract.cook_normalized_contract_np_match

end CookNormalizedG3Contract
end Real
end MCore
