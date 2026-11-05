import MCore.Real.CanonicalFinalExternal
import MCore.Real.P01WitnessPrepGlobal

namespace MCore.Real
namespace CanonicalFinalExternal

open P01IntegratedAssembly
open P01WitnessPrepGlobal
open P02G21G22Attack

/-- The prep phase is already fully inhabited.  Therefore the entire P01 side
    reduces to one concrete verifier phase over the certified prepared layout. -/
abbrev P01RemainingVerifier : Type :=
  P01VerifierPhase prepPhase.layout

/-- A verifier inhabitant closes P01 mechanically. -/
theorem p01Construction_of_verifier
    (V : P01RemainingVerifier) :
    P01FinalCertificate.P01ConstructionGap :=
  p01_of_verifier V

/-- Exact current internal OPEN_MATH pair:
    one physical verifier phase + the same-input G2.1 lower bound. -/
structure MinimalFinalExternalCertificate : Type where
  verifier : P01RemainingVerifier
  g21 : G21Pointwise

/-- No parser/prep/wiring assumptions remain in this producer. -/
theorem minimalFinalExternal_to_FINAL_ROOT
    (E : MinimalFinalExternalCertificate) :
    FINAL_ROOT := by
  exact finalExternal_to_FINAL_ROOT
    {
      p01 := p01Construction_of_verifier E.verifier
      g21 := E.g21
    }

/-- External/official closure adds only the model-equivalence proof. -/
theorem minimalFinalExternal_to_OFFICIAL_ROOT
    {officialP officialNP : CanonicalFinalProof.BitLanguage → Prop}
    (E : MinimalFinalExternalCertificate)
    (M : FailProofAllGaps.ExternalModelMatch officialP officialNP) :
    OFFICIAL_FINAL_ROOT officialP officialNP := by
  exact FailProofAllGaps.internal_separation_transfers M
    (minimalFinalExternal_to_FINAL_ROOT E)

#print axioms MCore.Real.CanonicalFinalExternal.p01Construction_of_verifier
#print axioms MCore.Real.CanonicalFinalExternal.minimalFinalExternal_to_FINAL_ROOT
#print axioms MCore.Real.CanonicalFinalExternal.minimalFinalExternal_to_OFFICIAL_ROOT

end CanonicalFinalExternal
end MCore.Real
