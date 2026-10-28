import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits
import MCore.Real.P01FinalCertificate

namespace MCore.Real
namespace HardenedFinal

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps
open P01FinalCertificate

/-- Hardened final external certificate.
    P01 supplies SAT ∈ NP in the fixed finite-control bitstring model.
    The only separation input is a genuine universal deterministic fail generator. -/
structure FinalExternalCertificate where
  p01 : P01ConstructionGap
  fail : FailureGenerator (SATBits circuitBitEncoding)

/-- Internal hardened final root. -/
def FINAL_ROOT : Prop :=
  CanonicalFinalProof.PneqNP

theorem p01_to_sat_in_np
    (h : P01ConstructionGap) :
    SATInNPGap circuitBitEncoding :=
  construction_closes_p01 h

def FinalExternalCertificate.toInternalClosure
    (E : FinalExternalCertificate) :
    SATInternalClosure :=
  {
    encoding := circuitBitEncoding
    sat_in_np := p01_to_sat_in_np E.p01
    fail_generator := E.fail
  }

theorem finalExternal_to_FINAL_ROOT
    (E : FinalExternalCertificate) :
    FINAL_ROOT :=
  sat_internal_closure_implies_p_ne_np E.toInternalClosure

/-- Exact external/official package.  The model-match theorem is kept explicit;
    it is not smuggled into the lower bound. -/
structure OfficialFinalExternalCertificate
    (officialP officialNP : BitLanguage → Prop)
    extends FinalExternalCertificate where
  model_match : ExternalModelMatch officialP officialNP

def OFFICIAL_FINAL_ROOT
    (officialP officialNP : BitLanguage → Prop) : Prop :=
  OfficialPneqNP officialP officialNP

theorem officialFinalExternal_to_root
    {officialP officialNP : BitLanguage → Prop}
    (E : OfficialFinalExternalCertificate officialP officialNP) :
    OFFICIAL_FINAL_ROOT officialP officialNP := by
  exact internal_separation_transfers E.model_match
    (finalExternal_to_FINAL_ROOT E.toFinalExternalCertificate)

/-- If the external predicates are the hardened model itself, no additional
    model-match assumption is needed. -/
def internalOfficialCertificate
    (E : FinalExternalCertificate) :
    OfficialFinalExternalCertificate InP InNP :=
  {
    toFinalExternalCertificate := E
    model_match := InternalModelMatch
  }

#print axioms MCore.Real.HardenedFinal.p01_to_sat_in_np
#print axioms MCore.Real.HardenedFinal.finalExternal_to_FINAL_ROOT
#print axioms MCore.Real.HardenedFinal.officialFinalExternal_to_root

end HardenedFinal
end MCore.Real
