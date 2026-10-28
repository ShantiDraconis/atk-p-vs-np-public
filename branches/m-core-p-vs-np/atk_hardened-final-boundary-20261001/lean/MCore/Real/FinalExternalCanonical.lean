import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits
import MCore.Real.P01FinalCertificate

namespace MCore
namespace Real
namespace FinalExternalCanonical

open CanonicalFinalProof
open FailProofAllGaps
open CanonicalSATBoundary
open CanonicalCircuitBits
open P01FinalCertificate
open CanonicalSATNTMAttack

/-- Final external payload for the hardened bit-language model.
No candidate-controlled encoder occurs here:
* P01 supplies the fixed canonical SAT-in-NP realization;
* FailureGenerator supplies the genuine deterministic lower bound;
* ExternalModelMatch transports the internal separation to the official model.
-/
structure FinalExternal
    (officialP officialNP : BitLanguage → Prop) where
  p01 : P01ConstructionGap
  fail_generator : FailureGenerator (SATBits circuitBitEncoding)
  model_match : ExternalModelMatch officialP officialNP

def FinalExternal.toSATExternalClosure
    {officialP officialNP : BitLanguage → Prop}
    (E : FinalExternal officialP officialNP) :
    SATExternalClosure officialP officialNP := by
  have hNP : SATInNPGap circuitBitEncoding :=
    construction_closes_p01 E.p01
  exact {
    encoding := circuitBitEncoding
    sat_in_np := hNP
    fail_generator := E.fail_generator
    model_match := E.model_match
  }

def FINAL_EXTERNAL
    (officialP officialNP : BitLanguage → Prop) : Type :=
  FinalExternal officialP officialNP

theorem FINAL_ROOT
    {officialP officialNP : BitLanguage → Prop}
    (E : FINAL_EXTERNAL officialP officialNP) :
    OfficialPneqNP officialP officialNP :=
  sat_external_closure_implies_official_separation
    E.toSATExternalClosure

#print axioms MCore.Real.FinalExternalCanonical.FINAL_ROOT

end FinalExternalCanonical
end Real
end MCore
