import MCore.Real.P01FinalCertificate
import MCore.Real.FailProofAllGaps

namespace MCore.Real
namespace CanonicalFinalExternal

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open FailProofAllGaps
open P01FinalCertificate

/-- Hardened final external certificate on the canonical finite-control
    bitstring machine model. -/
structure FinalExternalCertificate : Type where
  satInNP :
    SATInNPGap circuitBitEncoding
  failGenerator :
    FailureGenerator (SATBits circuitBitEncoding)

/-- Internal canonical separation root. -/
def FINAL_ROOT : Prop :=
  PneqNP

/-- The final external certificate yields the hardened internal separation. -/
theorem finalExternal_to_FINAL_ROOT
    (E : FinalExternalCertificate) :
    FINAL_ROOT := by
  exact target_failure_implies_p_ne_np
    E.satInNP
    (failure_generator_implies_universal_failure E.failGenerator)

/-- The P01 construction supplies exactly the SAT-in-NP field of the
    hardened final external certificate. -/
theorem p01_supplies_satInNP
    (h : P01ConstructionGap) :
    SATInNPGap circuitBitEncoding :=
  construction_closes_p01 h

/-- Exact producer from the two remaining canonical ingredients:
    (1) a concrete P01 machine construction and
    (2) a universal deterministic failure generator for the same SATBits. -/
def finalExternal_of_p01_and_failure
    (hP01 : P01ConstructionGap)
    (G : FailureGenerator (SATBits circuitBitEncoding)) :
    FinalExternalCertificate :=
  {
    satInNP := p01_supplies_satInNP hP01
    failGenerator := G
  }

theorem FINAL_ROOT_of_p01_and_failure
    (hP01 : P01ConstructionGap)
    (G : FailureGenerator (SATBits circuitBitEncoding)) :
    FINAL_ROOT :=
  finalExternal_to_FINAL_ROOT
    (finalExternal_of_p01_and_failure hP01 G)

/-- External/official transfer remains a separate semantic obligation. -/
theorem official_root_of_p01_failure_and_model_match
    {officialP officialNP : BitLanguage → Prop}
    (hP01 : P01ConstructionGap)
    (G : FailureGenerator (SATBits circuitBitEncoding))
    (M : ExternalModelMatch officialP officialNP) :
    OfficialPneqNP officialP officialNP := by
  exact internal_separation_transfers M
    (FINAL_ROOT_of_p01_and_failure hP01 G)

#print axioms MCore.Real.CanonicalFinalExternal.p01_supplies_satInNP
#print axioms MCore.Real.CanonicalFinalExternal.finalExternal_of_p01_and_failure
#print axioms MCore.Real.CanonicalFinalExternal.FINAL_ROOT_of_p01_and_failure
#print axioms MCore.Real.CanonicalFinalExternal.official_root_of_p01_failure_and_model_match

end CanonicalFinalExternal
end MCore.Real
