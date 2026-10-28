import MCore.Real.P01FinalCertificate
import MCore.Real.CanonicalSATBoundary

namespace MCore.Real
namespace P01BitFinal

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P01FinalCertificate

/-- Final external object in the exact bitstring model actually inhabited by P01. -/
structure FinalExternalCertificate : Prop where
  satInNP :
    CanonicalFinalProof.InNP
      (SATBits circuitBitEncoding)
  failProof :
    CanonicalFinalProof.UniversalFailure
      (SATBits circuitBitEncoding)

/-- Exact separation root in the same machine/input model. -/
def FINAL_ROOT : Prop :=
  CanonicalFinalProof.PneqNP

theorem finalExternal_to_FINAL_ROOT
    (E : FinalExternalCertificate) :
    FINAL_ROOT :=
  CanonicalFinalProof.target_failure_implies_p_ne_np
    E.satInNP E.failProof

/-- P01 machine construction discharges the NP half of the exact bit-model root. -/
theorem p01Construction_to_satInNP
    (C : P01MachineConstruction) :
    CanonicalFinalProof.InNP (SATBits circuitBitEncoding) :=
  ⟨C.toRealization⟩

/-- Therefore only the universal deterministic fail proof remains after P01. -/
def finalExternal_of_p01_and_fail
    (C : P01MachineConstruction)
    (hFail :
      CanonicalFinalProof.UniversalFailure
        (SATBits circuitBitEncoding)) :
    FinalExternalCertificate :=
  {
    satInNP := p01Construction_to_satInNP C
    failProof := hFail
  }

theorem FINAL_ROOT_of_p01_and_fail
    (C : P01MachineConstruction)
    (hFail :
      CanonicalFinalProof.UniversalFailure
        (SATBits circuitBitEncoding)) :
    FINAL_ROOT :=
  finalExternal_to_FINAL_ROOT
    (finalExternal_of_p01_and_fail C hFail)

#print axioms MCore.Real.P01BitFinal.p01Construction_to_satInNP
#print axioms MCore.Real.P01BitFinal.FINAL_ROOT_of_p01_and_fail

end P01BitFinal
end MCore.Real
