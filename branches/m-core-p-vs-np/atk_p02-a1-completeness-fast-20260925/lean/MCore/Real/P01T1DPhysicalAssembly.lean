import MCore.Real.P01FullVerifierPhysical
import MCore.Real.P01FullVerifierReverseDecoderGap
import MCore.Real.P01FullVerifierReadWitnessLocal
import MCore.Real.P01FullVerifierEvalLocal
import MCore.Real.P01FullVerifierShuttleReturn

namespace MCore
namespace Real
namespace P01T1DPhysicalAssembly

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01FullVerifierPhysical
open P01FullVerifierReverseDecoderGap

/-- Functional decoding is closed; the remaining object is a fixed finite-control
TM realizing the same verifier semantics on the physical verifier tape. -/
structure PhysicalAssemblyCertificate where
  realization : PhysicalVerifierRealization

def PhysicalAssemblyGap : Prop := Nonempty PhysicalAssemblyCertificate

theorem physicalAssembly_closes_verifier
    (h : PhysicalAssemblyGap) :
    P01FullVerifierMachine.FullVerifierGap := by
  rcases h with ⟨A⟩
  exact physical_realization_closes_full_verifier A.realization

/-- This theorem records that no separate functional decoder hypothesis remains. -/
theorem functional_decoder_available :
    ReverseDecoderGap :=
  reverse_decoder_gap_closed_functionally

#print axioms MCore.Real.P01T1DPhysicalAssembly.physicalAssembly_closes_verifier
#print axioms MCore.Real.P01T1DPhysicalAssembly.functional_decoder_available

end P01T1DPhysicalAssembly
end Real
end MCore
