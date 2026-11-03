import MCore.Real.P01FullVerifierStackSemantics
import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalCircuitBitsInverse

namespace MCore
namespace Real
namespace P01FullVerifierReverseDecoderGap

open CircuitK1
open CanonicalCircuitBits
open P01FullVerifierStackSemantics
open CanonicalCircuitBitsInverse

/-- Exact fail-closed boundary for the still-missing physical reverse decoder.
No inhabitant is asserted here. -/
structure ReverseDecoderCertificate where
  scanReverse : CanonicalFinalProof.BitString -> List EvalInstr
  correct :
    forall phi : Circuit,
      scanReverse (encodeCircuit phi) = evalProgram phi
  length_bound :
    forall phi : Circuit,
      (scanReverse (encodeCircuit phi)).length <= (encodeCircuit phi).length

def ReverseDecoderGap : Prop :=
  Nonempty ReverseDecoderCertificate

theorem reverse_decoder_length_from_correct
    (R : ReverseDecoderCertificate) (phi : Circuit) :
    (R.scanReverse (encodeCircuit phi)).length <=
      (encodeCircuit phi).length := by
  exact R.length_bound phi


/-- Functional decoder obtained from the already-proved exact canonical inverse.
This closes the present ReverseDecoderCertificate shape. It is deliberately
not claimed to be a physical finite-control TM implementation. -/
def functionalScanReverse (bits : CanonicalFinalProof.BitString) : List EvalInstr :=
  match decodeCircuit bits with
  | some phi => evalProgram phi
  | none => []

theorem functionalScanReverse_correct (phi : Circuit) :
    functionalScanReverse (encodeCircuit phi) = evalProgram phi := by
  simp [functionalScanReverse, decodeCircuit_encode]

theorem functionalScanReverse_length_bound (phi : Circuit) :
    (functionalScanReverse (encodeCircuit phi)).length ≤
      (encodeCircuit phi).length := by
  rw [functionalScanReverse_correct]
  exact evalProgram_length_le_encoding phi

def functionalReverseDecoderCertificate : ReverseDecoderCertificate :=
  { scanReverse := functionalScanReverse
    correct := functionalScanReverse_correct
    length_bound := functionalScanReverse_length_bound }

theorem reverse_decoder_gap_closed_functionally :
    ReverseDecoderGap :=
  ⟨functionalReverseDecoderCertificate⟩

#print axioms MCore.Real.P01FullVerifierReverseDecoderGap.reverse_decoder_length_from_correct
#print axioms MCore.Real.P01FullVerifierReverseDecoderGap.reverse_decoder_gap_closed_functionally

end P01FullVerifierReverseDecoderGap
end Real
end MCore
