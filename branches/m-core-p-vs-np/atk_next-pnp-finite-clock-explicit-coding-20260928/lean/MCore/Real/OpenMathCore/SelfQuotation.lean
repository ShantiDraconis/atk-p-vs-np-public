import Mathlib
import MCore.Real.P02CandidateCodingFrontier
import MCore.Real.P02DiagonalFrontier
import MCore.Real.CanonicalCircuitBitsInverse

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalCircuitBitsInverse
open P02CandidateCodingFrontier
open P02DiagonalFrontier

structure SelfDescription where
  coding : CandidateCodingInterface
  quote : PolyDTMCandidate → CircuitK1.Circuit
  quotedBits : PolyDTMCandidate → BitString
  quotedBits_eq :
    ∀ M, quotedBits M = encodeCircuit (quote M)
  valid :
    ∀ M, CanonicalSATValid (quotedBits M)

theorem selfDescription_bits_canonical
    (S : SelfDescription) (M : PolyDTMCandidate) :
    ∃ c : CircuitK1.Circuit,
      S.quotedBits M = encodeCircuit c := by
  exact ⟨S.quote M, S.quotedBits_eq M⟩

end MCore.Real.OpenMathCore
