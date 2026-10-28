import MCore.Real.P02UniversalFailureAlgebra

namespace MCore
namespace Real
namespace P02CandidateCodingFrontier

open CanonicalFinalProof

/-- Effective coding interface still absent from PolyDTMCandidate itself.
An inhabitant must provide an actual finite bitstring code, a partial decoder,
round-trip correctness, and a size measure. No existence is assumed here. -/
structure CandidateCodingInterface where
  encode : PolyDTMCandidate → BitString
  decode : BitString → Option PolyDTMCandidate
  decode_encode : ∀ M : PolyDTMCandidate, decode (encode M) = some M
  codeSize : PolyDTMCandidate → Nat
  codeSize_eq : ∀ M : PolyDTMCandidate, codeSize M = (encode M).length

def CandidateCodingGap : Prop := Nonempty CandidateCodingInterface

/-- Any coding interface gives injectivity of encode. -/
theorem encode_injective
    (C : CandidateCodingInterface) :
    ∀ ⦃M N : PolyDTMCandidate⦄, C.encode M = C.encode N → M = N := by
  intro M N h
  have hM := C.decode_encode M
  have hN := C.decode_encode N
  rw [h, hN] at hM
  exact Option.some.inj hM.symm

#print axioms MCore.Real.P02CandidateCodingFrontier.encode_injective

end P02CandidateCodingFrontier
end Real
end MCore
