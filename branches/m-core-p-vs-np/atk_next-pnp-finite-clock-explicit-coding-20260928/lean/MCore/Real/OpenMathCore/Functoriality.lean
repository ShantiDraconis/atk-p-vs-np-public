import Mathlib
import MCore.Real.P02CandidateCodingFrontier
import MCore.Real.CanonicalCircuitBitsInverse

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open P02CandidateCodingFrontier
open CanonicalCircuitBits
open CanonicalCircuitBitsInverse

structure PartialCodec (α : Type) where
  encode : α → BitString
  decode : BitString → Option α
  roundtrip : ∀ a, decode (encode a) = some a

def candidatePartialCodec (C : CandidateCodingInterface) :
    PartialCodec PolyDTMCandidate where
  encode := C.encode
  decode := C.decode
  roundtrip := C.decode_encode

def circuitPartialCodec : PartialCodec CircuitK1.Circuit where
  encode := encodeCircuit
  decode := decodeCircuit
  roundtrip := decodeCircuit_encode

theorem codec_encode_injective
    {α : Type} (C : PartialCodec α) :
    Function.Injective C.encode := by
  intro a b h
  have ha := C.roundtrip a
  have hb := C.roundtrip b
  rw [h, hb] at ha
  exact Option.some.inj ha.symm

structure CodecMorphism (α β : Type) (A : PartialCodec α) (B : PartialCodec β) where
  map : α → β
  mapBits : BitString → BitString
  encode_natural : ∀ a, mapBits (A.encode a) = B.encode (map a)

end MCore.Real.OpenMathCore
