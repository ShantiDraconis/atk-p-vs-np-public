import Mathlib
import MCore.Real.CanonicalCircuitBitsInverse
import MCore.Real.P02CandidateCodingFrontier

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalCircuitBitsInverse
open P02CandidateCodingFrontier

structure InferenceSystem (α : Type) where
  derives : List α → α → Prop
  weakening : ∀ {Γ Δ a}, derives Γ a → Γ ⊆ Δ → derives Δ a
  cut : ∀ {Γ a b}, derives Γ a → derives (a :: Γ) b → derives Γ b

structure EncodingFoundation where
  circuitEncode : CircuitK1.Circuit → BitString
  circuitDecode : BitString → Option CircuitK1.Circuit
  decode_encode : ∀ c, circuitDecode (circuitEncode c) = some c
  encode_decode : ∀ {x c}, circuitDecode x = some c → x = circuitEncode c

def canonicalEncodingFoundation : EncodingFoundation where
  circuitEncode := encodeCircuit
  circuitDecode := decodeCircuit
  decode_encode := decodeCircuit_encode
  encode_decode := by
    intro x c h
    exact decodeCircuit_inverse x c h

theorem canonical_encode_injective :
    Function.Injective canonicalEncodingFoundation.circuitEncode := by
  intro a b h
  exact encodeCircuit_injective h

structure ExplicitAxiomPolicy where
  propositionExtensionalityAllowed : Bool
  classicalChoiceAllowed : Bool
  quotientSoundAllowed : Bool
  hiddenAxiomNames : List String
  noHiddenAxioms : hiddenAxiomNames = []

def defaultAxiomPolicy : ExplicitAxiomPolicy where
  propositionExtensionalityAllowed := true
  classicalChoiceAllowed := true
  quotientSoundAllowed := true
  hiddenAxiomNames := []
  noHiddenAxioms := rfl

end MCore.Real.OpenMathCore
