import Mathlib.Logic.Equiv.List
import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace P02BitStringNatCoding

open CanonicalFinalProof

/-- Canonical natural-number code for the repository bitstring type, using
Mathlib's constructive Encodable instance for List Bool. -/
def encodeBitsNat (x : BitString) : Nat :=
  Encodable.encode x

/-- Partial inverse of encodeBitsNat. -/
def decodeBitsNat (n : Nat) : Option BitString :=
  Encodable.decode (α := BitString) n

@[simp] theorem decodeBitsNat_encodeBitsNat
    (x : BitString) :
    decodeBitsNat (encodeBitsNat x) = some x := by
  exact Encodable.encodek x

theorem encodeBitsNat_injective :
    Function.Injective encodeBitsNat := by
  intro a b h
  exact Encodable.encode_injective h

/-- Totalized semantic projection used for program-output interpretation.
Divergence / non-code can be kept separate at the Partrec layer; whenever an
actual natural result exists, this map gives a deterministic bitstring. -/
def decodeBitsNatD (n : Nat) : BitString :=
  (decodeBitsNat n).getD []

@[simp] theorem decodeBitsNatD_encodeBitsNat
    (x : BitString) :
    decodeBitsNatD (encodeBitsNat x) = x := by
  simp [decodeBitsNatD, decodeBitsNat_encodeBitsNat]

#print axioms MCore.Real.P02BitStringNatCoding.decodeBitsNat_encodeBitsNat
#print axioms MCore.Real.P02BitStringNatCoding.encodeBitsNat_injective
#print axioms MCore.Real.P02BitStringNatCoding.decodeBitsNatD_encodeBitsNat

end P02BitStringNatCoding
end Real
end MCore
