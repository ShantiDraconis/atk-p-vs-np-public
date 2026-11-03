import MCore.Real.PNPDiscovery.FiniteCandidateDescription
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits

/-- Prefix-free unary serialization of a finite list of natural numbers.
The list length is written first, so arbitrary tails remain parseable. -/
def encodeNatList (xs : List Nat) : BitString :=
  encodeNat xs.length ++ xs.flatMap encodeNat

/-- Parse exactly k unary naturals, returning the unconsumed bit tail. -/
def decodeNats : Nat → BitString → Option (List Nat × BitString)
  | 0, bits => some ([], bits)
  | k + 1, bits => do
      let (n, rest) ← decodeNat bits
      let (ns, tail) ← decodeNats k rest
      some (n :: ns, tail)

/-- Parsing an encoded concrete list prefix recovers that list and the
unchanged external tail. -/
theorem decodeNats_encode_append
    (xs : List Nat)
    (tail : BitString) :
    decodeNats xs.length
        (xs.flatMap encodeNat ++ tail) =
      some (xs, tail) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [decodeNats, List.flatMap_cons,
        List.append_assoc,
        decodeNat_encodeNat_append, ih]

def decodeNatList
    (bits : BitString) :
    Option (List Nat × BitString) := do
  let (k, rest) ← decodeNat bits
  decodeNats k rest

theorem decodeNatList_encode_append
    (xs : List Nat)
    (tail : BitString) :
    decodeNatList (encodeNatList xs ++ tail) =
      some (xs, tail) := by
  unfold encodeNatList decodeNatList
  rw [List.append_assoc]
  rw [decodeNat_encodeNat_append]
  exact decodeNats_encode_append xs tail

theorem decodeNatList_encode
    (xs : List Nat) :
    decodeNatList (encodeNatList xs) =
      some (xs, []) := by
  simpa using decodeNatList_encode_append xs []

/-- Boolean table entries are encoded as the naturals 0/1. -/
def boolWord : Bool → Nat
  | false => 0
  | true => 1

def boolOfWord : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

@[simp] theorem boolOfWord_boolWord
    (b : Bool) :
    boolOfWord (boolWord b) = some b := by
  cases b <;> rfl

def encodeBoolList (xs : List Bool) : BitString :=
  encodeNatList (xs.map boolWord)

def decodeBoolWords : List Nat → Option (List Bool)
  | [] => some []
  | n :: ns => do
      let b ← boolOfWord n
      let bs ← decodeBoolWords ns
      some (b :: bs)

theorem decodeBoolWords_map_boolWord
    (xs : List Bool) :
    decodeBoolWords (xs.map boolWord) = some xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [decodeBoolWords, ih, boolWord, boolOfWord]

def decodeBoolList
    (bits : BitString) :
    Option (List Bool × BitString) := do
  let (words, tail) ← decodeNatList bits
  let bs ← decodeBoolWords words
  some (bs, tail)

theorem decodeBoolList_encode_append
    (xs : List Bool)
    (tail : BitString) :
    decodeBoolList (encodeBoolList xs ++ tail) =
      some (xs, tail) := by
  unfold encodeBoolList decodeBoolList
  rw [decodeNatList_encode_append]
  simp [decodeBoolWords_map_boolWord xs]

/-- Exact unary size of a natural-list encoding. -/
theorem encodeNatList_length
    (xs : List Nat) :
    (encodeNatList xs).length =
      xs.length + 1 +
        (xs.map (fun n => n + 1)).sum := by
  unfold encodeNatList
  rw [List.length_append]
  rw [encodeNat_length]
  simp
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih]
      omega

#print axioms MCore.Real.PNPDiscovery.decodeNats_encode_append
#print axioms MCore.Real.PNPDiscovery.decodeNatList_encode_append
#print axioms MCore.Real.PNPDiscovery.decodeBoolWords_map_boolWord
#print axioms MCore.Real.PNPDiscovery.decodeBoolList_encode_append
#print axioms MCore.Real.PNPDiscovery.encodeNatList_length

end PNPDiscovery
end Real
end MCore
