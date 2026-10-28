import MCore.Real.CanonicalSATBoundary

namespace MCore
namespace Real
namespace CanonicalCircuitBits

open CircuitK1
open CanonicalFinalProof
open CanonicalSATBoundary

def encodeNat : Nat → BitString
  | 0 => [false]
  | n + 1 => true :: encodeNat n

def decodeNat : BitString → Option (Nat × BitString)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← decodeNat rest
      some (n + 1, tail)

theorem decodeNat_encodeNat_append
    (n : Nat) (tail : BitString) :
    decodeNat (encodeNat n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [encodeNat, decodeNat, ih]

/-- Fixed three-bit tags followed by recursively encoded payloads. -/
def encodeCircuit : Circuit → BitString
  | .input i => [false, false, false] ++ encodeNat i
  | .const false => [false, false, true]
  | .const true => [false, true, false]
  | .not c => [false, true, true] ++ encodeCircuit c
  | .and a b =>
      [true, false, false] ++ encodeCircuit a ++ encodeCircuit b
  | .or a b =>
      [true, false, true] ++ encodeCircuit a ++ encodeCircuit b

def decodeCircuitCore :
    Nat → BitString → Option (Circuit × BitString)
  | 0, _ => none
  | fuel + 1, bits =>
      match bits with
      | false :: false :: false :: rest =>
          match decodeNat rest with
          | some (i, tail) => some (.input i, tail)
          | none => none
      | false :: false :: true :: rest =>
          some (.const false, rest)
      | false :: true :: false :: rest =>
          some (.const true, rest)
      | false :: true :: true :: rest =>
          match decodeCircuitCore fuel rest with
          | some (c, tail) => some (.not c, tail)
          | none => none
      | true :: false :: false :: rest =>
          match decodeCircuitCore fuel rest with
          | some (a, rest') =>
              match decodeCircuitCore fuel rest' with
              | some (b, tail) => some (.and a b, tail)
              | none => none
          | none => none
      | true :: false :: true :: rest =>
          match decodeCircuitCore fuel rest with
          | some (a, rest') =>
              match decodeCircuitCore fuel rest' with
              | some (b, tail) => some (.or a b, tail)
              | none => none
          | none => none
      | _ => none

theorem size_le_encodeCircuit_length
    (c : Circuit) :
    CircuitK1.size c ≤ (encodeCircuit c).length := by
  induction c with
  | input i =>
      simp [CircuitK1.size, encodeCircuit, encodeNat]
  | const b =>
      cases b <;> simp [CircuitK1.size, encodeCircuit]
  | not c ih =>
      simp [CircuitK1.size, encodeCircuit]
      omega
  | and a b iha ihb =>
      simp [CircuitK1.size, encodeCircuit]
      omega
  | or a b iha ihb =>
      simp [CircuitK1.size, encodeCircuit]
      omega

theorem decodeCircuitCore_encode_append
    (c : Circuit)
    (tail : BitString)
    (fuel : Nat)
    (hFuel : CircuitK1.size c < fuel) :
    decodeCircuitCore fuel (encodeCircuit c ++ tail) =
      some (c, tail) := by
  induction c generalizing fuel tail with
  | input i =>
      cases fuel with
      | zero => omega
      | succ f =>
          simp [encodeCircuit, decodeCircuitCore,
            decodeNat_encodeNat_append]
  | const b =>
      cases fuel with
      | zero => omega
      | succ f =>
          cases b <;> simp [encodeCircuit, decodeCircuitCore]
  | not c ih =>
      cases fuel with
      | zero => omega
      | succ f =>
          have hc : CircuitK1.size c < f := by
            simp [CircuitK1.size] at hFuel
            omega
          simp [encodeCircuit, decodeCircuitCore, ih _ _ hc]
  | and a b iha ihb =>
      cases fuel with
      | zero => omega
      | succ f =>
          have ha : CircuitK1.size a < f := by
            simp [CircuitK1.size] at hFuel
            omega
          have hb : CircuitK1.size b < f := by
            simp [CircuitK1.size] at hFuel
            omega
          simp [encodeCircuit, decodeCircuitCore, List.append_assoc,
            iha _ _ ha, ihb _ _ hb]
  | or a b iha ihb =>
      cases fuel with
      | zero => omega
      | succ f =>
          have ha : CircuitK1.size a < f := by
            simp [CircuitK1.size] at hFuel
            omega
          have hb : CircuitK1.size b < f := by
            simp [CircuitK1.size] at hFuel
            omega
          simp [encodeCircuit, decodeCircuitCore, List.append_assoc,
            iha _ _ ha, ihb _ _ hb]

def decodeCircuit (bits : BitString) : Option Circuit :=
  match decodeCircuitCore (bits.length + 1) bits with
  | some (c, []) => some c
  | _ => none

theorem decodeCircuit_encode
    (c : Circuit) :
    decodeCircuit (encodeCircuit c) = some c := by
  have hFuel :
      CircuitK1.size c < (encodeCircuit c).length + 1 :=
    Nat.lt_succ_of_le (size_le_encodeCircuit_length c)
  have hCore :=
    decodeCircuitCore_encode_append
      c ([] : BitString) ((encodeCircuit c).length + 1) hFuel
  have hCore' :
      decodeCircuitCore ((encodeCircuit c).length + 1) (encodeCircuit c) =
        some (c, []) := by
    simpa using hCore
  simp [decodeCircuit, hCore']

def circuitBitEncoding : CircuitBitEncoding :=
  { encode := encodeCircuit
    decode := decodeCircuit
    decode_encode := decodeCircuit_encode }

theorem canonical_sat_encoding_closed :
    SATEncodingGap := by
  exact ⟨circuitBitEncoding⟩

theorem encoded_sat_equivalence
    (φ : Circuit) :
    SATBits circuitBitEncoding (encodeCircuit φ) ↔ SATLanguage φ :=
  encoded_sat_iff circuitBitEncoding φ

#print axioms MCore.Real.CanonicalCircuitBits.decodeNat_encodeNat_append
#print axioms MCore.Real.CanonicalCircuitBits.size_le_encodeCircuit_length
#print axioms MCore.Real.CanonicalCircuitBits.decodeCircuitCore_encode_append
#print axioms MCore.Real.CanonicalCircuitBits.decodeCircuit_encode
#print axioms MCore.Real.CanonicalCircuitBits.canonical_sat_encoding_closed
#print axioms MCore.Real.CanonicalCircuitBits.encoded_sat_equivalence

end CanonicalCircuitBits
end Real
end MCore
