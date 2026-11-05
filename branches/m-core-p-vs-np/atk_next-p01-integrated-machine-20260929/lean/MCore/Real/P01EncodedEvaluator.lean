import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalSATWitness
import MCore.Real.Semantics

namespace MCore
namespace Real
namespace P01EncodedEvaluator

open CanonicalFinalProof
open CanonicalCircuitBits
open CircuitK1

/-- Streaming evaluator over the canonical bit encoding.
It consumes exactly one encoded circuit prefix and returns its Boolean value
together with the unconsumed tail.  No Circuit value is stored in control. -/
def evalEncodedCore :
    Nat → Assignment → BitString → Option (Bool × BitString)
  | 0, _, _ => none
  | fuel + 1, sigma, bits =>
      match bits with
      | false :: false :: false :: rest =>
          match decodeNat rest with
          | some (i, tail) => some (sigma i, tail)
          | none => none
      | false :: false :: true :: rest =>
          some (false, rest)
      | false :: true :: false :: rest =>
          some (true, rest)
      | false :: true :: true :: rest =>
          match evalEncodedCore fuel sigma rest with
          | some (v, tail) => some (!v, tail)
          | none => none
      | true :: false :: false :: rest =>
          match evalEncodedCore fuel sigma rest with
          | some (l, rest') =>
              match evalEncodedCore fuel sigma rest' with
              | some (r, tail) => some (Bool.and l r, tail)
              | none => none
          | none => none
      | true :: false :: true :: rest =>
          match evalEncodedCore fuel sigma rest with
          | some (l, rest') =>
              match evalEncodedCore fuel sigma rest' with
              | some (r, tail) => some (Bool.or l r, tail)
              | none => none
          | none => none
      | _ => none

/-- On a canonical encoding, the streaming evaluator returns exactly the
semantic circuit value and preserves the external tail. -/
theorem evalEncodedCore_encode_append
    (sigma : Assignment)
    (c : Circuit)
    (tail : BitString)
    (fuel : Nat)
    (hFuel : CircuitK1.size c < fuel) :
    evalEncodedCore fuel sigma (encodeCircuit c ++ tail) =
      some (evalCircuit sigma c, tail) := by
  induction c generalizing fuel tail with
  | input i =>
      cases fuel with
      | zero => omega
      | succ f =>
          simp [evalEncodedCore, encodeCircuit, decodeNat_encodeNat_append,
            evalCircuit]
  | const b =>
      cases fuel with
      | zero => omega
      | succ f =>
          cases b <;> simp [evalEncodedCore, encodeCircuit, evalCircuit]
  | not c ih =>
      cases fuel with
      | zero => omega
      | succ f =>
          have hc : CircuitK1.size c < f := by
            simp [CircuitK1.size] at hFuel
            omega
          simp [evalEncodedCore, encodeCircuit, ih _ _ hc, evalCircuit]
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
          simp [evalEncodedCore, encodeCircuit, List.append_assoc,
            iha _ _ ha, ihb _ _ hb, evalCircuit]
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
          simp [evalEncodedCore, encodeCircuit, List.append_assoc,
            iha _ _ ha, ihb _ _ hb, evalCircuit]

/-- Fuel chosen only from the encoded input length is sufficient. -/
def evalEncoded
    (sigma : Assignment) (bits : BitString) : Option Bool :=
  match evalEncodedCore (bits.length + 1) sigma bits with
  | some (v, []) => some v
  | _ => none

theorem evalEncoded_encode
    (sigma : Assignment) (c : Circuit) :
    evalEncoded sigma (encodeCircuit c) =
      some (evalCircuit sigma c) := by
  have hFuel :
      CircuitK1.size c < (encodeCircuit c).length + 1 :=
    Nat.lt_succ_of_le (size_le_encodeCircuit_length c)
  have h :=
    evalEncodedCore_encode_append sigma c ([] : BitString)
      ((encodeCircuit c).length + 1) hFuel
  have h' :
      evalEncodedCore ((encodeCircuit c).length + 1) sigma (encodeCircuit c) =
        some (evalCircuit sigma c, []) := by
    simpa using h
  simp [evalEncoded, h']

/-- The streaming evaluator agrees with witness verification on the canonical
encoding.  This is the exact semantic specification the one-machine physical
verifier must refine. -/
theorem evalEncoded_witness
    (phi : Circuit)
    (w : CanonicalSATWitness.SATWitness phi) :
    evalEncoded (CanonicalSATWitness.assignmentOfWitness phi w)
        (encodeCircuit phi) =
      some (evalCircuit
        (CanonicalSATWitness.assignmentOfWitness phi w) phi) := by
  exact evalEncoded_encode
    (CanonicalSATWitness.assignmentOfWitness phi w) phi

#print axioms MCore.Real.P01EncodedEvaluator.evalEncodedCore_encode_append
#print axioms MCore.Real.P01EncodedEvaluator.evalEncoded_encode

end P01EncodedEvaluator
end Real
end MCore
