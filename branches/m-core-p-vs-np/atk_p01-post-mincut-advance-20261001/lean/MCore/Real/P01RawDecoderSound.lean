import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P01RawDecoderSound

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits

/-- Successful unary decoding reconstructs exactly the consumed unary prefix. -/
theorem decodeNat_success_sound :
    ∀ (bits : BitString) (n : Nat) (tail : BitString),
      decodeNat bits = some (n, tail) →
        bits = encodeNat n ++ tail := by
  intro bits
  induction bits with
  | nil =>
      intro n tail h
      simp [decodeNat] at h
  | cons b rest ih =>
      intro n tail h
      cases b with
      | false =>
          simp [decodeNat] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | true =>
          cases hd : decodeNat rest with
          | none =>
              simp [decodeNat, hd] at h
          | some p =>
              rcases p with ⟨k, rem⟩
              simp [decodeNat, hd] at h
              rcases h with ⟨rfl, rfl⟩
              have hs := ih k rem hd
              simp [encodeNat, hs, List.append_assoc]

/-- Successful recursive circuit decoding reconstructs exactly the encoded
circuit prefix and the returned residual tail.

This is the missing converse needed to connect a semantic decoder result to
the physical residual-source rejection theorem. -/
theorem decodeCircuitCore_success_sound :
    ∀ (fuel : Nat) (bits : BitString)
      (phi : Circuit) (tail : BitString),
      decodeCircuitCore fuel bits = some (phi, tail) →
        bits = encodeCircuit phi ++ tail := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits phi tail h
      simp [decodeCircuitCore] at h
  | succ fuel ih =>
      intro bits phi tail h
      cases bits with
      | nil =>
          simp [decodeCircuitCore] at h
      | cons b0 r0 =>
          cases r0 with
          | nil =>
              simp [decodeCircuitCore] at h
          | cons b1 r1 =>
              cases r1 with
              | nil =>
                  simp [decodeCircuitCore] at h
              | cons b2 rest =>
                  cases b0 <;> cases b1 <;> cases b2
                  · -- 000 input
                    cases hn : decodeNat rest with
                    | none =>
                        simp [decodeCircuitCore, hn] at h
                    | some p =>
                        rcases p with ⟨i, rem⟩
                        simp [decodeCircuitCore, hn] at h
                        rcases h with ⟨rfl, rfl⟩
                        have hs := decodeNat_success_sound rest i rem hn
                        simp [encodeCircuit, hs, List.append_assoc]
                  · -- 001 const false
                    simp [decodeCircuitCore] at h
                    rcases h with ⟨rfl, rfl⟩
                    rfl
                  · -- 010 const true
                    simp [decodeCircuitCore] at h
                    rcases h with ⟨rfl, rfl⟩
                    rfl
                  · -- 011 not
                    cases hc : decodeCircuitCore fuel rest with
                    | none =>
                        simp [decodeCircuitCore, hc] at h
                    | some p =>
                        rcases p with ⟨c, rem⟩
                        simp [decodeCircuitCore, hc] at h
                        rcases h with ⟨rfl, rfl⟩
                        have hs := ih rest c rem hc
                        simp [encodeCircuit, hs, List.append_assoc]
                  · -- 100 and
                    cases ha : decodeCircuitCore fuel rest with
                    | none =>
                        simp [decodeCircuitCore, ha] at h
                    | some p =>
                        rcases p with ⟨a, rest'⟩
                        cases hb : decodeCircuitCore fuel rest' with
                        | none =>
                            simp [decodeCircuitCore, ha, hb] at h
                        | some q =>
                            rcases q with ⟨b, rem⟩
                            simp [decodeCircuitCore, ha, hb] at h
                            rcases h with ⟨rfl, rfl⟩
                            have hsa := ih rest a rest' ha
                            have hsb := ih rest' b rem hb
                            simp [encodeCircuit, hsa, hsb, List.append_assoc]
                  · -- 101 or
                    cases ha : decodeCircuitCore fuel rest with
                    | none =>
                        simp [decodeCircuitCore, ha] at h
                    | some p =>
                        rcases p with ⟨a, rest'⟩
                        cases hb : decodeCircuitCore fuel rest' with
                        | none =>
                            simp [decodeCircuitCore, ha, hb] at h
                        | some q =>
                            rcases q with ⟨b, rem⟩
                            simp [decodeCircuitCore, ha, hb] at h
                            rcases h with ⟨rfl, rfl⟩
                            have hsa := ih rest a rest' ha
                            have hsb := ih rest' b rem hb
                            simp [encodeCircuit, hsa, hsb, List.append_assoc]
                  · -- 110 invalid
                    simp [decodeCircuitCore] at h
                  · -- 111 invalid
                    simp [decodeCircuitCore] at h

/-- A whole-decoder residual case is literally a canonical encoded prefix
followed by a nonempty tail. -/
theorem residual_is_canonical_prefix
    (bits : BitString)
    (phi : Circuit) (b : Bool) (tail : BitString)
    (h :
      decodeCircuitCore (bits.length + 1) bits =
        some (phi, b :: tail)) :
    bits = encodeCircuit phi ++ (b :: tail) :=
  decodeCircuitCore_success_sound
    (bits.length + 1) bits phi (b :: tail) h

#print axioms MCore.Real.P01RawDecoderSound.decodeNat_success_sound
#print axioms MCore.Real.P01RawDecoderSound.decodeCircuitCore_success_sound
#print axioms MCore.Real.P01RawDecoderSound.residual_is_canonical_prefix

end P01RawDecoderSound
end Real
end MCore
